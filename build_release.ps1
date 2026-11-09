[CmdletBinding()]
param(
    [switch]$InstallAfterBuild,
    [switch]$SkipDependencyInstall,
    [switch]$SkipOptionalPyAudio,
    [switch]$CleanNuitkaWorkspace,
    [ValidateSet('FULL','FAST')][string]$BuildMode = 'FULL',
    # Keep MSVC as the default (GitHub Actions). Local builds can explicitly select Zig.
    [ValidateSet('MSVC','ZIG')][string]$Compiler = 'MSVC',
    # Optional full path to zig.exe; if omitted, PATH and common install paths are searched.
    [string]$ZigPath = '',
    # Limit the number of parallel native C compiler jobs. The GitHub workflow
    # explicitly passes 2 so the normal hosted build remains a two-job build.
    # Locally, 0 (default) selects the detected physical core count.
    [int]$NuitkaJobs = 0,
    # Emergency fallback only: Nuitka --low-memory forces one compiler job.
    # Keep this OFF for normal GitHub builds to preserve the requested 2-job build.
    [switch]$LowMemory,
    # Nuitka's --show-progress/--show-memory/--show-modules print a line of
    # output for every module Nuitka analyzes. That console/log I/O adds
    # measurable overhead during the slow Python-analysis phase (the phase
    # that --jobs does not speed up). They default OFF now for normal builds;
    # pass -Diagnostics to turn them back on when you specifically need that
    # visibility, e.g. while investigating a new slow-module regression.
    [switch]$Diagnostics
)

$ErrorActionPreference = 'Stop'
$ProjectRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $ProjectRoot

$script:BuildStartTime = Get-Date
$script:BuildTimer = [System.Diagnostics.Stopwatch]::StartNew()
$script:BuildExitCode = 0
$script:BuildSucceeded = $false
$script:CancelRequested = $false
$script:CancelHandler = $null
$script:CompilerFatalErrorDetected = $false
$LogDir = Join-Path $ProjectRoot 'build_logs'
New-Item -ItemType Directory -Force -Path $LogDir | Out-Null
# One unique run ID ties the stage log and full session log together.
$Stamp = $script:BuildStartTime.ToString('yyyyMMdd_HHmmss_fff')
$RunId = [guid]::NewGuid().ToString('N').Substring(0,8)
$LogName = 'Engo_Build_{0}_{1}_{2}.log' -f $Stamp, $PID, $RunId
$SessionLogName = 'Engo_BuildSession_{0}_{1}_{2}.log' -f $Stamp, $PID, $RunId
$LogPath = Join-Path $LogDir $LogName
$SessionLogPath = Join-Path $LogDir $SessionLogName
$script:LogWriter = $null
$script:SessionLogWriter = $null

# Keep normal native compilation parallel. GitHub Actions passes
# -NuitkaJobs 2 explicitly; the developer machine defaults to physical cores.
# The optional -LowMemory switch is a manual fallback for C1002 and forces one
# compiler job, so it must never be enabled in the normal 2-job workflow.
$script:LogicalProcessorCount = [Math]::Max(1, [int][Environment]::ProcessorCount)
$script:PhysicalCoreCount = $script:LogicalProcessorCount
try {
    $CimProcessor = Get-CimInstance -ClassName Win32_Processor -ErrorAction Stop | Select-Object -First 1
    if ($CimProcessor -and [int]$CimProcessor.NumberOfCores -gt 0) {
        $script:PhysicalCoreCount = [int]$CimProcessor.NumberOfCores
    }
} catch {
    $script:PhysicalCoreCount = [Math]::Max(1, [Math]::Floor($script:LogicalProcessorCount / 2))
}
if ($LowMemory) {
    $script:BuildNuitkaJobs = 1
} elseif ($NuitkaJobs -gt 0) {
    $script:BuildNuitkaJobs = [Math]::Min($script:LogicalProcessorCount, $NuitkaJobs)
} else {
    $script:BuildNuitkaJobs = [Math]::Max(1, $script:PhysicalCoreCount)
}

$LogStream = [System.IO.File]::Open(
    $LogPath,
    [System.IO.FileMode]::CreateNew,
    [System.IO.FileAccess]::Write,
    [System.IO.FileShare]::ReadWrite
)
$script:LogWriter = [System.IO.StreamWriter]::new($LogStream, [System.Text.UTF8Encoding]::new($true))
$script:LogWriter.AutoFlush = $true
$SessionLogStream = [System.IO.File]::Open(
    $SessionLogPath,
    [System.IO.FileMode]::CreateNew,
    [System.IO.FileAccess]::Write,
    [System.IO.FileShare]::ReadWrite
)
$script:SessionLogWriter = [System.IO.StreamWriter]::new($SessionLogStream, [System.Text.UTF8Encoding]::new($true))
$script:SessionLogWriter.AutoFlush = $true

# Intercept Ctrl+C locally. GitHub Actions owns cancellation of hosted jobs;
# registering a PowerShell scriptblock as a .NET console signal callback there
# can be invoked without a PowerShell runspace during runner timeout/cancel.
if ($env:GITHUB_ACTIONS -eq 'true') {
    Write-Host 'GitHub Actions cancellation is managed by the runner; custom ConsoleCancelKeyPress callback is disabled.'
} else {
    $script:CancelHandler = [System.ConsoleCancelEventHandler]{
        param($Sender, $EventArgs)
        $EventArgs.Cancel = $true
        $script:CancelRequested = $true
    }
    try {
        [Console]::add_CancelKeyPress($script:CancelHandler)
        Write-Host 'Build cancellation handler armed: Ctrl+C will stop the complete active build process tree.'
    } catch {
        Write-Host ("WARNING: Could not register Ctrl+C handler: {0}" -f $_.Exception.Message) -ForegroundColor Yellow
    }
}

function Write-LogLine([string]$Message) {
    # Keep the console readable while writing timestamped, flushed copies to both logs.
    Write-Host $Message
    $RecordedLine = '[{0}] {1}' -f (Get-Date -Format 'yyyy-MM-dd HH:mm:ss.fff'), $Message
    try {
        if ($null -ne $script:LogWriter) { $script:LogWriter.WriteLine($RecordedLine) }
    } catch {
        Write-Host "WARNING: Could not write to stage log: $($_.Exception.Message)" -ForegroundColor Yellow
        try { $script:LogWriter.Dispose() } catch { }
        $script:LogWriter = $null
    }
    try {
        if ($null -ne $script:SessionLogWriter) { $script:SessionLogWriter.WriteLine($RecordedLine) }
    } catch {
        Write-Host "WARNING: Could not write to session log: $($_.Exception.Message)" -ForegroundColor Yellow
        try { $script:SessionLogWriter.Dispose() } catch { }
        $script:SessionLogWriter = $null
    }
}

function Invoke-PendingBuildPowerRestore {
    # Legacy cleanup only: restore the user's original plan if an older
    # thermal-limited build left its recovery command behind. This version
    # does not create or activate any temporary power plan.
    $PendingRestoreFiles = @(Get-ChildItem -LiteralPath $LogDir -Filter 'Engo_BuildPowerRestore_*.cmd' -File -ErrorAction SilentlyContinue)
    foreach ($RestoreFile in $PendingRestoreFiles) {
        Write-LogLine ("[LEGACY POWER RECOVERY] Found pending power-plan restore file: {0}" -f $RestoreFile.FullName)
        try {
            & $env:ComSpec /d /c ('"{0}"' -f $RestoreFile.FullName)
            $RestoreCode = [int]$LASTEXITCODE
            if ($RestoreCode -eq 0) {
                Write-LogLine '[LEGACY POWER RECOVERY] Previous Windows power plan restored; no new temporary plan will be created by this builder.'
            } else {
                Write-LogLine ("[LEGACY POWER RECOVERY WARNING] Automatic power-plan recovery returned exit code {0}; restore file was retained." -f $RestoreCode)
            }
        } catch {
            Write-LogLine ("[LEGACY POWER RECOVERY WARNING] Could not run pending power-plan recovery: {0}" -f $_.Exception.Message)
        }
    }
}

function ConvertTo-WindowsArgument([AllowNull()][string]$Value) {
    # Quote one argument using the Windows CommandLineToArgvW escaping rules.
    if ($null -eq $Value) { return '""' }
    if ($Value.Length -gt 0 -and $Value -notmatch '[\s"]') { return $Value }
    $Builder = New-Object System.Text.StringBuilder
    [void]$Builder.Append('"')
    $Backslashes = 0
    foreach ($Character in $Value.ToCharArray()) {
        if ($Character -eq [char]92) {
            $Backslashes++
            continue
        }
        if ($Character -eq [char]34) {
            if ($Backslashes -gt 0) { [void]$Builder.Append(('\' * (2 * $Backslashes))) }
            [void]$Builder.Append('\"')
            $Backslashes = 0
            continue
        }
        if ($Backslashes -gt 0) {
            [void]$Builder.Append(('\' * $Backslashes))
            $Backslashes = 0
        }
        [void]$Builder.Append($Character)
    }
    # Backslashes immediately before the closing quote must be doubled.
    if ($Backslashes -gt 0) { [void]$Builder.Append(('\' * (2 * $Backslashes))) }
    [void]$Builder.Append('"')
    return $Builder.ToString()
}

function Write-NativeOutputLine {
    param(
        [Parameter(Mandatory=$true)][string]$StreamName,
        [AllowEmptyString()][string]$Line,
        [bool]$NuitkaCompile = $false,
        [hashtable]$ProgressState = $null
    )

    $LogLine = if ($StreamName -eq 'STDERR') { '[STDERR] ' + $Line } else { '[STDOUT] ' + $Line }
    Write-LogLine $LogLine

    # MSVC C1002 and SCons fatal messages are terminal build failures. Detect
    # them while streaming output so orphaned Nuitka/compiler workers do not
    # keep the runner alive until its global job timeout.
    if ($NuitkaCompile -and $Line -match '(?i)(fatal error C1002:|fatal error C1001:|scons:\s+\*\*\*.*\bError\s+\d+|FATAL:\s+Failed unexpectedly in Scons C backend compilation)') {
        $script:CompilerFatalErrorDetected = $true
    }

    if ($NuitkaCompile -and $null -ne $ProgressState) {
        if ($Line -match 'Starting Python compilation') {
            $ProgressState.Stage = 'Python module analysis/compilation (Nuitka emits sparse progress here)'
            $ProgressState.Percent = [Math]::Max($ProgressState.Percent, 10)
        } elseif ($Line -match 'Completed Python level compilation') {
            $ProgressState.Stage = 'Python analysis complete; preparing native source'
            $ProgressState.Percent = [Math]::Max($ProgressState.Percent, 25)
        } elseif ($Line -match 'Generating source code for C backend') {
            $ProgressState.Stage = 'Generating C source files'
            $ProgressState.Percent = [Math]::Max($ProgressState.Percent, 32)
        } elseif ($Line -match '(?i)(Nuitka-Scons|scons:|C compiler|compiling C|cl\.exe|clang-cl)') {
            $ProgressState.Stage = 'Compiling native C/C++ modules (this can take a while)'
            $ProgressState.Percent = [Math]::Max($ProgressState.Percent, 42)
        } elseif ($Line -match '(?i)(linking|link\.exe|lld-link)') {
            $ProgressState.Stage = 'Linking native modules'
            $ProgressState.Percent = [Math]::Max($ProgressState.Percent, 76)
        } elseif ($Line -match '(?i)(post-compilation|copying.*(dll|file)|deploying|standalone distribution)') {
            $ProgressState.Stage = 'Assembling standalone application files'
            $ProgressState.Percent = [Math]::Max($ProgressState.Percent, 88)
        } elseif ($Line -match '(?i)successfully created') {
            $ProgressState.Stage = 'Nuitka standalone output created'
            $ProgressState.Percent = [Math]::Max($ProgressState.Percent, 97)
        }
        Write-Progress -Activity 'Engo Windows build (Nuitka)' -Status ("{0}% - {1} (estimated phase)" -f $ProgressState.Percent, $ProgressState.Stage) -PercentComplete $ProgressState.Percent
    }
}

function Drain-NativeOutput {
    param(
        [Parameter(Mandatory=$true)][System.IO.StreamReader]$Reader,
        [Parameter(Mandatory=$true)][string]$StreamName,
        [bool]$NuitkaCompile = $false,
        [hashtable]$ProgressState = $null
    )

    while ($true) {
        $Line = $Reader.ReadLine()
        if ($null -eq $Line) { break }
        Write-NativeOutputLine -StreamName $StreamName -Line ([string]$Line) -NuitkaCompile $NuitkaCompile -ProgressState $ProgressState
    }
}

function Invoke-Native {
    param(
        [Parameter(Mandatory=$true)][string]$Executable,
        [Parameter(Mandatory=$true)][string[]]$Arguments,
        [Parameter(Mandatory=$true)][string]$Label,
        [switch]$AllowFailure
    )

    if ($script:CancelRequested) {
        throw [System.OperationCanceledException]::new('Build cancelled by user with Ctrl+C.')
    }
    Write-LogLine "`n=== $Label ==="
    $DisplayArguments = @($Arguments | ForEach-Object { ConvertTo-WindowsArgument ([string]$_) })
    $ArgumentLine = $DisplayArguments -join ' '
    Write-LogLine ('> ' + $Executable + ' ' + $ArgumentLine)

    # Use file-backed stdout/stderr capture instead of .NET asynchronous event
    # callbacks. This avoids callback/runspace instability in Windows PowerShell
    # 5.1 and still lets the builder stream output into both logs while running.
    $CaptureId = [guid]::NewGuid().ToString('N')
    $StdoutPath = Join-Path $LogDir ("native_{0}.stdout.txt" -f $CaptureId)
    $StderrPath = Join-Path $LogDir ("native_{0}.stderr.txt" -f $CaptureId)
    $Process = $null
    $StdoutStream = $null
    $StderrStream = $null
    $StdoutReader = $null
    $StderrReader = $null
    $Stopwatch = [System.Diagnostics.Stopwatch]::StartNew()
    $ExitSeenAt = $null
    $NextHeartbeat = 20
    $NuitkaCompile = ($Label -like '*Compile Engo with Nuitka*')
    $ProgressState = @{ Percent = 3; Stage = 'Starting Nuitka compiler' }
    $CaptureCompleted = $false
    # Track the complete descendant tree. Nuitka may re-exec its interpreter
    # several times, so the Start-Process PID can be nearly idle while a deeper
    # Python worker performs the real analysis/compilation.
    $TrackedProcessIds = @{}
    $NextProcessTreeScan = 0

    try {
        if ($NuitkaCompile) {
            Write-Progress -Activity 'Engo Windows build (Nuitka)' -Status '3% - Starting Nuitka compiler (estimated phase)' -PercentComplete 3
            Write-LogLine 'LIVE OUTPUT: Nuitka stdout/stderr are captured to temporary files and streamed into the logs.'
        }

        # Python's output is unbuffered so progress is visible as it happens.
        $OldPythonUnbuffered = $env:PYTHONUNBUFFERED
        $OldPythonEncoding = $env:PYTHONIOENCODING
        $env:PYTHONUNBUFFERED = '1'
        $env:PYTHONIOENCODING = 'utf-8'
        try {
            $Process = Start-Process -FilePath $Executable `
                -ArgumentList $ArgumentLine `
                -WorkingDirectory $ProjectRoot `
                -RedirectStandardOutput $StdoutPath `
                -RedirectStandardError $StderrPath `
                -WindowStyle Hidden `
                -PassThru `
                -ErrorAction Stop
        } finally {
            if ($null -eq $OldPythonUnbuffered) { Remove-Item Env:PYTHONUNBUFFERED -ErrorAction SilentlyContinue }
            else { $env:PYTHONUNBUFFERED = $OldPythonUnbuffered }
            if ($null -eq $OldPythonEncoding) { Remove-Item Env:PYTHONIOENCODING -ErrorAction SilentlyContinue }
            else { $env:PYTHONIOENCODING = $OldPythonEncoding }
        }

        Write-LogLine ("PROCESS STARTED: PID {0} | executable: {1} | working directory: {2}" -f $Process.Id, $Executable, $ProjectRoot)
        Write-LogLine ("RAW CAPTURE FILES: stdout={0}; stderr={1}" -f $StdoutPath, $StderrPath)

        # Start-Process creates both redirection files before returning. Open
        # them with shared read access so the build can tail them safely.
        $FileReadyClock = [System.Diagnostics.Stopwatch]::StartNew()
        while ((-not (Test-Path -LiteralPath $StdoutPath)) -or (-not (Test-Path -LiteralPath $StderrPath))) {
            if ($FileReadyClock.Elapsed.TotalSeconds -gt 5) {
                throw 'The redirected stdout/stderr capture files were not created by Start-Process.'
            }
            Start-Sleep -Milliseconds 50
        }
        $FileReadyClock.Stop()

        $StdoutStream = [System.IO.File]::Open($StdoutPath, [System.IO.FileMode]::Open, [System.IO.FileAccess]::Read, [System.IO.FileShare]::ReadWrite)
        $StderrStream = [System.IO.File]::Open($StderrPath, [System.IO.FileMode]::Open, [System.IO.FileAccess]::Read, [System.IO.FileShare]::ReadWrite)
        $StdoutReader = [System.IO.StreamReader]::new($StdoutStream, [System.Text.Encoding]::UTF8, $true)
        $StderrReader = [System.IO.StreamReader]::new($StderrStream, [System.Text.Encoding]::UTF8, $true)

        $TrackedProcessIds[[string]$Process.Id] = $true
        Write-LogLine ("PROCESS MONITOR: root PID {0}; heartbeat interval={1}s; stdout/stderr file-tail mode" -f $Process.Id, $NextHeartbeat)
        if ($NuitkaCompile) {
            Write-LogLine '[PROCESS TREE] Tracking all descendant processes because Nuitka can re-exec Python and move the real workload into a child worker.'
        }
        while ($true) {
            if ($script:CancelRequested) {
                Write-LogLine '[CANCEL] Ctrl+C received. Stopping Nuitka/NSIS and all tracked descendants...'
                throw [System.OperationCanceledException]::new('Build cancelled by user with Ctrl+C.')
            }

            Drain-NativeOutput -Reader $StdoutReader -StreamName 'STDOUT' -NuitkaCompile $NuitkaCompile -ProgressState $ProgressState
            Drain-NativeOutput -Reader $StderrReader -StreamName 'STDERR' -NuitkaCompile $NuitkaCompile -ProgressState $ProgressState

            if ($NuitkaCompile -and $script:CompilerFatalErrorDetected) {
                throw [System.InvalidOperationException]::new("Nuitka reported a fatal native compiler/SCons compilation error. Remaining build processes will be stopped. Full stdout/stderr is recorded in $LogPath")
            }

            # Refresh the known process tree every 3 seconds. Keep previously
            # discovered PIDs even if an intermediate parent exits, otherwise
            # grandchildren could become detached from the live WMI snapshot.
            if ($NuitkaCompile -and $Stopwatch.Elapsed.TotalSeconds -ge $NextProcessTreeScan) {
                try {
                    $ProcessSnapshot = @(Get-CimInstance -ClassName Win32_Process -ErrorAction Stop | Select-Object ProcessId, ParentProcessId, Name)
                    $AddedProcess = $true
                    while ($AddedProcess) {
                        $AddedProcess = $false
                        foreach ($Candidate in $ProcessSnapshot) {
                            $CandidatePid = [string]([int]$Candidate.ProcessId)
                            $ParentPid = [string]([int]$Candidate.ParentProcessId)
                            if ($TrackedProcessIds.ContainsKey($ParentPid) -and -not $TrackedProcessIds.ContainsKey($CandidatePid)) {
                                $TrackedProcessIds[$CandidatePid] = $true
                                $AddedProcess = $true
                            }
                        }
                    }
                } catch {
                    Write-LogLine ("[PROCESS TREE WARNING] Could not refresh descendant list: {0}" -f $_.Exception.Message)
                }
                $NextProcessTreeScan = $Stopwatch.Elapsed.TotalSeconds + 3
            }

            $Process.Refresh()
            if ($Process.HasExited) {
                # Do not stop monitoring just because the launcher exits while
                # a known Nuitka child is still compiling or writing to capture files.
                $TrackedIdsForExit = @($TrackedProcessIds.Keys | ForEach-Object { [int]$_ })
                $RemainingTreeProcesses = @(Get-Process -Id $TrackedIdsForExit -ErrorAction SilentlyContinue)
                if ($RemainingTreeProcesses.Count -eq 0) { break }
                # Helper daemons (mspdbsrv, vctip, compiler-cache server) are meant to stay
                # alive after Nuitka exits and would make this loop wait forever.
                # Give real children 120s to finish, then stop waiting.
                if ($null -eq $ExitSeenAt) { $ExitSeenAt = $Stopwatch.Elapsed.TotalSeconds }
                if (($Stopwatch.Elapsed.TotalSeconds - $ExitSeenAt) -ge 120) {
                    Write-LogLine '[BUILD STATUS] Launcher exited; leftover helper processes ignored after 120s grace.'
                    break
                }
            }

            if ($Stopwatch.Elapsed.TotalSeconds -ge $NextHeartbeat) {
                try {
                    if ($NuitkaCompile) {
                        $TrackedIds = @($TrackedProcessIds.Keys | ForEach-Object { [int]$_ })
                        $TreeProcesses = @(Get-Process -Id $TrackedIds -ErrorAction SilentlyContinue)
                        $CpuTotalSeconds = 0.0
                        $RamTotalBytes = [int64]0
                        foreach ($TreeProcess in $TreeProcesses) {
                            try { $CpuTotalSeconds += $TreeProcess.TotalProcessorTime.TotalSeconds } catch { }
                            try { $RamTotalBytes += [int64]$TreeProcess.WorkingSet64 } catch { }
                        }
                        $CpuSeconds = [Math]::Round($CpuTotalSeconds, 1)
                        $RamGB = [Math]::Round($RamTotalBytes / 1GB, 2)
                        $ActiveProcessCount = $TreeProcesses.Count
                        $ActivePidList = (@($TreeProcesses | ForEach-Object { [string]$_.Id }) -join ',')
                        $Heartbeat = "[BUILD STATUS] Still running: $Label | elapsed $([int]$Stopwatch.Elapsed.TotalMinutes)m $($Stopwatch.Elapsed.Seconds)s | TREE CPU ${CpuSeconds}s | TREE RAM ${RamGB} GB | active processes: $ActiveProcessCount | PIDs: $ActivePidList"
                    } else {
                        $CpuSeconds = [Math]::Round($Process.TotalProcessorTime.TotalSeconds, 1)
                        $RamGB = [Math]::Round($Process.WorkingSet64 / 1GB, 2)
                        $Heartbeat = "[BUILD STATUS] Still running: $Label | elapsed $([int]$Stopwatch.Elapsed.TotalMinutes)m $($Stopwatch.Elapsed.Seconds)s | CPU ${CpuSeconds}s | RAM ${RamGB} GB"
                    }
                } catch {
                    $Heartbeat = "[BUILD STATUS] Still running: $Label | elapsed $([int]$Stopwatch.Elapsed.TotalMinutes)m $($Stopwatch.Elapsed.Seconds)s | process-tree metrics unavailable: $($_.Exception.Message)"
                }
                if ($NuitkaCompile) { $Heartbeat += " | stage: $($ProgressState.Stage)" }
                Write-LogLine $Heartbeat
                if ($NuitkaCompile) {
                    Write-Progress -Activity 'Engo Windows build (Nuitka)' -Status ("{0}% - {1} | elapsed {2}m {3}s (estimated phase)" -f $ProgressState.Percent, $ProgressState.Stage, [int]$Stopwatch.Elapsed.TotalMinutes, $Stopwatch.Elapsed.Seconds) -PercentComplete $ProgressState.Percent
                }
                $NextHeartbeat += 20
            }
            Start-Sleep -Milliseconds 150
        }

        # Wait and drain one final time after process exit to capture every byte
        # written immediately before termination.
        $Process.WaitForExit()
        Drain-NativeOutput -Reader $StdoutReader -StreamName 'STDOUT' -NuitkaCompile $NuitkaCompile -ProgressState $ProgressState
        Drain-NativeOutput -Reader $StderrReader -StreamName 'STDERR' -NuitkaCompile $NuitkaCompile -ProgressState $ProgressState
        $Stopwatch.Stop()
        $Code = [int]$Process.ExitCode
        Write-LogLine ("Exit code: {0}; elapsed: {1:N1} seconds" -f $Code, $Stopwatch.Elapsed.TotalSeconds)
        if ($NuitkaCompile) { Write-Progress -Activity 'Engo Windows build (Nuitka)' -Completed }
        $CaptureCompleted = $true

        if ($Code -ne 0 -and -not $AllowFailure) {
            throw "$Label failed with exit code $Code. Full stdout/stderr is recorded in $LogPath"
        }
        return $Code
    }
    catch {
        if ($NuitkaCompile) { Write-Progress -Activity 'Engo Windows build (Nuitka)' -Completed }
        if ($_.Exception.Message -notlike '*Full stdout/stderr is recorded*') {
            Write-LogLine ("PROCESS LAUNCH/CAPTURE ERROR: " + $_.Exception.ToString())
        }
        if ($null -ne $Process) {
            try {
                Write-LogLine '[PROCESS CLEANUP] Terminating the complete child process tree after cancellation or monitor failure.'
                Stop-BuildProcessTree -RootProcess $Process -KnownProcessIds $TrackedProcessIds
            } catch {
                Write-LogLine ("[PROCESS CLEANUP WARNING] " + $_.Exception.Message)
            }
        }
        throw
    }
    finally {
        $Stopwatch.Stop()
        try { if ($null -ne $StdoutReader) { $StdoutReader.Dispose() } elseif ($null -ne $StdoutStream) { $StdoutStream.Dispose() } } catch { }
        try { if ($null -ne $StderrReader) { $StderrReader.Dispose() } elseif ($null -ne $StderrStream) { $StderrStream.Dispose() } } catch { }
        try { if ($null -ne $Process) { $Process.Dispose() } } catch { }
        if ($CaptureCompleted) {
            Remove-Item -LiteralPath $StdoutPath, $StderrPath -Force -ErrorAction SilentlyContinue
        } else {
            Write-LogLine ("[WARNING] Raw process capture files retained for diagnosis: {0} | {1}" -f $StdoutPath, $StderrPath)
        }
    }
}

function Stop-BuildProcessTree {
    param(
        [System.Diagnostics.Process]$RootProcess,
        [hashtable]$KnownProcessIds
    )

    $RootId = 0
    if ($null -ne $RootProcess) {
        try { $RootId = [int]$RootProcess.Id } catch { }
    }

    # taskkill /T handles the currently attached descendants in one operation.
    if ($RootId -gt 0) {
        try {
            $Taskkill = Join-Path $env:SystemRoot 'System32\taskkill.exe'
            if (Test-Path -LiteralPath $Taskkill) {
                Write-LogLine ("[CANCEL] Terminating process tree rooted at PID {0} with taskkill /T /F." -f $RootId)
                & $Taskkill /PID $RootId /T /F 2>&1 | ForEach-Object {
                    Write-LogLine ("[CANCEL TASKKILL] " + [string]$_)
                }
            }
        } catch {
            Write-LogLine ("[CANCEL WARNING] taskkill tree termination failed: {0}" -f $_.Exception.Message)
        }
    }

    # Also terminate every PID discovered by the monitor. This catches
    # grandchildren that became detached after an intermediate process exited.
    $Ids = @()
    if ($null -ne $KnownProcessIds) {
        $Ids = @($KnownProcessIds.Keys | ForEach-Object { [int]$_ } | Sort-Object -Descending -Unique)
    }
    if ($RootId -gt 0 -and $Ids -notcontains $RootId) { $Ids += $RootId }

    for ($Pass = 1; $Pass -le 3; $Pass++) {
        foreach ($ProcessId in $Ids) {
            try {
                $StillRunning = Get-Process -Id $ProcessId -ErrorAction SilentlyContinue
                if ($StillRunning) {
                    Stop-Process -Id $ProcessId -Force -ErrorAction SilentlyContinue
                }
            } catch { }
        }
        Start-Sleep -Milliseconds 250
    }

    $Remaining = @()
    foreach ($ProcessId in $Ids) {
        if (Get-Process -Id $ProcessId -ErrorAction SilentlyContinue) { $Remaining += $ProcessId }
    }
    if ($Remaining.Count -gt 0) {
        Write-LogLine ("[CANCEL WARNING] Some tracked process IDs still appear active: {0}" -f ($Remaining -join ', '))
    } else {
        Write-LogLine '[CANCEL] All tracked build processes have exited.'
    }
}

function Test-PythonRuntime {
    param(
        [Parameter(Mandatory=$true)][string]$Executable,
        [string[]]$PrefixArguments = @(),
        [Parameter(Mandatory=$true)][string]$Label
    )

    $ProbeScript = Join-Path $ProjectRoot 'build_support\python_runtime_probe.py'
    if (-not (Test-Path -LiteralPath $ProbeScript)) {
        Write-LogLine "Python probe script is missing: $ProbeScript"
        return 127
    }

    # Run the tiny probe in isolated mode. -I -S skips user-site packages and
    # .pth startup hooks, which can otherwise stall interpreter discovery.
    # Use file redirection here instead of the general async event-capture path:
    # it is more reliable for this very short process and always leaves a result.
    $Arguments = @($PrefixArguments) + @('-I', '-S', $ProbeScript)
    $DisplayArguments = @($Arguments | ForEach-Object { ConvertTo-WindowsArgument ([string]$_) })
    Write-LogLine "`n=== $Label [Probe] ==="
    Write-LogLine ('> ' + $Executable + ' ' + ($DisplayArguments -join ' '))

    $ProbeId = [guid]::NewGuid().ToString('N')
    $StdoutPath = Join-Path $LogDir ("python_probe_{0}.stdout.txt" -f $ProbeId)
    $StderrPath = Join-Path $LogDir ("python_probe_{0}.stderr.txt" -f $ProbeId)
    $ArgumentLine = ($Arguments | ForEach-Object { ConvertTo-WindowsArgument ([string]$_) }) -join ' '
    $Clock = [System.Diagnostics.Stopwatch]::StartNew()
    $ProbeProcess = $null
    $ProbeCode = 126

    try {
        $ProbeProcess = Start-Process -FilePath $Executable `
            -ArgumentList $ArgumentLine `
            -WorkingDirectory $ProjectRoot `
            -RedirectStandardOutput $StdoutPath `
            -RedirectStandardError $StderrPath `
            -WindowStyle Hidden `
            -PassThru
        Write-LogLine ("PYTHON PROBE STARTED: PID {0} | executable: {1}" -f $ProbeProcess.Id, $Executable)

        if (-not $ProbeProcess.WaitForExit(15000)) {
            Write-LogLine '[WARNING] Python runtime probe exceeded 15 seconds. Terminating it and trying the next interpreter source.'
            try { Stop-Process -Id $ProbeProcess.Id -Force -ErrorAction SilentlyContinue } catch { }
            try { $ProbeProcess.WaitForExit() } catch { }
            $ProbeCode = 124
        } else {
            $ProbeCode = [int]$ProbeProcess.ExitCode
        }

        foreach ($StreamInfo in @(
            @{ Path = $StdoutPath; Prefix = '[STDOUT] ' },
            @{ Path = $StderrPath; Prefix = '[STDERR] ' }
        )) {
            if (Test-Path -LiteralPath $StreamInfo.Path) {
                foreach ($Line in @(Get-Content -LiteralPath $StreamInfo.Path -ErrorAction SilentlyContinue)) {
                    Write-LogLine ($StreamInfo.Prefix + [string]$Line)
                }
            }
        }

        Write-LogLine ("Exit code: {0}; elapsed: {1:N1} seconds" -f $ProbeCode, $Clock.Elapsed.TotalSeconds)
        return [int]$ProbeCode
    }
    catch {
        Write-LogLine ("PYTHON PROBE LAUNCH/CAPTURE ERROR: " + $_.Exception.ToString())
        Write-LogLine ("Probe target: {0}" -f $Executable)
        return 126
    }
    finally {
        $Clock.Stop()
        if ($null -ne $ProbeProcess) { try { $ProbeProcess.Dispose() } catch { } }
        Remove-Item -LiteralPath $StdoutPath, $StderrPath -Force -ErrorAction SilentlyContinue
    }
}

function Find-NsisCompiler {
    $Candidates = @(
        (Join-Path $env:ProgramFiles 'NSIS\makensis.exe'),
        (Join-Path ${env:ProgramFiles(x86)} 'NSIS\makensis.exe'),
        (Join-Path $env:LOCALAPPDATA 'Programs\NSIS\makensis.exe'),
        (Join-Path $env:ProgramFiles 'NSIS\Bin\makensis.exe'),
        (Join-Path ${env:ProgramFiles(x86)} 'NSIS\Bin\makensis.exe')
    ) | Where-Object { $_ -and (Test-Path -LiteralPath $_) }
    if ($Candidates.Count -gt 0) { return $Candidates[0] }
    $Command = Get-Command 'makensis.exe' -ErrorAction SilentlyContinue
    if ($Command) { return $Command.Source }
    return $null
}

try {
    if ($script:CancelRequested) {
        throw [System.OperationCanceledException]::new('Build cancelled by user with Ctrl+C.')
    }
    Write-LogLine '============================================================'
    Write-LogLine 'ENGO BUILD SESSION START'
    Write-LogLine '============================================================'
    Write-LogLine 'Engo Windows release builder'
    Write-LogLine 'BUILDER_FIX_MARKER: MAX_PERFORMANCE_PROCESS_TREE_MATHTEXT_20261105'
    Invoke-PendingBuildPowerRestore
    Write-LogLine "Build mode: $BuildMode"
    if ($LowMemory) {
        Write-LogLine ("[MEMORY] Emergency Nuitka --low-memory mode is enabled (one compiler job). Detected physical cores: {0}; logical processors: {1}." -f $script:PhysicalCoreCount, $script:LogicalProcessorCount)
    } else {
        Write-LogLine ("[PARALLEL] Nuitka native compilation will use --jobs={0}. Detected physical cores: {1}; logical processors: {2}." -f $script:BuildNuitkaJobs, $script:PhysicalCoreCount, $script:LogicalProcessorCount)
    }
    Write-LogLine '[PERFORMANCE] The currently active Windows power plan will not be changed by this build.'
    Write-LogLine "Project: $ProjectRoot"
    Write-LogLine "Started: $($script:BuildStartTime.ToString('yyyy-MM-dd HH:mm:ss.fff'))"
    Write-LogLine "PowerShell PID: $PID"
    Write-LogLine "PowerShell executable: $([string](Get-Process -Id $PID -ErrorAction SilentlyContinue).Path)"
    Write-LogLine "PowerShell version: $($PSVersionTable.PSVersion)"
    Write-LogLine "PowerShell edition: $($PSVersionTable.PSEdition)"
    Write-LogLine "PowerShell build: $($PSVersionTable.BuildVersion)"
    Write-LogLine "CLR version: $([Environment]::Version)"
    Write-LogLine "Host: $((Get-Host).Name) $((Get-Host).Version)"
    Write-LogLine "Process architecture: $([IntPtr]::Size * 8)-bit"
    Write-LogLine "OS is 64-bit: $([Environment]::Is64BitOperatingSystem)"
    Write-LogLine "PROCESSOR_ARCHITECTURE: $env:PROCESSOR_ARCHITECTURE"
    Write-LogLine "PROCESSOR_ARCHITEW6432: $env:PROCESSOR_ARCHITEW6432"
    Write-LogLine "PROCESSOR_IDENTIFIER: $env:PROCESSOR_IDENTIFIER"
    Write-LogLine "Logical processors available: $([Environment]::ProcessorCount)"
    Write-LogLine "COMPUTERNAME: $env:COMPUTERNAME"
    Write-LogLine "OS environment: $env:OS"
    Write-LogLine "TEMP: $env:TEMP"
    Write-LogLine "Working directory: $((Get-Location).Path)"
    Write-LogLine "Command line: $([Environment]::CommandLine)"
    try {
        $WindowsInfo = Get-ItemProperty -LiteralPath 'HKLM:\SOFTWARE\Microsoft\Windows NT\CurrentVersion' -ErrorAction Stop
        Write-LogLine "Windows product: $($WindowsInfo.ProductName)"
        Write-LogLine "Windows display version: $($WindowsInfo.DisplayVersion)"
        Write-LogLine "Windows build: $($WindowsInfo.CurrentBuild).$($WindowsInfo.UBR)"
    } catch {
        Write-LogLine "Windows registry version lookup unavailable: $($_.Exception.Message)"
        Write-LogLine "Windows version fallback: $([Environment]::OSVersion.VersionString)"
    }
    Write-LogLine "Build flags: InstallAfterBuild=$InstallAfterBuild; SkipDependencyInstall=$SkipDependencyInstall; SkipOptionalPyAudio=$SkipOptionalPyAudio; CleanNuitkaWorkspace=$CleanNuitkaWorkspace; Compiler=$Compiler"
    Write-LogLine "Stage log: $LogPath"
    Write-LogLine "Session log: $SessionLogPath"

    $MainPath = Join-Path $ProjectRoot 'main.py'
    if ($Compiler -eq 'ZIG') {
        $RequirementsPath = Join-Path $ProjectRoot 'requirements-build-zig.txt'
    } else {
        $RequirementsPath = Join-Path $ProjectRoot 'requirements-build.txt'
    }
    $IconPath = Join-Path $ProjectRoot 'engopdfviewer.ico'
    $CheckboxPath = Join-Path $ProjectRoot 'checkbox_checked.png'
    $ChevronPath = Join-Path $ProjectRoot 'combo_chevron_light.png'
    $ChevronUpLightPath = Join-Path $ProjectRoot 'combo_chevron_up_light.png'
    $ChevronUpDarkPath = Join-Path $ProjectRoot 'combo_chevron_up_dark.png'
    $GuidePath = Join-Path $ProjectRoot 'ENGO_PROGRAM_GUIDE.md'
    $NsisScript = Join-Path $ProjectRoot 'installer\EngoInstaller.nsi'
    Write-LogLine '[STAGE START] Validate required source files and installer script'
    foreach ($Required in @($MainPath, $RequirementsPath, $IconPath, $CheckboxPath, $ChevronPath, $ChevronUpLightPath, $ChevronUpDarkPath, $GuidePath, $NsisScript)) {
        if (-not (Test-Path -LiteralPath $Required)) { throw "Required project file is missing: $Required" }
        Write-LogLine "[FILE OK] $Required"
    }
    Write-LogLine '[STAGE END] Validate required source files and installer script'

    Write-LogLine '[STAGE START] Locate NSIS compiler'
    $Makensis = Find-NsisCompiler
    if (-not $Makensis) {
        throw 'NSIS compiler (makensis.exe) was not found. Install NSIS 3.13 from https://nsis.sourceforge.io/Download, then run BUILD_SETUP.bat again.'
    }
    Write-LogLine "NSIS compiler: $Makensis"
    Write-LogLine '[STAGE END] Locate NSIS compiler'

    Write-LogLine '[STAGE START] Read application version and prepare output paths'
    Write-LogLine "[POWERSHELL] Get-Content -LiteralPath `"$MainPath`" -Raw -Encoding UTF8"
    $MainText = Get-Content -LiteralPath $MainPath -Raw -Encoding UTF8
    $VersionMatch = [regex]::Match($MainText, '(?m)^APP_VERSION\s*=\s*["''](?<version>\d+\.\d+\.\d+)["'']')
    if (-not $VersionMatch.Success) { throw 'Could not read APP_VERSION = "x.y.z" from main.py. Update that constant before building.' }
    $Version = $VersionMatch.Groups['version'].Value
    $AppName = 'Engo PDF Viewer & AI Study Agent'
    $ExeName = "$AppName.exe"
    Write-LogLine "Detected source version: $Version"
    Write-LogLine '[STAGE END] Read application version and prepare output paths'

    $DistDir = Join-Path $ProjectRoot 'dist'
    $AppDistDir = Join-Path $DistDir $AppName
    $CompilerWorkspaceName = if ($Compiler -eq 'ZIG') { 'nuitka_zig' } else { 'nuitka' }
    if ([string]::IsNullOrWhiteSpace($env:ENGO_BUILD_TEMP_DIR)) {
        $NuitkaWorkDir = Join-Path $ProjectRoot ("build\$CompilerWorkspaceName")
    } else {
        $ExternalBuildTemp = [Environment]::ExpandEnvironmentVariables($env:ENGO_BUILD_TEMP_DIR.Trim())
        $NuitkaWorkDir = Join-Path $ExternalBuildTemp ("Engo_Nuitka_$Compiler")
        Write-LogLine "Using external build directory for $Compiler from ENGO_BUILD_TEMP_DIR: $NuitkaWorkDir"
    }
    # Keep Nuitka's intermediate build folder between runs. This is required
    # for useful incremental rebuilds and compiler-cache reuse. Only remove it
    # when the user explicitly requests a clean rebuild.
    if ($CleanNuitkaWorkspace -and (Test-Path -LiteralPath $NuitkaWorkDir)) {
        Write-LogLine "[CACHE] Explicit clean requested; removing Nuitka workspace: $NuitkaWorkDir"
        Remove-Item -LiteralPath $NuitkaWorkDir -Recurse -Force
    } elseif (Test-Path -LiteralPath $NuitkaWorkDir) {
        $ExistingNuitkaBuild = Join-Path $NuitkaWorkDir 'main.build'
        if (Test-Path -LiteralPath $ExistingNuitkaBuild) {
            $CachedFileCount = @(Get-ChildItem -LiteralPath $ExistingNuitkaBuild -File -Recurse -ErrorAction SilentlyContinue).Count
            Write-LogLine ("[CACHE] Reusing existing Nuitka workspace: {0} | main.build files: {1}" -f $NuitkaWorkDir, $CachedFileCount)
        } else {
            Write-LogLine ("[CACHE] Nuitka workspace exists; no prior main.build cache found: {0}" -f $NuitkaWorkDir)
        }
    } else {
        Write-LogLine ("[CACHE] First build: a new Nuitka workspace will be created at {0}" -f $NuitkaWorkDir)
    }

    # Prefer a project-local environment so the global Python installation remains untouched.
    Write-LogLine '[STAGE START] Discover and validate Python 3.13 x64 build runtime'
    $VenvDir = Join-Path $ProjectRoot '.build_venv'
    $Python = Join-Path $VenvDir 'Scripts\python.exe'
    $NeedNewVenv = -not (Test-Path -LiteralPath $Python)
    if (-not $NeedNewVenv) {
        $NeedNewVenv = ((Test-PythonRuntime -Executable $Python -Label 'Check existing build environment') -ne 0)
    }
    if ($NeedNewVenv) {
        if (Test-Path -LiteralPath $VenvDir) {
            Write-LogLine "[POWERSHELL] Remove-Item -LiteralPath `"$VenvDir`" -Recurse -Force"
            Remove-Item -LiteralPath $VenvDir -Recurse -Force
        }
        $BasePython = $null
        $BasePythonArgs = @()

        # Prefer a real python.exe installation before invoking Windows py.exe.
        # WindowsApps aliases can hang while resolving Store-managed runtimes.
        $DirectPythonCandidates = @(
            (Join-Path $env:LOCALAPPDATA 'Python\pythoncore-3.13-64\python.exe'),
            (Join-Path $env:LOCALAPPDATA 'Programs\Python\Python313\python.exe'),
            (Join-Path $env:ProgramFiles 'Python313\python.exe'),
            (Join-Path ${env:ProgramFiles(x86)} 'Python313-32\python.exe')
        ) | Where-Object { $_ -and (Test-Path -LiteralPath $_) }
        foreach ($Candidate in $DirectPythonCandidates) {
            $ProbeCode = Test-PythonRuntime -Executable $Candidate -Label "Probe direct Python: $Candidate"
            if ($ProbeCode -eq 0) { $BasePython = $Candidate; break }
        }

        # Fall back to the Python Launcher only when no direct interpreter was found.
        if (-not $BasePython) {
            $PyLauncher = Get-Command 'py.exe' -ErrorAction SilentlyContinue
            if ($PyLauncher) {
                $ProbeCode = Test-PythonRuntime -Executable $PyLauncher.Source -PrefixArguments @('-3.13') -Label 'Probe Python Launcher for Python 3.13 x64'
                if ($ProbeCode -eq 0) { $BasePython = $PyLauncher.Source; $BasePythonArgs = @('-3.13') }
            }
        }
        if (-not $BasePython) {
            $PyManager = Get-Command 'pymanager' -ErrorAction SilentlyContinue
            if ($PyManager) {
                $ProbeCode = Test-PythonRuntime -Executable $PyManager.Source -PrefixArguments @('exec','3.13') -Label 'Probe Python Install Manager for Python 3.13 x64'
                if ($ProbeCode -eq 0) { $BasePython = $PyManager.Source; $BasePythonArgs = @('exec','3.13') }
            }
        }
        if (-not $BasePython) {
            $PythonCommand = Get-Command 'python.exe' -ErrorAction SilentlyContinue
            if ($PythonCommand -and $PythonCommand.Source -notlike '*\WindowsApps\*') {
                $ProbeCode = Test-PythonRuntime -Executable $PythonCommand.Source -Label 'Probe PATH Python for Python 3.13 x64'
                if ($ProbeCode -eq 0) { $BasePython = $PythonCommand.Source }
            }
        }
        if (-not $BasePython) {
            throw 'Python 3.13 x64 was not found. Install Python 3.13 x64, then run BUILD_SETUP.bat again.'
        }
        Invoke-Native $BasePython ($BasePythonArgs + @('-m','venv',$VenvDir)) 'Create isolated Python 3.13 build environment'
    }
    if (-not (Test-Path -LiteralPath $Python)) { throw "Could not create the build environment: $Python" }
    if ((Test-PythonRuntime -Executable $Python -Label 'Validate Python version and architecture') -ne 0) { throw 'The isolated build environment is not Python 3.13 x64.' }
    Write-LogLine '[STAGE END] Discover and validate Python 3.13 x64 build runtime'

    Write-LogLine "Python selected: $Python"
    Write-LogLine "Python runtime was newly created: $NeedNewVenv"

    $ResolvedZigExe = $null
    if ($Compiler -eq 'ZIG') {
        Write-LogLine '[STAGE START] Locate and validate Zig compiler'
        $ZigCandidates = @()
        if (-not [string]::IsNullOrWhiteSpace($ZigPath)) { $ZigCandidates += $ZigPath.Trim('"') }
        if (-not [string]::IsNullOrWhiteSpace($env:ZIG_EXE)) { $ZigCandidates += $env:ZIG_EXE.Trim('"') }
        $ZigCommand = Get-Command 'zig.exe' -ErrorAction SilentlyContinue
        if ($ZigCommand -and $ZigCommand.Source) { $ZigCandidates += $ZigCommand.Source }
        $ZigCandidates += @('C:\Tools\zig\zig.exe', (Join-Path $ProjectRoot 'tools\zig\zig.exe'))
        if (-not [string]::IsNullOrWhiteSpace($env:LOCALAPPDATA)) {
            $ZigCandidates += (Join-Path $env:LOCALAPPDATA 'Programs\zig\zig.exe')
        }
        foreach ($ZigCandidate in $ZigCandidates) {
            if ([string]::IsNullOrWhiteSpace([string]$ZigCandidate)) { continue }
            $CandidatePath = [Environment]::ExpandEnvironmentVariables([string]$ZigCandidate)
            if (Test-Path -LiteralPath $CandidatePath -PathType Container) {
                $CandidatePath = Join-Path $CandidatePath 'zig.exe'
            }
            if (Test-Path -LiteralPath $CandidatePath -PathType Leaf) {
                $ResolvedZigExe = (Resolve-Path -LiteralPath $CandidatePath).Path
                break
            }
        }
        if (-not $ResolvedZigExe) {
            throw 'Zig was selected but zig.exe was not found. Extract the official Windows x86_64 ZIP to C:\Tools\zig, or pass -ZigPath with the full path to zig.exe.'
        }
        $ZigDirectory = Split-Path -Parent $ResolvedZigExe
        if (($env:PATH -split ';') -notcontains $ZigDirectory) { $env:PATH = $ZigDirectory + ';' + $env:PATH }
        $ZigVersionText = (& $ResolvedZigExe version 2>&1 | Out-String).Trim()
        $ZigExitCode = $LASTEXITCODE
        if ($ZigExitCode -ne 0 -or [string]::IsNullOrWhiteSpace($ZigVersionText)) {
            throw "Zig compiler could not run successfully: $ResolvedZigExe"
        }
        Write-LogLine "[ZIG] Executable: $ResolvedZigExe"
        Write-LogLine "[ZIG] Version: $ZigVersionText"
        Write-LogLine '[STAGE END] Locate and validate Zig compiler'
    }

    Write-LogLine '[STAGE START] Install or reuse Python build dependencies'
    if ((-not $SkipDependencyInstall) -or $NeedNewVenv) {
        Invoke-Native $Python @('-m','pip','install','--disable-pip-version-check','--upgrade','pip','wheel') 'Update build tooling'
        Invoke-Native $Python @('-m','pip','install','--disable-pip-version-check','-r',$RequirementsPath) 'Install application and Nuitka build dependencies'
    } else {
        Write-LogLine '[SKIPPED] Dependency installation disabled by FAST build mode; existing .build_venv is reused.'
    }
    Write-LogLine '[STAGE END] Install or reuse Python build dependencies'

    if ($Compiler -eq 'ZIG') {
        Write-LogLine '[STAGE START] Ensure Nuitka 4.x Zig backend'
        # The existing requirements-build.txt deliberately stays on Nuitka 2.x for the
        # unchanged MSVC GitHub workflow. Zig+Python 3.13 needs the newer supported backend.
        Invoke-Native $Python @('-m','pip','install','--disable-pip-version-check','--upgrade','Nuitka>=4.1,<5') 'Install Nuitka 4.x with supported Zig backend'
        Invoke-Native $Python @('-m','nuitka','--version') 'Verify installed Nuitka Zig-capable version'
        Write-LogLine '[STAGE END] Ensure Nuitka 4.x Zig backend'
    }

    Write-LogLine '[STAGE START] Check/install optional PyAudio package'
    if (-not $SkipOptionalPyAudio) {
        Write-LogLine "`n=== Optional microphone compatibility package ==="
        $PyAudioCode = Invoke-Native $Python @('-m','pip','install','--disable-pip-version-check','--only-binary=:all:','PyAudio') 'Install optional PyAudio microphone compatibility package' -AllowFailure
        if ($PyAudioCode -ne 0) {
            Write-LogLine 'WARNING: PyAudio wheel could not be installed in this run. Checking whether a previously installed wheel is available.'
        }
    }
    $PyAudioCheck = Invoke-Native $Python @('-c','import importlib.util,sys; sys.exit(0 if importlib.util.find_spec("pyaudio") else 1)') 'Check optional PyAudio availability' -AllowFailure
    $HasPyAudio = ($PyAudioCheck -eq 0)
    if (-not $HasPyAudio) {
        Write-LogLine 'NOTE: PyAudio is not available. The main Gemini Live lesson path uses sounddevice; SpeechRecognition microphone capture may need separate PyAudio support.'
    }
    Write-LogLine "PyAudio available: $HasPyAudio"
    Write-LogLine '[STAGE END] Check/install optional PyAudio package'

    # Create the output folders after dependency checks, then measure free space
    # again so pip cannot silently consume the build's remaining safety margin.
    Write-LogLine '[STAGE START] Prepare output folders and run disk-space preflight'
    Write-LogLine "[POWERSHELL] New-Item -ItemType Directory -Force -Path `"$DistDir`", `"$NuitkaWorkDir`""
    New-Item -ItemType Directory -Force -Path $DistDir, $NuitkaWorkDir | Out-Null
    $NuitkaOutputDir = Join-Path $NuitkaWorkDir 'main.dist'
    $NuitkaExePath = Join-Path $NuitkaOutputDir $ExeName

    # Disk preflight: C generation can consume several GB before the compiler starts.
    # The work drive needs at least 12 GB; project and Windows TEMP drives need 5 GB.
    $DiskChecks = @(
        @{ Label = 'Project/output'; Path = $ProjectRoot; MinimumGB = 5.0 },
        @{ Label = 'Nuitka compiler workspace'; Path = $NuitkaWorkDir; MinimumGB = 12.0 },
        @{ Label = 'Windows temporary directory'; Path = ([string]$env:TEMP); MinimumGB = 5.0 }
    )
    $DriveRequirements = @{}
    foreach ($Check in $DiskChecks) {
        if ([string]::IsNullOrWhiteSpace($Check.Path)) { continue }
        $DriveRoot = [System.IO.Path]::GetPathRoot([System.IO.Path]::GetFullPath($Check.Path))
        $DriveName = $DriveRoot.TrimEnd('\').TrimEnd(':')
        if ([string]::IsNullOrWhiteSpace($DriveName)) { continue }
        if (-not $DriveRequirements.ContainsKey($DriveName)) {
            $DriveRequirements[$DriveName] = [pscustomobject]@{ MinimumGB = [double]$Check.MinimumGB; Labels = @($Check.Label); Root = $DriveRoot }
        } else {
            $DriveRequirements[$DriveName].MinimumGB = [Math]::Max([double]$DriveRequirements[$DriveName].MinimumGB, [double]$Check.MinimumGB)
            $DriveRequirements[$DriveName].Labels += $Check.Label
        }
    }
    foreach ($DriveName in $DriveRequirements.Keys) {
        $DriveInfo = Get-PSDrive -Name $DriveName -PSProvider FileSystem -ErrorAction SilentlyContinue
        if ($null -eq $DriveInfo) { throw "Could not inspect free disk space for drive $DriveName`:. Check that the build and TEMP paths are on local accessible drives." }
        $FreeGB = [Math]::Round(([double]$DriveInfo.Free / 1GB), 2)
        $RequiredGB = [double]$DriveRequirements[$DriveName].MinimumGB
        Write-LogLine ("DISK CHECK {0}: {1} GB free; minimum {2} GB; used for: {3}" -f $DriveRequirements[$DriveName].Root, $FreeGB, $RequiredGB, ($DriveRequirements[$DriveName].Labels -join ', '))
        if ($FreeGB -lt $RequiredGB) {
            throw ("Insufficient free space on {0}. Available: {1} GB; required minimum: {2} GB. Free space and run BUILD_SETUP.bat again. Recommended free space on the Nuitka workspace drive: 20 GB or more." -f $DriveRequirements[$DriveName].Root, $FreeGB, $RequiredGB)
        }
        if ($DriveRequirements[$DriveName].Labels -contains 'Nuitka compiler workspace' -and $FreeGB -lt 20) {
            Write-LogLine ("WARNING: {0} GB is free on the Nuitka workspace drive. The build may fit, but 20 GB or more is recommended." -f $FreeGB)
        }
    }
    Write-LogLine '[STAGE END] Prepare output folders and run disk-space preflight'

    # A prior successful standalone folder is removed only after the disk preflight passes.
    if (Test-Path -LiteralPath $AppDistDir) {
        Write-LogLine "[POWERSHELL] Remove-Item -LiteralPath `"$AppDistDir`" -Recurse -Force"
        Remove-Item -LiteralPath $AppDistDir -Recurse -Force
    }

    # Embed Windows Explorer version properties into the application executable.
    $Parts = @($Version.Split('.') | ForEach-Object { [int]$_ })
    while ($Parts.Count -lt 4) { $Parts += 0 }
    $Tuple = ($Parts[0..3] -join ', ')
    $VersionInfoPath = Join-Path $ProjectRoot 'build\version_info.txt'
    $VersionInfo = @"
VSVersionInfo(
  ffi=FixedFileInfo(
    filevers=($Tuple), prodvers=($Tuple),
    mask=0x3f, flags=0x0, OS=0x4, fileType=0x1, subtype=0x0, date=(0, 0)
  ),
  kids=[
    StringFileInfo([
      StringTable('040904B0', [
        StringStruct('CompanyName', 'Engo'),
        StringStruct('FileDescription', 'Engo PDF Viewer & AI Study Agent'),
        StringStruct('FileVersion', '$Version'),
        StringStruct('InternalName', 'Engo'),
        StringStruct('OriginalFilename', '$ExeName'),
        StringStruct('ProductName', 'Engo PDF Viewer & AI Study Agent'),
        StringStruct('ProductVersion', '$Version')
      ])
    ]),
    VarFileInfo([VarStruct('Translation', [1033, 1200])])
  ]
)
"@
    Write-LogLine "[POWERSHELL] Set-Content -LiteralPath `"$VersionInfoPath`" -Encoding ASCII (version resource metadata)"
    Set-Content -LiteralPath $VersionInfoPath -Value $VersionInfo -Encoding ASCII

    Write-LogLine '[STAGE START] Build application with Nuitka (Python analysis, C/C++ compilation, packaging)'
    # Nuitka compiles Python modules into native extension/binary code and ships a
    # normal standalone application directory (not a single-file executable).
    # The original .py source remains in the development project, not in dist.
    # Build Nuitka argv as a List[string], adding exactly one complete argument
    # per Add() call. This avoids PowerShell array-expression / positional-binding
    # edge cases with option values that contain spaces (app name, paths, etc.).
    $NuitkaArgs = New-Object 'System.Collections.Generic.List[string]'
    [void]$NuitkaArgs.Add('--mode=standalone')
    [void]$NuitkaArgs.Add('--enable-plugin=pyqt6')
    [void]$NuitkaArgs.Add('--windows-console-mode=disable')
    [void]$NuitkaArgs.Add('--assume-yes-for-downloads')
    if ($Compiler -eq 'ZIG') {
        # Zig supports 64-bit Windows Python 3.13+ in current Nuitka 4.x releases.
        [void]$NuitkaArgs.Add('--zig')
    } else {
        # Keep the default GitHub Actions/MSVC path unchanged.
        [void]$NuitkaArgs.Add('--msvc=latest')
    }
    # Preserve two-job compilation in the normal GitHub workflow. Nuitka's
    # --low-memory option implies --jobs=1, so it is added only when the user
    # explicitly requests the emergency -LowMemory fallback.
    if ($LowMemory) {
        [void]$NuitkaArgs.Add('--low-memory')
    } else {
        [void]$NuitkaArgs.Add(("--jobs={0}" -f $script:BuildNuitkaJobs))
    }
    # Keep link-time optimization disabled to avoid an additional link-time
    # memory peak. This does not by itself guarantee that C1002 will disappear.
    [void]$NuitkaArgs.Add('--lto=no')
    # Intentionally keep Nuitka's main.build directory for subsequent builds.
    # The very first retry after this compiler change should use
    # -CleanNuitkaWorkspace to discard stale MinGW/MSVC intermediate objects.
    [void]$NuitkaArgs.Add(('--output-dir={0}' -f $NuitkaWorkDir))
    [void]$NuitkaArgs.Add(('--output-filename={0}' -f $ExeName))
    [void]$NuitkaArgs.Add(('--windows-icon-from-ico={0}' -f $IconPath))
    [void]$NuitkaArgs.Add(('--file-version={0}.0' -f $Version))
    [void]$NuitkaArgs.Add(('--product-version={0}.0' -f $Version))
    [void]$NuitkaArgs.Add('--company-name=Engo')
    [void]$NuitkaArgs.Add('--product-name=Engo PDF Viewer & AI Study Agent')
    [void]$NuitkaArgs.Add('--file-description=Engo PDF Viewer & AI Study Agent')
    [void]$NuitkaArgs.Add(('--include-data-files={0}=engopdfviewer.ico' -f $IconPath))
    [void]$NuitkaArgs.Add(('--include-data-files={0}=checkbox_checked.png' -f $CheckboxPath))
    [void]$NuitkaArgs.Add(('--include-data-files={0}=combo_chevron_light.png' -f $ChevronPath))
    [void]$NuitkaArgs.Add(('--include-data-files={0}=combo_chevron_up_light.png' -f $ChevronUpLightPath))
    [void]$NuitkaArgs.Add(('--include-data-files={0}=combo_chevron_up_dark.png' -f $ChevronUpDarkPath))
    [void]$NuitkaArgs.Add(('--include-data-files={0}=ENGO_PROGRAM_GUIDE.md' -f $GuidePath))
    # main.py was split into several local modules (engo_*.py). Nuitka compiles
    # every Python module to its OWN C file. Standalone mode already follows
    # their imports; listing them explicitly is a safety net so a module can
    # never be silently left out of the build. These C files are compiled in
    # parallel according to --jobs, normally two jobs on GitHub Actions.
    $EngoModuleFiles = @(Get-ChildItem -LiteralPath $ProjectRoot -Filter 'engo_*.py' -File | Sort-Object Name)
    if ($EngoModuleFiles.Count -eq 0) { throw 'No engo_*.py modules were found next to main.py; the split project is incomplete.' }
    foreach ($EngoModuleFile in $EngoModuleFiles) {
        $EngoModuleName = [System.IO.Path]::GetFileNameWithoutExtension($EngoModuleFile.Name)
        [void]$NuitkaArgs.Add(('--include-module={0}' -f $EngoModuleName))
    }
    Write-LogLine ("[NUITKA PARALLEL] Local split modules included ({0}): {1}" -f $EngoModuleFiles.Count, (($EngoModuleFiles | ForEach-Object { $_.Name }) -join ', '))
    [void]$NuitkaArgs.Add('--include-package=google.genai')
    [void]$NuitkaArgs.Add('--include-package=keyring')
    # The application imports the maintained package as `import pymupdf as fitz`.
    # It does not import the separate legacy top-level `fitz` package by name.
    # Keep PyMuPDF itself, but do not force the unrelated/legacy `fitz` tree.
    [void]$NuitkaArgs.Add('--include-package=pymupdf')
    [void]$NuitkaArgs.Add('--include-package=markdown')
    # Matplotlib is imported statically only for MathText rendering in main.py.
    # Standalone mode follows those visible imports automatically. Do not force
    # the entire package: that also pulled unused sphinxext modules (and doctest)
    # into analysis, greatly expanding the module graph before compilation.
    # sounddevice is a single Python module, not a package. Nuitka has a built-in
    # package configuration for this module that collects the Windows PortAudio DLLs.
    [void]$NuitkaArgs.Add('--include-module=sounddevice')
    [void]$NuitkaArgs.Add('--include-package=speech_recognition')
    [void]$NuitkaArgs.Add('--include-package=websockets')
    [void]$NuitkaArgs.Add('--include-module=PyQt6.QtNetwork')
    [void]$NuitkaArgs.Add('--include-module=keyring.backends.Windows')
    [void]$NuitkaArgs.Add('--include-package-data=google.genai')
    [void]$NuitkaArgs.Add('--include-package-data=matplotlib')
    Write-LogLine '[NUITKA OPTIMIZATION] Matplotlib is followed through its actual MathText imports; package data remains included for bundled fonts.'
    Write-LogLine '[NUITKA OPTIMIZATION] Excluding the test-only pyparsing.testing module that pulled unittest into the previous analysis.'
    Write-LogLine '[NUITKA DIAGNOSTICS] --show-progress, --show-memory, and --show-modules enabled for visibility into the analysis graph.'
    Write-LogLine '[NUITKA OPTIMIZATION] The source imports pymupdf as fitz; the separate forced fitz package/data inclusion has been removed.'
    [void]$NuitkaArgs.Add('--include-package-data=certifi')
    [void]$NuitkaArgs.Add('--include-package-data=keyring')
    [void]$NuitkaArgs.Add('--include-package-data=pymupdf')
    # pyparsing.testing is a test-only module and was the source of the
    # unittest anti-bloat warning in the captured Nuitka 2.8.10 run.
    [void]$NuitkaArgs.Add('--nofollow-import-to=pyparsing.testing')
    # markdown.test_tools is markdown's own test-support module (imports
    # unittest). Engo only ever imports the markdown conversion API at
    # runtime, never this test helper, so excluding it is safe and keeps one
    # more unittest-pulling module out of the analysis graph.
    [void]$NuitkaArgs.Add('--nofollow-import-to=markdown.test_tools')
    if ($Diagnostics) {
        # Emit module/progress diagnostics so a long analysis phase is
        # attributable to actual module inclusion. Opt-in only: printing a
        # line per analyzed module adds real I/O overhead across ~700+
        # modules, so normal builds leave this off for speed.
        [void]$NuitkaArgs.Add('--show-progress')
        [void]$NuitkaArgs.Add('--show-memory')
        [void]$NuitkaArgs.Add('--show-modules')
    }
    [void]$NuitkaArgs.Add('--include-package-data=markdown')
    [void]$NuitkaArgs.Add('--include-package-data=speech_recognition')
    [void]$NuitkaArgs.Add('--include-package-data=websockets')
    [void]$NuitkaArgs.Add(('--report={0}' -f (Join-Path $NuitkaWorkDir 'nuitka-compilation-report.xml')))
    if ($HasPyAudio) { [void]$NuitkaArgs.Add('--include-module=pyaudio') }
    # ONNX Runtime is not imported or used by this project; do not bundle it just
    # because it happens to be installed in a developer's build virtualenv.
    Write-LogLine 'Optional package check: ONNX Runtime is not explicitly bundled (no project reference found).'
    # Keep main.py as the single and final positional input after all options.
    [void]$NuitkaArgs.Add($MainPath)

    # Guard against a regression where a value with spaces is split into
    # multiple argv entries before launching Nuitka.
    $ExpectedAppNameArgument = '--output-filename={0}' -f $ExeName
    if (-not $NuitkaArgs.Contains($ExpectedAppNameArgument)) {
        throw "Nuitka argument construction failed: missing intact output filename argument: $ExpectedAppNameArgument"
    }
    if ($NuitkaArgs[$NuitkaArgs.Count - 1] -ne $MainPath) {
        throw 'Nuitka argument construction failed: main.py must be the final positional argument.'
    }
    Write-LogLine ("Nuitka argv entries: {0}" -f $NuitkaArgs.Count)
    Write-LogLine ("Nuitka intermediate files and compilation report will be written to: {0}" -f $NuitkaWorkDir)
    for ($ArgIndex = 0; $ArgIndex -lt $NuitkaArgs.Count; $ArgIndex++) {
        Write-LogLine ("  argv[{0}] = {1}" -f $ArgIndex, (ConvertTo-WindowsArgument ([string]$NuitkaArgs[$ArgIndex])))
    }

    # Remove only the previous standalone output tree. Keep main.build and the
    # per-user Nuitka compiler cache intact so unchanged third-party modules can
    # benefit from cached object files on repeat builds.
    if (Test-Path -LiteralPath $NuitkaOutputDir) {
        Write-LogLine ("[CACHE] Removing stale standalone output only: {0}" -f $NuitkaOutputDir)
        Remove-Item -LiteralPath $NuitkaOutputDir -Recurse -Force
    }

    # Pass the full Nuitka argv to a tiny Python launcher as Base64-encoded JSON.
    # The launcher uses subprocess([...]) so Windows/PowerShell never has to
    # re-parse option values containing spaces, ampersands, or multiple '=' signs.
    $NuitkaRunnerPath = Join-Path $NuitkaWorkDir 'invoke_nuitka.py'
    $NuitkaRunnerSource = @'
import base64
import json
import subprocess
import sys

try:
    arguments = json.loads(base64.b64decode(sys.argv[1]).decode("utf-8"))
    if not isinstance(arguments, list) or not all(isinstance(item, str) for item in arguments):
        raise ValueError("Nuitka arguments payload must be a JSON list of strings")
    completed = subprocess.run([sys.executable, "-m", "nuitka", *arguments], check=False)
    raise SystemExit(completed.returncode)
except SystemExit:
    raise
except Exception as exc:
    print("Nuitka launcher error: " + str(exc), file=sys.stderr)
    raise SystemExit(2)
'@
    [System.IO.File]::WriteAllText($NuitkaRunnerPath, $NuitkaRunnerSource, [System.Text.UTF8Encoding]::new($false))
    $NuitkaArgsJson = ConvertTo-Json -InputObject ([string[]]$NuitkaArgs.ToArray()) -Compress
    $NuitkaArgPayload = [Convert]::ToBase64String([System.Text.Encoding]::UTF8.GetBytes($NuitkaArgsJson))
    $CompilerMode = if ($Compiler -eq 'ZIG') { 'Zig' } else { 'MSVC latest' }
    if ($LowMemory) { $CompilerMode += '; --low-memory (one job)' } else { $CompilerMode += '; parallel jobs' }
    if ($Compiler -eq 'ZIG') { $CompilerMode += "; executable: $ResolvedZigExe" }
    Write-LogLine ("[COMPILER] {0}; compiler jobs: {1}; LTO disabled. Physical cores: {2}; logical processors: {3}." -f $CompilerMode, $script:BuildNuitkaJobs, $script:PhysicalCoreCount, $script:LogicalProcessorCount)
    Invoke-Native -Executable $Python -Arguments @($NuitkaRunnerPath, $NuitkaArgPayload) -Label 'Compile Engo with Nuitka into a protected standalone build'
    if (-not (Test-Path -LiteralPath $NuitkaExePath)) {
        throw "Nuitka finished but the standalone executable was not found at $NuitkaExePath. Check the compilation report and build log."
    }
    if ((Get-Item -LiteralPath $NuitkaExePath).Length -le 0) {
        throw "Nuitka created an empty application executable: $NuitkaExePath"
    }
    Write-LogLine '[STAGE END] Build application with Nuitka'
    Write-LogLine "[POWERSHELL] Copy-Item -LiteralPath `"$NuitkaOutputDir`" -Destination `"$AppDistDir`" -Recurse -Force"
    Copy-Item -LiteralPath $NuitkaOutputDir -Destination $AppDistDir -Recurse -Force
    $AppExePath = Join-Path $AppDistDir $ExeName
    if (-not (Test-Path -LiteralPath $AppExePath)) { throw "Nuitka standalone payload is missing the application executable: $AppExePath" }
    Write-LogLine '[STAGE END] Copy standalone application payload'

    # Optional Authenticode signing. No certificate or password is stored in source.
    $CertificateThumbprint = ([string]$env:ENGO_CERT_SHA1).Replace(' ', '')
    if ($CertificateThumbprint) {
        Write-LogLine '[STAGE START] Sign application executable using Authenticode'
        $SignToolCommand = Get-Command 'signtool.exe' -ErrorAction SilentlyContinue
        $SignTool = if ($SignToolCommand) { $SignToolCommand.Source } else { $null }
        if (-not $SignTool) {
            $SdkRoot = Join-Path ${env:ProgramFiles(x86)} 'Windows Kits\10\bin'
            if (Test-Path -LiteralPath $SdkRoot) {
                $SdkTools = Get-ChildItem -Path $SdkRoot -Filter 'signtool.exe' -Recurse -ErrorAction SilentlyContinue |
                    Where-Object { $_.FullName -match '\\x64\\signtool\.exe$' } |
                    Sort-Object FullName -Descending
                if ($SdkTools) { $SignTool = $SdkTools[0].FullName }
            }
        }
        if (-not $SignTool) { throw 'ENGO_CERT_SHA1 is set but signtool.exe was not found. Install the Windows SDK signing tools.' }
        Invoke-Native $SignTool @('sign','/sha1',$CertificateThumbprint,'/fd','SHA256','/tr','http://timestamp.digicert.com','/td','SHA256',$AppExePath) 'Sign the application executable'
    }

    Write-LogLine '[STAGE START] Compile Windows installer with NSIS'
    $InstallerPath = Join-Path $DistDir "Engo_Setup_v$Version.exe"
    if (Test-Path -LiteralPath $InstallerPath) {
        Write-LogLine "[POWERSHELL] Remove-Item -LiteralPath `"$InstallerPath`" -Force"
        Remove-Item -LiteralPath $InstallerPath -Force
    }
    Invoke-Native $Makensis @('/V3',"/DPRODUCT_VERSION=$Version",$NsisScript) 'Compile the professional Windows Setup and Uninstaller'
    if (-not (Test-Path -LiteralPath $InstallerPath -PathType Leaf)) {
        throw "NSIS compiler did not create the expected Setup file: $InstallerPath"
    }
    $InstallerInfo = Get-Item -LiteralPath $InstallerPath -ErrorAction Stop
    if ($InstallerInfo.Length -le 0) {
        throw "NSIS created an empty installer file: $InstallerPath"
    }
    Write-LogLine ("[INSTALLER VERIFIED] File exists and is non-empty: {0:N2} MB" -f ($InstallerInfo.Length / 1MB))
    Write-LogLine '[STAGE END] Compile Windows installer with NSIS'
    if ($CertificateThumbprint) {
        Write-LogLine '[STAGE START] Sign and verify Setup installer'
        Invoke-Native $SignTool @('sign','/sha1',$CertificateThumbprint,'/fd','SHA256','/tr','http://timestamp.digicert.com','/td','SHA256',$InstallerPath) 'Sign the Setup installer'
        Invoke-Native $SignTool @('verify','/pa','/v',$InstallerPath) 'Verify the Setup digital signature'
    }

    Write-LogLine "[POWERSHELL] Get-FileHash -LiteralPath `"$InstallerPath`" -Algorithm SHA256"
    $Hash = (Get-FileHash -LiteralPath $InstallerPath -Algorithm SHA256).Hash
    Write-LogLine "`nSUCCESS: $InstallerPath"
    Write-LogLine "SHA256: $Hash"
    Write-LogLine 'The generated installer includes the complete Nuitka standalone runtime and a registered Windows uninstaller. The installed payload contains no plain application .py source files.'

    if ($InstallAfterBuild) {
            Write-LogLine "`nLaunching Setup with Windows elevation (UAC)..."
        $Process = Start-Process -FilePath $InstallerPath -Verb RunAs -Wait -PassThru
        Write-LogLine "Setup process exit code: $($Process.ExitCode)"
        if ($Process.ExitCode -ne 0) { throw "Setup returned exit code $($Process.ExitCode)." }
    }

    if ($script:CancelRequested) { throw [System.OperationCanceledException]::new('Build cancelled by user with Ctrl+C before final success confirmation.') }
    $script:BuildSucceeded = $true
    Write-LogLine "`nBuild completed successfully."
    Write-LogLine "Setup: $InstallerPath"
    Write-LogLine "Stage log:   $LogPath"
    Write-LogLine "Session log: $SessionLogPath"
} catch {
    $CaughtError = $_
    $WasCancelled = ($script:CancelRequested -or ($CaughtError.Exception -is [System.OperationCanceledException]))
    if ($WasCancelled) {
        $script:BuildExitCode = 130
        Write-Host "`nBUILD CANCELLED" -ForegroundColor Yellow
        Write-LogLine '[CANCELLED] User interrupted the build. This run is NOT successful.'
        Write-LogLine ("CANCELLATION DETAILS: " + $CaughtError.Exception.ToString())
    } else {
        Write-Host "`nBUILD ERROR" -ForegroundColor Red
        Write-LogLine ("BUILD ERROR: " + $CaughtError.Exception.ToString())
    }
    if ($CaughtError.ErrorDetails -and $CaughtError.ErrorDetails.Message) {
        Write-LogLine ("ERROR DETAILS: " + $CaughtError.ErrorDetails.Message)
    }
    if ($CaughtError.CategoryInfo) { Write-LogLine ("ERROR CATEGORY: " + $CaughtError.CategoryInfo.ToString()) }
    if ($CaughtError.FullyQualifiedErrorId) { Write-LogLine ("ERROR ID: " + $CaughtError.FullyQualifiedErrorId) }
    if ($null -ne $CaughtError.TargetObject) { Write-LogLine ("ERROR TARGET: " + [string]$CaughtError.TargetObject) }
    if ($CaughtError.InvocationInfo -and $CaughtError.InvocationInfo.PositionMessage) {
        Write-LogLine ("POWERSHELL LOCATION: " + $CaughtError.InvocationInfo.PositionMessage)
    }
    if ($CaughtError.ScriptStackTrace) {
        Write-LogLine ("POWERSHELL STACK: " + $CaughtError.ScriptStackTrace)
    }
    Write-LogLine ("Log file: " + $LogPath)
    Write-Host "Detailed stage log: $LogPath" -ForegroundColor Yellow
    Write-Host "Full session log:  $SessionLogPath" -ForegroundColor Yellow
    if (-not $WasCancelled) { $script:BuildExitCode = 1 }
} finally {
    # This maximum-performance builder does not change Windows power settings.
    try {
        $script:BuildTimer.Stop()
        if ($script:CancelRequested -and $script:BuildExitCode -eq 0) {
            $script:BuildExitCode = 130
            $script:BuildSucceeded = $false
            Write-LogLine '[CANCELLED] Ctrl+C was received before final log closure; SUCCESS is revoked.'
        }
        if ($script:BuildExitCode -eq 0 -and -not $script:BuildSucceeded) {
            $script:BuildExitCode = 1
            Write-LogLine '[FINAL VALIDATION FAILED] Script reached finalization without completing every success condition.'
        }
        $BuildEndTime = Get-Date
        Write-LogLine '============================================================'
        Write-LogLine "BUILD SESSION ENDED: $($BuildEndTime.ToString('yyyy-MM-dd HH:mm:ss.fff'))"
        Write-LogLine ("TOTAL BUILD DURATION: {0:hh\:mm\:ss} ({1:N1} seconds)" -f $script:BuildTimer.Elapsed, $script:BuildTimer.Elapsed.TotalSeconds)
        Write-LogLine "FINAL EXIT CODE: $script:BuildExitCode"
        $FinalBuildResult = if ($script:BuildExitCode -eq 0 -and $script:BuildSucceeded) { 'SUCCESS' } elseif ($script:BuildExitCode -eq 130) { 'CANCELLED' } else { 'FAILED' }
        Write-LogLine "BUILD RESULT: $FinalBuildResult"
        Write-LogLine "STAGE LOG: $LogPath"
        Write-LogLine "SESSION LOG: $SessionLogPath"
        Write-LogLine 'ENGO BUILD SESSION COMPLETE'
    } catch {
        Write-Host "WARNING: Could not finalize build logs: $($_.Exception.ToString())" -ForegroundColor Yellow
    }
    try {
        if ($null -ne $script:CancelHandler) {
            [Console]::remove_CancelKeyPress($script:CancelHandler)
            $script:CancelHandler = $null
        }
    } catch { }
    try { if ($null -ne $script:LogWriter) { $script:LogWriter.Flush(); $script:LogWriter.Dispose() } } catch { }
    try { if ($null -ne $script:SessionLogWriter) { $script:SessionLogWriter.Flush(); $script:SessionLogWriter.Dispose() } } catch { }
}

exit ([int]$script:BuildExitCode)
