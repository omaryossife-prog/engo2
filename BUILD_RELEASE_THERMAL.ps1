# ENGO local Zig build with moderate CPU limits.
# Place this file in D:\ENGO1\1 and run it from PowerShell.

$ErrorActionPreference = 'Stop'
$Project = $PSScriptRoot
$BuildScript = Join-Path $Project 'build_release.ps1'
$TempPath = 'F:\ENGO_TEMP'

if (-not (Test-Path -LiteralPath $BuildScript -PathType Leaf)) {
    Write-Host "ERROR: build_release.ps1 was not found in $Project" -ForegroundColor Red
    exit 2
}

# Preserve the build script's existing disk-space safety requirements.
$requiredC = 5GB
$requiredD = 12GB
$c = Get-PSDrive -Name C
$d = Get-PSDrive -Name D
$cFree = [int64]$c.Free
$dFree = [int64]$d.Free

Write-Host ("C: {0:N2} GB free | D: {1:N2} GB free" -f ($cFree / 1GB), ($dFree / 1GB))
if ($cFree -lt $requiredC -or $dFree -lt $requiredD) {
    Write-Host 'Build stopped: free space is below the required minimum (C: 5 GB, D: 12 GB).' -ForegroundColor Yellow
    exit 3
}

# Keep temporary build files off C:, as in the previous working setup.
New-Item -ItemType Directory -Force -Path $TempPath | Out-Null
$env:TEMP = $TempPath
$env:TMP = $TempPath

# Moderate thermal limit: 6 of the machine's 12 logical processors.
# NuitkaJobs remains 2, so compilation parallelism is not reduced to one job.
try {
    $buildProcess = [System.Diagnostics.Process]::GetCurrentProcess()
    $buildProcess.PriorityClass = [System.Diagnostics.ProcessPriorityClass]::BelowNormal
    $buildProcess.ProcessorAffinity = [IntPtr]0x3F
    Write-Host 'Thermal limit active: BelowNormal priority, CPU affinity 0-5, NuitkaJobs 2.' -ForegroundColor Cyan
}
catch {
    Write-Warning ("Could not apply one or more CPU limits: {0}" -f $_.Exception.Message)
    Write-Warning 'The build will continue with the normal process settings.'
}

Write-Host 'Starting local FULL build with Zig...' -ForegroundColor Green
& $BuildScript -BuildMode FULL -Compiler ZIG -NuitkaJobs 2 -CleanNuitkaWorkspace

$code = 0
if ($null -ne $LASTEXITCODE) {
    $code = [int]$LASTEXITCODE
}
exit $code
