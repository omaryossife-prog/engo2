# ENGO local Zig build with a Windows Job Object CPU hard cap.
# Place beside build_release.ps1 in D:\ENGO1\1 and run from PowerShell.

$ErrorActionPreference = 'Stop'
$Project = $PSScriptRoot
$BuildScript = Join-Path $Project 'build_release.ps1'
$TempPath = 'F:\ENGO_TEMP'
$CpuLimitPercent = 50

if (-not (Test-Path -LiteralPath $BuildScript -PathType Leaf)) {
    Write-Host "ERROR: build_release.ps1 was not found in $Project" -ForegroundColor Red
    exit 2
}

# build_release.ps1 removes the old Nuitka workspace first when
# -CleanNuitkaWorkspace is supplied, then performs its own 12 GB D: preflight.
# This outer check allows that cleanup to reclaim space before the real preflight.
$minimumC = 5GB
$minimumDBeforeCleanup = 10GB
$minimumF = 5GB

$c = [int64](Get-PSDrive -Name C).Free
$d = [int64](Get-PSDrive -Name D).Free
$f = [int64](Get-PSDrive -Name F).Free
Write-Host ("C: {0:N2} GB free | D: {1:N2} GB free | F: {2:N2} GB free" -f ($c / 1GB), ($d / 1GB), ($f / 1GB))

if ($c -lt $minimumC -or $d -lt $minimumDBeforeCleanup -or $f -lt $minimumF) {
    Write-Host 'Build stopped: insufficient initial free space (C: 5 GB, D: 10 GB before cleanup, F: 5 GB).' -ForegroundColor Yellow
    exit 3
}

New-Item -ItemType Directory -Force -Path $TempPath | Out-Null
$env:TEMP = $TempPath
$env:TMP = $TempPath

if (-not ('EnGoCpuJobLimit' -as [type])) {
    Add-Type -TypeDefinition @'
using System;
using System.ComponentModel;
using System.Runtime.InteropServices;

public static class EnGoCpuJobLimit
{
    [StructLayout(LayoutKind.Explicit)]
    private struct CpuRateControlInfo
    {
        [FieldOffset(0)] public UInt32 ControlFlags;
        [FieldOffset(4)] public UInt32 CpuRate;
    }

    [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true)]
    private static extern IntPtr CreateJobObject(IntPtr attributes, string name);

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool SetInformationJobObject(IntPtr job, int infoClass, IntPtr info, UInt32 length);

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool AssignProcessToJobObject(IntPtr job, IntPtr process);

    [DllImport("kernel32.dll")]
    private static extern IntPtr GetCurrentProcess();

    [DllImport("kernel32.dll")]
    private static extern bool CloseHandle(IntPtr handle);

    public static IntPtr ApplyToCurrentProcess(int percent)
    {
        if (percent < 1 || percent > 100)
            throw new ArgumentOutOfRangeException("percent");

        IntPtr job = CreateJobObject(IntPtr.Zero, null);
        if (job == IntPtr.Zero)
            throw new Win32Exception(Marshal.GetLastWin32Error(), "CreateJobObject failed");

        try
        {
            CpuRateControlInfo info = new CpuRateControlInfo();
            info.ControlFlags = 0x1u | 0x4u; // ENABLE | HARD_CAP
            info.CpuRate = (UInt32)(percent * 100);

            IntPtr buffer = Marshal.AllocHGlobal(Marshal.SizeOf(typeof(CpuRateControlInfo)));
            try
            {
                Marshal.StructureToPtr(info, buffer, false);
                if (!SetInformationJobObject(job, 15, buffer, (UInt32)Marshal.SizeOf(typeof(CpuRateControlInfo))))
                    throw new Win32Exception(Marshal.GetLastWin32Error(), "SetInformationJobObject failed");
            }
            finally
            {
                Marshal.FreeHGlobal(buffer);
            }

            if (!AssignProcessToJobObject(job, GetCurrentProcess()))
                throw new Win32Exception(Marshal.GetLastWin32Error(), "AssignProcessToJobObject failed");

            return job; // Keep the handle open for the entire build.
        }
        catch
        {
            CloseHandle(job);
            throw;
        }
    }

    public static void CloseJob(IntPtr job)
    {
        if (job != IntPtr.Zero) CloseHandle(job);
    }
}
'@
}

$jobHandle = [IntPtr]::Zero
$exitCode = 0
try {
    $currentProcess = [System.Diagnostics.Process]::GetCurrentProcess()
    $currentProcess.PriorityClass = [System.Diagnostics.ProcessPriorityClass]::BelowNormal

    $jobHandle = [EnGoCpuJobLimit]::ApplyToCurrentProcess($CpuLimitPercent)
    Write-Host "CPU HARD CAP ACTIVE: $CpuLimitPercent% total CPU | BelowNormal priority | NuitkaJobs 2." -ForegroundColor Cyan
    Write-Host 'Child compiler processes inherit the same CPU-limited Job Object.' -ForegroundColor Cyan
    Write-Host 'The main builder will clean its old Nuitka workspace, then re-check D: for at least 12 GB.' -ForegroundColor Cyan

    Write-Host 'Starting local FULL build with Zig...' -ForegroundColor Green
    & $BuildScript -BuildMode FULL -Compiler ZIG -NuitkaJobs 2 -CleanNuitkaWorkspace

    if ($null -ne $LASTEXITCODE) { $exitCode = [int]$LASTEXITCODE }
}
catch {
    Write-Host ("BUILD NOT STARTED / STOPPED: {0}" -f $_.Exception.Message) -ForegroundColor Red
    Write-Host 'The build was not allowed to continue without the CPU hard cap.' -ForegroundColor Yellow
    $exitCode = 4
}
finally {
    if ($jobHandle -ne [IntPtr]::Zero) {
        [EnGoCpuJobLimit]::CloseJob($jobHandle)
    }
}

exit $exitCode
