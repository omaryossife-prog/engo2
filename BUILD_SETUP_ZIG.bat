@echo off
setlocal EnableExtensions
cd /d "%~dp0"
if not exist "%~dp0build_logs" mkdir "%~dp0build_logs" >nul 2>&1
for /f %%I in ('powershell.exe -NoLogo -NoProfile -Command "Get-Date -Format yyyyMMdd_HHmmss_fff" 2^>nul') do set "STAMP=%%I"
if not defined STAMP set "STAMP=%RANDOM%_%RANDOM%"
set "LAUNCH_LOG=%~dp0build_logs\Engo_BuildLauncher_ZIG_%STAMP%.log"
title Engo - Local Zig Build (2 compiler jobs)
echo [LAUNCH] %date% %time% > "%LAUNCH_LOG%"
echo [MODE] FULL + ZIG + 2 compiler jobs>> "%LAUNCH_LOG%"
echo [COMMAND] powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0build_release.ps1" -BuildMode FULL -Compiler ZIG -NuitkaJobs 2 -CleanNuitkaWorkspace>> "%LAUNCH_LOG%"
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0build_release.ps1" -BuildMode FULL -Compiler ZIG -NuitkaJobs 2 -CleanNuitkaWorkspace
set "RC=%errorlevel%"
echo [RETURN] %date% %time%>> "%LAUNCH_LOG%"
echo [POWERSHELL_EXIT_CODE] %RC%>> "%LAUNCH_LOG%"
echo.
if "%RC%"=="0" (
  echo Zig build completed. Check the installer in the dist folder.
) else if "%RC%"=="130" (
  echo Build cancelled by user.
) else (
  echo Zig build failed. Open build_logs for Engo_Build_*.log and Engo_BuildSession_*.log.
)
echo Launcher log: %LAUNCH_LOG%
echo.
pause
exit /b %RC%
