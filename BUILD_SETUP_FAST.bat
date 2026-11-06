@echo off
setlocal EnableExtensions
cd /d "%~dp0"
if not exist "%~dp0build_logs" mkdir "%~dp0build_logs" >nul 2>&1
rem Legacy recovery only: run a restore command if an older builder left one behind.
for %%F in ("%~dp0build_logs\Engo_BuildPowerRestore_*.cmd") do if exist "%%~fF" call "%%~fF" >nul 2>&1
for /f %%I in ('powershell.exe -NoLogo -NoProfile -Command "Get-Date -Format yyyyMMdd_HHmmss_fff" 2^>nul') do set "STAMP=%%I"
if not defined STAMP set "STAMP=%RANDOM%_%RANDOM%"
set "LAUNCH_LOG=%~dp0build_logs\Engo_BuildLauncher_FAST_%STAMP%.log"
title Engo - Fast Rebuild Setup
echo [LAUNCH] %date% %time% > "%LAUNCH_LOG%"
echo [MODE] FAST>> "%LAUNCH_LOG%"
echo [COMMAND] powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0build_release.ps1" -BuildMode FAST -SkipDependencyInstall -SkipOptionalPyAudio>> "%LAUNCH_LOG%"
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0build_release.ps1" -BuildMode FAST -SkipDependencyInstall -SkipOptionalPyAudio
set "RC=%errorlevel%"
rem Legacy recovery only; this builder does not alter the active Windows power plan.
for %%F in ("%~dp0build_logs\Engo_BuildPowerRestore_*.cmd") do if exist "%%~fF" call "%%~fF" >nul 2>&1
echo [RETURN] %date% %time%>> "%LAUNCH_LOG%"
echo [POWERSHELL_EXIT_CODE] %RC%>> "%LAUNCH_LOG%"
echo [DETAIL] See Engo_Build_*.log and Engo_BuildSession_*.log for stage output.>> "%LAUNCH_LOG%"
echo.
if "%RC%"=="130" (
  echo Build cancelled by user. No SUCCESS status was recorded.
) else if not "%RC%"=="0" (
  echo Fast build failed. Open build_logs for Engo_Build_*.log and Engo_BuildSession_*.log.
) else (
  echo Fast Setup rebuild completed. See dist and build_logs for both detailed logs.
)
echo Launcher log: %LAUNCH_LOG%
echo.
pause
exit /b %RC%
