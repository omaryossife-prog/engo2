@echo off
setlocal EnableExtensions
cd /d "%~dp0"
rem Force the project-local workspace so only this repository build cache is cleared.
set "ENGO_BUILD_TEMP_DIR="
if not exist "%~dp0build_logs" mkdir "%~dp0build_logs" >nul 2>&1
for /f %%I in ('powershell.exe -NoLogo -NoProfile -Command "Get-Date -Format yyyyMMdd_HHmmss_fff" 2^>nul') do set "STAMP=%%I"
if not defined STAMP set "STAMP=%RANDOM%_%RANDOM%"
set "LAUNCH_LOG=%~dp0build_logs\Engo_BuildLauncher_RECOVERY_%STAMP%.log"
title Engo - Clean Recovery Build (MSVC parallel)
echo [LAUNCH] %date% %time% > "%LAUNCH_LOG%"
echo [MODE] FULL + CLEAN NUITKA WORKSPACE (local physical-core parallelism)>> "%LAUNCH_LOG%"
echo [COMMAND] powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0build_release.ps1" -BuildMode FULL -CleanNuitkaWorkspace>> "%LAUNCH_LOG%"
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0build_release.ps1" -BuildMode FULL -CleanNuitkaWorkspace
set "RC=%errorlevel%"
echo [RETURN] %date% %time%>> "%LAUNCH_LOG%"
echo [POWERSHELL_EXIT_CODE] %RC%>> "%LAUNCH_LOG%"
echo.
if "%RC%"=="0" (
  echo Recovery build completed successfully. Check the dist folder.
) else if "%RC%"=="130" (
  echo Build cancelled by user.
) else (
  echo Recovery build failed. Open build_logs for the detailed compiler error.
)
echo Launcher log: %LAUNCH_LOG%
echo.
pause
exit /b %RC%
