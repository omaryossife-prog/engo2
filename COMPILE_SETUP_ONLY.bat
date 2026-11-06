@echo off
setlocal EnableExtensions
cd /d "%~dp0"
title Engo - Compile Setup Only
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0compile_setup_only.ps1"
set "RC=%errorlevel%"
echo.
if not "%RC%"=="0" (
  echo Setup compilation failed. See the error above.
) else (
  echo Setup created in the dist folder.
)
echo.
pause
exit /b %RC%
