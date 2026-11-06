@echo off
setlocal EnableExtensions
cd /d "%~dp0"
title Engo - Build, Package and Install
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0build_release.ps1" -InstallAfterBuild
set "RC=%errorlevel%"
echo.
if "%RC%"=="130" echo Build cancelled by user.
if not "%RC%"=="0" if not "%RC%"=="130" echo Build or installation failed. Open build_logs for details.
echo.
pause
exit /b %RC%
