@echo off
setlocal EnableExtensions
cd /d "%~dp0"
for %%F in ("%~dp0dist\Engo_Setup_v*.exe") do if exist "%%~fF" (
  echo Launching existing Engo Setup: %%~nxF
  start "Engo Setup" "%%~fF"
  exit /b 0
)
echo No Setup package exists yet. Building the application and then launching Setup...
call "%~dp0BUILD_AND_INSTALL.bat"
exit /b %errorlevel%
