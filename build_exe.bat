@echo off
setlocal EnableExtensions
cd /d "%~dp0"
echo The legacy EXE build shortcut now creates the complete Windows Setup package.
call "%~dp0BUILD_SETUP.bat"
exit /b %errorlevel%
