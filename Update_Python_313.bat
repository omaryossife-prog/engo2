@echo off
setlocal EnableExtensions
cd /d "%~dp0"
title "Engo PDF Viewer & AI Study Agent - Install/Update Python 3.13"

echo ======================================================
echo Engo PDF Viewer ^& AI Study Agent - Python 3.13 installer / updater
echo ======================================================
echo This will install or update the official Python 3.13 runtime,
echo then install Engo PDF Viewer ^& AI Study Agent dependencies and build tools.
echo.

set "PYTHON_MANAGER="

REM Prefer the modern Python Install Manager executable.
pymanager install --help >nul 2>&1
if not errorlevel 1 set "PYTHON_MANAGER=pymanager"
if defined PYTHON_MANAGER goto manager_found

REM The modern manager can also be exposed through the py command.
py install --help >nul 2>&1
if not errorlevel 1 set "PYTHON_MANAGER=py"
if defined PYTHON_MANAGER goto manager_found

echo Python Install Manager was not found. Trying the official Microsoft Store package...
where winget >nul 2>&1
if errorlevel 1 goto manual_manager
winget install --id 9NQ7512CXL7T --source msstore --exact --accept-package-agreements --accept-source-agreements
if errorlevel 1 goto manual_manager

echo.
echo Checking the newly installed Python Install Manager...
pymanager install --help >nul 2>&1
if not errorlevel 1 set "PYTHON_MANAGER=pymanager"
if defined PYTHON_MANAGER goto manager_found
py install --help >nul 2>&1
if not errorlevel 1 set "PYTHON_MANAGER=py"
if defined PYTHON_MANAGER goto manager_found

echo.
echo The Python Install Manager was installed, but Windows has not refreshed the command path yet.
echo Close this window, open it again, and run Update_Python_313.bat one more time.
pause
exit /b 1

:manager_found
echo Using manager: %PYTHON_MANAGER%
echo Installing/updating the latest available regular Python 3.13 runtime...
%PYTHON_MANAGER% install --update 3.13
if errorlevel 1 goto runtime_failed

echo.
echo Verifying Python 3.13...
set "PYTHON_CMD=py -3.13"
%PYTHON_CMD% -c "import sys; print('Python:', sys.version); print('Executable:', sys.executable); raise SystemExit(0 if sys.version_info[:2] == (3,13) else 1)" >nul 2>&1
if not errorlevel 1 goto python_ready
set "PYTHON_CMD=pymanager exec 3.13"
%PYTHON_CMD% -c "import sys; print('Python:', sys.version); print('Executable:', sys.executable); raise SystemExit(0 if sys.version_info[:2] == (3,13) else 1)" >nul 2>&1
if not errorlevel 1 goto python_ready

echo.
echo Python 3.13 was installed, but neither py nor pymanager can launch it.
echo If an old Python Launcher is installed, open Windows Settings - Apps - Installed apps,
echo uninstall the old entry named "Python Launcher", then rerun this file.
pause
exit /b 1

:python_ready
echo Python 3.13 is ready:
%PYTHON_CMD% -c "import sys; print(sys.version); print(sys.executable)"
echo.
echo Updating pip...
%PYTHON_CMD% -m ensurepip --upgrade
if errorlevel 1 echo NOTE: ensurepip could not run; trying pip directly.
%PYTHON_CMD% -m pip install --upgrade pip
if errorlevel 1 goto package_failed

echo.
echo Installing Engo PDF Viewer ^& AI Study Agent requirements and Nuitka...
%PYTHON_CMD% -m pip install -r requirements.txt nuitka
if errorlevel 1 goto package_failed

echo.
echo Installing optional prebuilt PyAudio wheel for microphone input...
%PYTHON_CMD% -m pip install --upgrade --only-binary=:all: PyAudio
if errorlevel 1 echo NOTE: PyAudio wheel was not available for this Python/Windows setup. The PDF viewer can still run, but microphone input may need troubleshooting.

echo.
echo ======================================================
echo DONE - Python 3.13 and Engo dependencies are ready.
echo Now run run.bat, or build_exe.bat to create the EXE.
echo ======================================================
pause
exit /b 0

:runtime_failed
echo.
echo Python 3.13 could not be downloaded or installed.
echo Check your internet connection, then run this file again.
echo If this keeps failing, visit https://www.python.org/downloads/windows/
pause
exit /b 1

:package_failed
echo.
echo Python 3.13 is installed, but one or more Python packages failed to install.
echo Review the package error above, then run this file again after fixing the network/permissions issue.
pause
exit /b 1

:manual_manager
echo.
echo Automatic installation of Python Install Manager via winget was unavailable.
echo Open the official Python downloads page and install Python Install Manager:
start "" "https://www.python.org/downloads/windows/"
echo After installing the manager, close this window and run Update_Python_313.bat again.
pause
exit /b 1
