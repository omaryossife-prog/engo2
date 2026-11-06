@echo off
setlocal EnableExtensions
cd /d "%~dp0"
title "Engo PDF Viewer & AI Study Agent - Microphone Repair"

echo ===============================================
echo Engo PDF Viewer ^& AI Study Agent - Microphone Support Repair
echo ===============================================
call :select_python
if not errorlevel 1 goto python_selected

echo Python 3.13 runtime was not found. Starting the automatic installer...
call "%~dp0Update_Python_313.bat"
if errorlevel 1 goto no_python
call :select_python
if errorlevel 1 goto no_python

:python_selected
%PYTHON_CMD% -c "import sys; print('Using Python:', sys.executable); print('Version:', sys.version.split()[0])"
echo.
echo Installing SpeechRecognition and the prebuilt PyAudio wheel...
%PYTHON_CMD% -m pip install --upgrade SpeechRecognition
if errorlevel 1 goto failed
%PYTHON_CMD% -m pip install --upgrade --only-binary=:all: PyAudio
if errorlevel 1 goto failed
echo.
echo Verifying microphone support in the same Python 3.13 environment...
%PYTHON_CMD% -c "import sys, speech_recognition, pyaudio; print('Python:', sys.executable); print('SpeechRecognition:', speech_recognition.__version__); print('PyAudio:', pyaudio.__version__); print('Microphone module import: OK')"
if errorlevel 1 goto failed
echo.
echo Microphone support is installed. Close and restart Engo PDF Viewer ^& AI Study Agent.
pause
exit /b 0

:select_python
set "PYTHON_CMD=py -3.13"
%PYTHON_CMD% -c "import sys; raise SystemExit(0 if sys.version_info[:2] == (3,13) else 1)" >nul 2>&1
if not errorlevel 1 exit /b 0
set "PYTHON_CMD=pymanager exec 3.13"
%PYTHON_CMD% -c "import sys; raise SystemExit(0 if sys.version_info[:2] == (3,13) else 1)" >nul 2>&1
if not errorlevel 1 exit /b 0
exit /b 1

:failed
echo.
echo PyAudio could not be installed. This may be a missing prebuilt wheel or a network issue.
echo Try again with internet access, and make sure Windows and Python have matching architecture (usually 64-bit).
pause
exit /b 1

:no_python
echo Python 3.13 could not be installed or launched. Review the errors above.
pause
exit /b 1
