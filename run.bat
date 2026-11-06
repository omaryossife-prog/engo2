@echo off
setlocal EnableExtensions
cd /d "%~dp0"
title "Engo PDF Viewer & AI Study Agent v2.3.6"

call :select_python
if not errorlevel 1 goto python_selected

echo Python 3.13 runtime was not found. Starting the automatic installer...
call "%~dp0Update_Python_313.bat"
if errorlevel 1 goto no_python
call :select_python
if errorlevel 1 goto no_python

:python_selected
%PYTHON_CMD% -c "import sys; print('Using Python:', sys.executable); print('Version:', sys.version.split()[0])"

REM Native DOCX/PPTX reading and in-place text highlighting require lxml.
REM Check and install it using the same Python selected above, not another runtime.
%PYTHON_CMD% -c "from lxml import etree" >nul 2>&1
if errorlevel 1 (
    echo Native Office support needs lxml. Installing it for this Python 3.13 runtime...
    %PYTHON_CMD% -m pip install "lxml>=5.0"
    if errorlevel 1 (
        echo.
        echo ERROR: lxml could not be installed. Check your internet connection and Python permissions.
        echo You can retry manually with: %PYTHON_CMD% -m pip install "lxml^>=5.0"
        pause
        exit /b 1
    )
)
%PYTHON_CMD% -c "from lxml import etree; print('Native Office XML support: OK')"

%PYTHON_CMD% -c "import markdown" >nul 2>&1
if errorlevel 1 (
    echo Installing the Markdown renderer needed for formatted chat messages...
    %PYTHON_CMD% -m pip install "Markdown>=3.6"
    if errorlevel 1 echo WARNING: Markdown could not be installed; basic Qt Markdown fallback will be used.
)
%PYTHON_CMD% main.py
if errorlevel 1 pause
exit /b 0

:select_python
set "PYTHON_CMD=py -3.13"
%PYTHON_CMD% -c "import sys; raise SystemExit(0 if sys.version_info[:2] == (3,13) else 1)" >nul 2>&1
if not errorlevel 1 exit /b 0
set "PYTHON_CMD=pymanager exec 3.13"
%PYTHON_CMD% -c "import sys; raise SystemExit(0 if sys.version_info[:2] == (3,13) else 1)" >nul 2>&1
if not errorlevel 1 exit /b 0
exit /b 1

:no_python
echo.
echo Could not install or launch Python 3.13. Check the error above.
pause
exit /b 1
