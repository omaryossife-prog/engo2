Engo build logs
================

Both BUILD_SETUP.bat (FULL) and BUILD_SETUP_FAST.bat (FAST) create two UTF-8 logs in build_logs\:

1) Engo_BuildSession_*.log
   Full session record: build mode, start/end timestamps, PowerShell and Windows details,
   architecture, build flags, all logged build output, duration, result, and final exit code.

2) Engo_Build_*.log
   Detailed stage record: commands and arguments, Python probe output, native process stdout/stderr,
   Nuitka and NSIS output, stage markers, elapsed times, warnings, and errors.

The two files created by the same run share the same timestamp, PowerShell PID, and run ID.
Logs are flushed as the build runs so they can be opened while a build is still in progress.


Compiler recovery notes
=======================

This build profile targets Python 3.13 x64 with MSVC (Visual Studio 2022 or newer),
not MinGW64. Install Visual Studio Build Tools with the "Desktop development with C++"
workload (MSVC x64/x86 tools and a Windows 10/11 SDK) on a local build machine.
The build now uses Nuitka --low-memory, which implies one compiler job, to reduce
peak memory while compiling the large google.genai.types module. A fatal MSVC/SCons
error is detected from streamed output so remaining compiler workers are stopped promptly.

After switching from a previous MinGW build, run BUILD_SETUP_RECOVERY.bat once.
It deletes only the generated build\nuitka workspace (intermediate compiler files) and starts a clean FULL build;
it does not delete your source files, .build_venv, dist installer history, or logs.
For normal subsequent builds, use BUILD_SETUP.bat or BUILD_SETUP_FAST.bat.

The GitHub Actions job timeout is set to 360 minutes (the documented maximum for
GitHub-hosted runners), and the build cache key is separated from the old compiler
profile so incompatible intermediate objects are not restored.
