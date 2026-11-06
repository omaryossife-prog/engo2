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
