ENGO LOCAL BUILD USING ZIG (NO VISUAL STUDIO BUILD TOOLS)
=========================================================

What this patch changes
-----------------------
- Adds a local-only Zig build path selected with -Compiler ZIG.
- Keeps MSVC as the script default, so the existing GitHub Actions workflow
  continues to use its current MSVC setup without modification.
- Keeps the two-job native compilation setting (--jobs=2).
- Uses a separate build\nuitka_zig workspace so MSVC and Zig objects are not mixed.
- Uses requirements-build-zig.txt to install Nuitka 4.x only in the local Zig
  build environment. The existing requirements-build.txt remains unchanged.
- Intended for 64-bit Python 3.13 on Windows; Nuitka Zig backend is Windows x64-only.
- Keeps the app's existing standalone, PyQt6, version-resource, package and
  installer settings intact.

Before running
--------------
1. Download the official Windows x86_64 Zig ZIP from https://ziglang.org/download/.
2. Extract it so this file exists:
      C:\Tools\zig\zig.exe
   (or place zig.exe on PATH, or pass -ZigPath manually to the PowerShell script.)
3. Confirm the app project has Python 3.13 x64 and NSIS installed.
4. Copy these three files into the root of the Engo project, replacing the
   existing build_release.ps1:
      build_release.ps1
      requirements-build-zig.txt
      BUILD_SETUP_ZIG.bat
5. Double-click BUILD_SETUP_ZIG.bat.

Build behavior
--------------
- First Zig build uses a clean Zig-specific workspace.
- The number of native compiler jobs is set to 2.
- The existing MSVC workspace is not deleted.
- The existing GitHub Actions workflow remains on MSVC because Compiler defaults
  to MSVC and the workflow was not changed by this patch.
- Output installer is expected under dist, same as the existing build script.
- Detailed logs are written under build_logs.

Manual invocation
-----------------
  powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File .\build_release.ps1 -BuildMode FULL -Compiler ZIG -NuitkaJobs 2 -CleanNuitkaWorkspace

You can specify a non-default compiler path with:
  -ZigPath "D:\Tools\zig\zig.exe"

Important limitations
---------------------
- This changes the compiler backend; it does not guarantee Zig will compile
  every native dependency successfully on the first attempt.
- Test the produced installer and key Engo features before publishing it.
- This patch was structurally checked in the current Linux workspace, but a
  Windows Zig/Nuitka build was not executed here.
