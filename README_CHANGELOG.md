# Engo PDF Viewer v17 – AI chat, voice focus and installed UI fixes

## Changes in this update

- Kept the chat header close (×) control and removed the unused AI-settings dialog entry point from the chat module. AI provider settings remain in Application Settings, in the maintenance rows before Clear cache / Reset.
- Refined the chat panel open/close sequence: the pane slides first, then recent messages cascade into view. Closing reverses the message/composer motion. Full-screen chat uses the same empty-panel-then-reveal behavior, with a coordinated collapse on exit.
- Restored the complete selected PDF passage in the user's sent message. The excerpt itself is clickable and returns to its saved PDF page/region; the existing temporary yellow navigation highlight remains non-destructive and fades after its brief display.
- Updated the saved-passage title, preview tooltip and jump label when the interface language changes, without rebuilding or losing the conversation transcript.
- Added wrapping rules for Markdown list items and table cells so long numbered steps/calculations wrap inside the chat width instead of forcing horizontal scrolling.
- Improved voice-tutor handwriting focus: boxes are widened to a readable line-sized region, and fuzzy PDF text-block matches are accepted only when they overlap the model's selected visual area. Existing stale-focus clearing after speech playback is preserved.
- Kept and verified the existing selected-region answer scope: approximately 80% selected region / 20% relevant PDF context when PDF context is enabled; selected-only 100% scope when disabled.
- Forced the Arabic AI toolbar captions to retain their requested mixed Arabic/Latin order: `(ai محادثة مع)` and `(ai حصة صوتية مع)`.
- Hardened asset lookup for source, PyInstaller and Nuitka installed layouts. All four light/dark combo chevron assets are present and listed in the release build script.

## Validation

- All project Python files passed `py_compile` syntax validation.
- Static assertions passed for chat close/settings placement, saved passage navigation, yellow highlight path, 80/20 and 100% context instructions, Markdown wrapping, voice focus sizing, Arabic toolbar captions, resource lookup and all four packaged chevron assets.
- The interactive PyQt UI and Windows installer/EXE were not run in this environment because PyQt6 is not installed here. Rebuild with `BUILD_SETUP.bat` on the Windows development machine to test the real UI and setup package.
