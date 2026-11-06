; Engo PDF Viewer & AI Study Agent - Windows Installer
; Built with NSIS 3.x. The compiler version is supplied by build_release.ps1.

Unicode true
!include "MUI2.nsh"
!include "LogicLib.nsh"
!include "x64.nsh"

!ifndef PRODUCT_VERSION
  !define PRODUCT_VERSION "2.3.6"
!endif

!define PRODUCT_NAME "Engo PDF Viewer & AI Study Agent"
!define PRODUCT_KEY  "EngoPDFViewerAIStudyAgent"
!define APP_EXE      "Engo PDF Viewer & AI Study Agent.exe"
!define COMPANY_NAME "Engo"
!define STARTMENU_KEY "Software\Engo\${PRODUCT_KEY}"

; Required by MUI_PAGE_STARTMENU and MUI_STARTMENU_WRITE_BEGIN.
Var StartMenuFolder

Name "${PRODUCT_NAME}"
Caption "${PRODUCT_NAME} Setup"
OutFile "${__FILEDIR__}\..\dist\Engo_Setup_v${PRODUCT_VERSION}.exe"
InstallDir "$PROGRAMFILES64\Engo\${PRODUCT_NAME}"
InstallDirRegKey HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "InstallLocation"
RequestExecutionLevel admin
; Registry view is selected inside .onInit and un.onInit.
; NSIS does not allow SetRegView at global script scope.
SetCompressor /SOLID lzma
SetCompressorDictSize 64
ShowInstDetails show
ShowUnInstDetails show
BrandingText "Engo"

; Windows Explorer > Properties metadata for the Setup executable.
VIProductVersion "${PRODUCT_VERSION}.0"
VIAddVersionKey /LANG=1033 "ProductName" "${PRODUCT_NAME}"
VIAddVersionKey /LANG=1033 "CompanyName" "${COMPANY_NAME}"
VIAddVersionKey /LANG=1033 "FileDescription" "Engo PDF Viewer & AI Study Agent Setup"
VIAddVersionKey /LANG=1033 "FileVersion" "${PRODUCT_VERSION}"
VIAddVersionKey /LANG=1033 "ProductVersion" "${PRODUCT_VERSION}"
VIAddVersionKey /LANG=1033 "OriginalFilename" "Engo_Setup_v${PRODUCT_VERSION}.exe"

; Keep the same AppId for all releases so upgrades target the existing installation.
; The build script does not generate a new identifier when the app version changes.

!define MUI_ABORTWARNING
!define MUI_ICON "${__FILEDIR__}\..\engopdfviewer.ico"
!define MUI_UNICON "${__FILEDIR__}\..\engopdfviewer.ico"
!define MUI_WELCOMEPAGE_TITLE "Welcome to Engo PDF Viewer & AI Study Agent Setup"
!define MUI_WELCOMEPAGE_TEXT "This wizard will install Engo PDF Viewer & AI Study Agent on your computer.$\r$\n$\r$\nOn the next page, choose the installation folder. You can browse to any available drive (for example D: or E:); the full application and its required runtime files will be installed together in that folder.$\r$\n$\r$\nClose any running copy of Engo before continuing. Your personal settings and study data are kept separately from the application files."
!define MUI_DIRECTORYPAGE_TEXT_TOP "Choose where Engo will be installed. Use Browse to select a folder on any available drive; the complete program will be installed inside the selected Engo folder."
!define MUI_DIRECTORYPAGE_TEXT_DESTINATION "Engo installation folder:"
!define MUI_FINISHPAGE_TITLE "Engo has been installed"
!define MUI_FINISHPAGE_TEXT "Engo PDF Viewer & AI Study Agent was installed successfully."
!define MUI_FINISHPAGE_RUN "$INSTDIR\${APP_EXE}"
!define MUI_FINISHPAGE_RUN_TEXT "Launch Engo PDF Viewer & AI Study Agent"
!define MUI_STARTMENUPAGE_DEFAULTFOLDER "${PRODUCT_NAME}"
!define MUI_STARTMENUPAGE_REGISTRY_ROOT HKLM
!define MUI_STARTMENUPAGE_REGISTRY_KEY "${STARTMENU_KEY}"
!define MUI_STARTMENUPAGE_REGISTRY_VALUENAME "StartMenuFolder"

!insertmacro MUI_PAGE_WELCOME
!insertmacro MUI_PAGE_COMPONENTS
!insertmacro MUI_PAGE_DIRECTORY
!insertmacro MUI_PAGE_STARTMENU Application $StartMenuFolder
!insertmacro MUI_PAGE_INSTFILES
!insertmacro MUI_PAGE_FINISH

!insertmacro MUI_UNPAGE_CONFIRM
!insertmacro MUI_UNPAGE_INSTFILES

!insertmacro MUI_LANGUAGE "English"
!insertmacro MUI_LANGUAGE "Arabic"

Function .onInit
  ${IfNot} ${RunningX64}
    MessageBox MB_ICONSTOP "Engo PDF Viewer & AI Study Agent requires 64-bit Windows."
    Abort
  ${EndIf}
  SetRegView 64
  SetShellVarContext all
  !insertmacro MUI_LANGDLL_DISPLAY

  ; A clean upgrade removes the previous app payload first, preventing obsolete
  ; DLLs from an older build from remaining in the installation folder.
  ; Engo settings, chats and user documents live outside this folder and are preserved.
  ReadRegStr $R0 HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "InstallLocation"
  ${If} $R0 != ""
    ${If} ${FileExists} "$R0\Uninstall.exe"
      MessageBox MB_YESNO|MB_ICONQUESTION "An existing Engo installation was found.$\r$\n$\r$\nThe previous application files will be removed before this version is installed. Your settings and study data will be preserved.$\r$\n$\r$\nContinue?" IDYES +2
        Abort
      ExecWait '"$R0\Uninstall.exe" /S _?=$R0' $R1
      ${If} $R1 != 0
        MessageBox MB_ICONSTOP "The previous Engo installation could not be removed (code $R1). Close Engo and try again."
        Abort
      ${EndIf}
    ${EndIf}
  ${EndIf}
FunctionEnd

Section "Engo PDF Viewer & AI Study Agent (required)" SEC_CORE
  SectionIn RO
  SetShellVarContext all
  SetOutPath "$INSTDIR"

  ; Each release is a fresh Nuitka standalone build. Copy the complete runtime tree.
  File /r "${__FILEDIR__}\..\dist\Engo PDF Viewer & AI Study Agent\*.*"

  WriteUninstaller "$INSTDIR\Uninstall.exe"

  !insertmacro MUI_STARTMENU_WRITE_BEGIN Application
    CreateDirectory "$SMPROGRAMS\$StartMenuFolder"
    CreateShortCut "$SMPROGRAMS\$StartMenuFolder\${PRODUCT_NAME}.lnk" "$INSTDIR\${APP_EXE}" "" "$INSTDIR\${APP_EXE}" 0
    CreateShortCut "$SMPROGRAMS\$StartMenuFolder\Uninstall ${PRODUCT_NAME}.lnk" "$INSTDIR\Uninstall.exe"
  !insertmacro MUI_STARTMENU_WRITE_END

  ; Add/Remove Programs entry.
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "DisplayName" "${PRODUCT_NAME}"
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "DisplayVersion" "${PRODUCT_VERSION}"
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "Publisher" "${COMPANY_NAME}"
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "InstallLocation" "$INSTDIR"
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "DisplayIcon" "$INSTDIR\${APP_EXE}"
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "UninstallString" '"$INSTDIR\Uninstall.exe"'
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "QuietUninstallString" '"$INSTDIR\Uninstall.exe" /S'
  WriteRegDWORD HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "NoModify" 1
  WriteRegDWORD HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "NoRepair" 1
  WriteRegDWORD HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}" "EstimatedSize" 0
SectionEnd

Section /o "Create a desktop shortcut" SEC_DESKTOP
  SetShellVarContext all
  CreateShortCut "$DESKTOP\${PRODUCT_NAME}.lnk" "$INSTDIR\${APP_EXE}" "" "$INSTDIR\${APP_EXE}" 0
SectionEnd

LangString DESC_CORE ${LANG_ENGLISH} "Install Engo and all required runtime files."
LangString DESC_DESKTOP ${LANG_ENGLISH} "Create a shortcut on the Windows desktop."
LangString DESC_CORE ${LANG_ARABIC} "تثبيت Engo وجميع ملفات التشغيل المطلوبة."
LangString DESC_DESKTOP ${LANG_ARABIC} "إنشاء اختصار للبرنامج على سطح المكتب."
!insertmacro MUI_FUNCTION_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${SEC_CORE} $(DESC_CORE)
  !insertmacro MUI_DESCRIPTION_TEXT ${SEC_DESKTOP} $(DESC_DESKTOP)
!insertmacro MUI_FUNCTION_DESCRIPTION_END

Section "Uninstall"
  SetShellVarContext all
  Delete "$DESKTOP\${PRODUCT_NAME}.lnk"

  ; Remove the Start Menu group using the previously selected folder name.
  ReadRegStr $R0 HKLM "${STARTMENU_KEY}" "StartMenuFolder"
  ${If} $R0 != ""
    RMDir /r "$SMPROGRAMS\$R0"
  ${EndIf}

  DeleteRegKey HKLM "${STARTMENU_KEY}"
  DeleteRegKey HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PRODUCT_KEY}"
  RMDir /r "$INSTDIR"
SectionEnd

Function un.onInit
  SetRegView 64
  SetShellVarContext all
  IfSilent un_silent un_interactive
un_interactive:
  MessageBox MB_ICONQUESTION|MB_YESNO "Remove Engo PDF Viewer & AI Study Agent from this computer? Your personal settings and study data will not be deleted." IDYES un_silent
  Abort
un_silent:
FunctionEnd
