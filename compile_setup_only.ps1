$ErrorActionPreference = 'Stop'
$ProjectRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $ProjectRoot

function Find-NsisCompiler {
    $Candidates = @(
        (Join-Path $env:ProgramFiles 'NSIS\makensis.exe'),
        (Join-Path ${env:ProgramFiles(x86)} 'NSIS\makensis.exe'),
        (Join-Path $env:LOCALAPPDATA 'Programs\NSIS\makensis.exe'),
        (Join-Path $env:ProgramFiles 'NSIS\Bin\makensis.exe'),
        (Join-Path ${env:ProgramFiles(x86)} 'NSIS\Bin\makensis.exe')
    ) | Where-Object { $_ -and (Test-Path -LiteralPath $_) }
    if ($Candidates.Count -gt 0) { return $Candidates[0] }
    $Command = Get-Command 'makensis.exe' -ErrorAction SilentlyContinue
    if ($Command) { return $Command.Source }
    return $null
}

try {
    $MainPath = Join-Path $ProjectRoot 'main.py'
    $NsisScript = Join-Path $ProjectRoot 'installer\EngoInstaller.nsi'
    $AppName = 'Engo PDF Viewer & AI Study Agent'
    $AppExe = Join-Path $ProjectRoot "dist\$AppName\$AppName.exe"
    if (-not (Test-Path -LiteralPath $MainPath)) { throw "main.py was not found: $MainPath" }
    if (-not (Test-Path -LiteralPath $NsisScript)) { throw "NSIS script was not found: $NsisScript" }
    if (-not (Test-Path -LiteralPath $AppExe)) {
        throw "The Nuitka standalone application build is missing: $AppExe`nRun BUILD_SETUP.bat first to build the application."
    }

    $Source = Get-Content -LiteralPath $MainPath -Raw -Encoding UTF8
    $VersionMatch = [regex]::Match($Source, '(?m)^APP_VERSION\s*=\s*["'']([^"'']+)["'']')
    if (-not $VersionMatch.Success) { throw 'Could not read APP_VERSION from main.py.' }
    $Version = $VersionMatch.Groups[1].Value

    $Makensis = Find-NsisCompiler
    if (-not $Makensis) { throw 'NSIS compiler makensis.exe was not found. Install NSIS, then retry.' }

    $DistDir = Join-Path $ProjectRoot 'dist'
    New-Item -ItemType Directory -Force -Path $DistDir | Out-Null
    $InstallerPath = Join-Path $DistDir "Engo_Setup_v$Version.exe"
    if (Test-Path -LiteralPath $InstallerPath) { Remove-Item -LiteralPath $InstallerPath -Force }

    Write-Host 'Engo - Compile Setup only' -ForegroundColor Cyan
    Write-Host "Version: $Version"
    Write-Host "NSIS:    $Makensis"
    Write-Host 'The Nuitka standalone application is already present; it will not be rebuilt.'
    & $Makensis '/V3' "/DPRODUCT_VERSION=$Version" $NsisScript
    $Code = [int]$LASTEXITCODE
    if ($Code -ne 0) { throw "NSIS compilation failed with exit code $Code." }
    if (-not (Test-Path -LiteralPath $InstallerPath)) { throw "NSIS did not create the expected installer: $InstallerPath" }

    $Hash = (Get-FileHash -LiteralPath $InstallerPath -Algorithm SHA256).Hash
    Write-Host ''
    Write-Host 'SETUP CREATED SUCCESSFULLY' -ForegroundColor Green
    Write-Host "File:   $InstallerPath"
    Write-Host "SHA256: $Hash"
} catch {
    Write-Host ''
    Write-Host 'SETUP COMPILATION FAILED' -ForegroundColor Red
    Write-Host $_.Exception.Message -ForegroundColor Yellow
    exit 1
}
