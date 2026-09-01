# deploy.ps1 — build the «Путь Мудрости» Quartz site for deployment.
#
#   .\deploy.ps1                          # build with baseUrl from quartz.config.yaml (localhost dev)
#   .\deploy.ps1 -BaseUrl "example.com"   # build for production domain (config restored afterwards)
#   .\deploy.ps1 -Serve                   # build + dev server on :8080
#   .\deploy.ps1 -SkipLinkCheck           # без пост-проверки ссылок
#
# Output: .\public\ — self-contained static site, ready to upload
# (VPS: copy public\* to the nginx web root; GitHub Pages: push public\* to the pages branch).
# После сборки автоматически гоняется tools\linkcheck.cjs (битые ссылки -> ненулевой exit).

param(
  [string]$BaseUrl = "",
  [switch]$Serve,
  [switch]$SkipLinkCheck
)
$ErrorActionPreference = "Stop"

$nodeDir = "C:\Users\abary\AppData\Local\Programs\node-v24.18.0-win-x64"
if ($env:Path -notlike "*$nodeDir*") { $env:Path = "$nodeDir;$env:Path" }

Set-Location $PSScriptRoot
$cfg = Join-Path $PSScriptRoot "quartz.config.yaml"
$bak = "$cfg.bak"
$enc = New-Object System.Text.UTF8Encoding($false)

# crash-recovery: прошлый запуск умер до restore — вернуть конфиг из .bak ДО всего
if (Test-Path $bak) {
  Copy-Item $bak $cfg -Force
  Remove-Item $bak -Force
  Write-Host "recovered quartz.config.yaml from stale .bak (прошлый запуск не дожил до restore)"
}

$orig = [System.IO.File]::ReadAllText($cfg, $enc)

try {
  if ($BaseUrl -ne "") {
    Copy-Item $cfg $bak -Force
    $patched = $orig -replace '(?m)^(\s*baseUrl:).*$', ('$1 ' + $BaseUrl)
    if ($patched -eq $orig) { throw "строка baseUrl: в quartz.config.yaml не найдена/не заменена" }
    [System.IO.File]::WriteAllText($cfg, $patched, $enc)
    Write-Host "baseUrl -> $BaseUrl"
  }
  if ($Serve) { npx quartz build --serve } else { npx quartz build }
  if ($LASTEXITCODE -ne 0) { throw "quartz build failed (exit $LASTEXITCODE)" }
}
finally {
  if ($BaseUrl -ne "") {
    [System.IO.File]::WriteAllText($cfg, $orig, $enc)
    if (Test-Path $bak) { Remove-Item $bak -Force }
    Write-Host "quartz.config.yaml restored"
  }
}

if (-not $Serve -and -not $SkipLinkCheck) {
  node (Join-Path $PSScriptRoot "tools\linkcheck.cjs")
  if ($LASTEXITCODE -ne 0) { throw "link check FAILED — битые ссылки в public\ (см. выше)" }
  if ($BaseUrl -ne "") {
    $leak = Get-ChildItem (Join-Path $PSScriptRoot "public") -Filter "*.xml" |
      Select-String -Pattern "localhost" -List
    if ($leak) { throw "localhost протёк в sitemap/RSS — baseUrl-патч не применился" }
    Write-Host "no localhost leaks in sitemap/RSS"
  }
}

