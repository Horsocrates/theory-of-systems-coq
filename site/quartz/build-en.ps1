# build-en.ps1 — английская сборка «The Path of Wisdom» в public\en\ и связь пар RU↔EN.
#
#   .\deploy.ps1          # сначала русская сборка (она очищает public\ целиком)
#   .\build-en.ps1        # затем английская: public\en\ + кнопка языка, hreflang, пометка черновика
#
# Шаги: tools\make-en-config.cjs -> quartz.config.en.yaml (русский конфиг + оверлей);
# подмена quartz.config.yaml на время сборки (с .bak-восстановлением, как в deploy.ps1);
# npx quartz build -d content-en -o public\en; восстановление конфига; tools\lang-pairs.cjs.
# Таблица слагов прода (regulus_app\scripts\slugs_en.tsv) нужна, чтобы ссылки английских страниц
# на ещё не переведённые вели на русские страницы.

param(
  [string]$Slugs = "C:\Users\abary\OneDrive\Desktop\regulus_app\scripts\slugs_en.tsv"
)
$ErrorActionPreference = "Stop"

$nodeDir = "C:\Users\abary\AppData\Local\Programs\node-v24.18.0-win-x64"
if ($env:Path -notlike "*$nodeDir*") { $env:Path = "$nodeDir;$env:Path" }

Set-Location $PSScriptRoot
$cfg = Join-Path $PSScriptRoot "quartz.config.yaml"
$bak = "$cfg.bak"

if (Test-Path $bak) {
  Copy-Item $bak $cfg -Force
  Remove-Item $bak -Force
  Write-Host "recovered quartz.config.yaml from stale .bak"
}
if (-not (Test-Path (Join-Path $PSScriptRoot "public\index.html"))) { throw "сначала русская сборка: .\deploy.ps1" }

node tools\make-en-config.cjs
if ($LASTEXITCODE -ne 0) { throw "make-en-config failed" }

Copy-Item $cfg $bak -Force
try {
  Copy-Item (Join-Path $PSScriptRoot "quartz.config.en.yaml") $cfg -Force
  npx quartz build -d content-en -o public/en
  if ($LASTEXITCODE -ne 0) { throw "quartz build (en) failed (exit $LASTEXITCODE)" }
}
finally {
  Copy-Item $bak $cfg -Force
  Remove-Item $bak -Force
  Write-Host "quartz.config.yaml restored"
}

$slugArg = @()
if (Test-Path $Slugs) { $slugArg = @("--slugs", $Slugs) } else { Write-Host "WARNING: slugs_en.tsv not found — links to untranslated pages stay as they are" }
node tools\lang-pairs.cjs --ru public --en public/en --content-en content-en @slugArg
if ($LASTEXITCODE -ne 0) { throw "lang-pairs failed" }
