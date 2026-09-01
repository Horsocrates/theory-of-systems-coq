# batch_tom.ps1 — convert Части II–XX (113 chapters) into site part folders.
$ErrorActionPreference = "Stop"
$enc = New-Object System.Text.UTF8Encoding($false)

# load converter functions: take LOCAL tex2md.ps1 up to the pilot driver marker
# (раньше грузился из session-scratchpad — путь с GUID умирал вместе с сессией)
$libSrc = Join-Path $PSScriptRoot "tex2md.ps1"
$libText = [System.IO.File]::ReadAllText($libSrc, $enc)
$cut = $libText.IndexOf('# --- pilot driver')
if ($cut -lt 0) { throw "marker '# --- pilot driver' not found in $libSrc" }
$libPath = Join-Path $env:TEMP "tex2md-lib.ps1"
[System.IO.File]::WriteAllText($libPath, $libText.Substring(0, $cut), (New-Object System.Text.UTF8Encoding($true)))
. $libPath

$book = "C:\Users\abary\OneDrive\Desktop\theory-of-systems-coq\Книги\Математика"
$tomRoot = "C:\Users\abary\quartz-put-mudrosti\content\Библиотека\Том Математика"
$romans = @('I','II','III','IV','V','VI','VII','VIII','IX','X','XI','XII','XIII','XIV','XV','XVI','XVII','XVIII','XIX','XX')

$totalCh = 0; $warnings = @()
for ($n = 2; $n -le 20; $n++) {
  $roman = $romans[$n-1]
  $nn = "{0:d2}" -f $n
  $bookPart = Join-Path $book ("Часть " + $roman)

  # part title/description: from flat page (first run) or existing folder index (re-run)
  $flat = Get-ChildItem $tomRoot -File -Filter "$nn *.md" | Select-Object -First 1
  if ($flat) {
    $metaText = [System.IO.File]::ReadAllText($flat.FullName, $enc)
    $partFolderName = [System.IO.Path]::GetFileNameWithoutExtension($flat.Name)
  } else {
    $dir = Get-ChildItem $tomRoot -Directory -Filter "$nn *" | Select-Object -First 1
    if (-not $dir) { $warnings += "no source of meta for part $nn"; continue }
    $metaText = [System.IO.File]::ReadAllText((Join-Path $dir.FullName "index.md"), $enc)
    $partFolderName = $dir.Name
  }
  $partTitle = [regex]::Match($metaText, 'title: "([^"]+)"').Groups[1].Value
  $partDesc  = [regex]::Match($metaText, 'description: "([^"]+)"').Groups[1].Value
  $sitePart = Join-Path $tomRoot $partFolderName
  New-Item -ItemType Directory -Force $sitePart | Out-Null

  # chapters
  $chapterLinks = @()
  $glavy = Get-ChildItem $bookPart -Directory | Where-Object { $_.Name -match '^Глава (\d+)$' } |
           Sort-Object { [int]([regex]::Match($_.Name, '\d+').Value) }
  foreach ($g in $glavy) {
    $k = [int]([regex]::Match($g.Name, '\d+').Value)
    $cand = Get-ChildItem $g.FullName -Filter "chapter-*.tex" | Sort-Object Length -Descending
    if (-not $cand) { $warnings += "no tex in $($bookPart)\$($g.Name)"; continue }
    if ($cand.Count -gt 1) { $warnings += "multiple tex in Часть $roman/$($g.Name): took $($cand[0].Name)" }
    $res = Convert-TexToMd -texPath $cand[0].FullName
    $plainTitle = Convert-MathToPlain $res.Title
    if ($plainTitle -eq '') { $plainTitle = "Глава $k" }
    $fname = ("{0:d2} {1}" -f $k, ($plainTitle -replace '[\\/:*?"<>|]', '')).Trim().TrimEnd('.')
    $md = "---`n" +
          ("title: `"Глава {0}. {1}`"`n" -f $k, ($plainTitle -replace '"', '')) +
          "---`n`n" + $res.Body + "`n`n---`n`n" +
          ("Часть: [[{0}|{1}]] · Том: [[Том Математика|«Математика»]]`n" -f $partFolderName, $partTitle)
    [System.IO.File]::WriteAllText((Join-Path $sitePart "$fname.md"), $md, $enc)
    $chapterLinks += ("{0}. [[{1}|Глава {0}. {2}]]" -f $k, $fname, $plainTitle)
    $totalCh++
  }

  # part index
  $idx = "---`n" +
         "title: `"$partTitle`"`n" +
         "description: `"$partDesc`"`n" +
         "---`n`n" + $partDesc + "`n`n**Главы:**`n`n" + ($chapterLinks -join "`n") + "`n`n---`n`n" +
         "Том: [[Том Математика|«Математика»]] · Направление: [[Математика]]`n"
  [System.IO.File]::WriteAllText((Join-Path $sitePart "index.md"), $idx, $enc)
  if ($flat) { Remove-Item $flat.FullName -Force -Confirm:$false }
  Write-Output ("Часть {0} ({1}): {2} глав" -f $roman, $partFolderName, $chapterLinks.Count)
}

Write-Output "TOTAL chapters converted: $totalCh"
if ($warnings) { "=== warnings ==="; $warnings | ForEach-Object { $_ } }

# leftover report across all new parts
$left = @{}
Get-ChildItem $tomRoot -Recurse -Filter *.md | ForEach-Object {
  $c = [System.IO.File]::ReadAllText($_.FullName, $enc)
  $c = [regex]::Replace($c, '(?s)```.*?```', '')
  $c = [regex]::Replace($c, '(?s)\$\$.*?\$\$', '')
  $c = [regex]::Replace($c, '\$[^$\n]*\$', '')
  foreach ($m in [regex]::Matches($c, '\\[a-zA-Z]+')) { $left[$m.Value]++ }
}
"=== leftover commands outside math/code (top 20) ==="
$left.GetEnumerator() | Sort-Object Value -Descending | Select-Object -First 20 | ForEach-Object { "{0}: {1}" -f $_.Key, $_.Value }
