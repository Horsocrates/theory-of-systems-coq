# tom_nav.ps1 — post-pass: prev/next navigation line at the bottom of every tom chapter.
# Idempotent. Run after tex2md/batch_tom (and together with tom_concepts.ps1).
$ErrorActionPreference = "Stop"
$enc = New-Object System.Text.UTF8Encoding($false)
$tom = "C:\Users\abary\quartz-put-mudrosti\content\Библиотека\Направления\Математика\Том Математика"
$linkRoot = "Библиотека/Направления/Математика/Том Математика"
$romans = @('I','II','III','IV','V','VI','VII','VIII','IX','X','XI','XII','XIII','XIV','XV','XVI','XVII','XVIII','XIX','XX')

# ordered chapter list: intro, then parts 01..20 with chapters sorted by filename
$seq = New-Object System.Collections.Generic.List[object]
$intro = Join-Path $tom "00 Методологическое введение.md"
if (Test-Path $intro) {
  $seq.Add(@{ File = $intro; Link = "$linkRoot/00 Методологическое введение"; Title = 'Методологическое введение'; Part = 0 })
}
$parts = Get-ChildItem $tom -Directory | Sort-Object Name
foreach ($p in $parts) {
  $pn = [int]($p.Name.Substring(0, 2))
  Get-ChildItem $p.FullName -File -Filter *.md | Where-Object { $_.Name -ne 'index.md' } | Sort-Object Name | ForEach-Object {
    $t = [System.IO.File]::ReadAllText($_.FullName, $enc)
    $title = [regex]::Match($t, 'title: "([^"]+)"').Groups[1].Value
    if (-not $title) { $title = $_.BaseName }
    $seq.Add(@{ File = $_.FullName; Link = "$linkRoot/$($p.Name)/$($_.BaseName)"; Title = $title; Part = $pn })
  }
}
Write-Output "sequence: $($seq.Count) pages"

for ($i = 0; $i -lt $seq.Count; $i++) {
  $cur = $seq[$i]
  $navParts = @()
  if ($i -gt 0) {
    $prev = $seq[$i - 1]
    $lbl = $prev.Title
    if ($prev.Part -ne $cur.Part -and $prev.Part -gt 0) { $lbl += (' — Часть ' + $romans[$prev.Part - 1]) }
    $navParts += ('← [[' + $prev.Link + '|' + $lbl + ']]')
  }
  if ($i -lt $seq.Count - 1) {
    $next = $seq[$i + 1]
    $lbl = $next.Title
    if ($next.Part -ne $cur.Part -and $next.Part -gt 0) { $lbl += (' — Часть ' + $romans[$next.Part - 1]) }
    $navParts += ('[[' + $next.Link + '|' + $lbl + ']] →')
  }
  $navLine = 'Навигация: ' + ($navParts -join ' · ')
  $t = [System.IO.File]::ReadAllText($cur.File, $enc)
  $t = [regex]::Replace($t, "(?m)^Навигация: .*\r?\n?", '')
  $t = $t.TrimEnd() + "`n`n" + $navLine + "`n"
  [System.IO.File]::WriteAllText($cur.File, $t, $enc)
}
Write-Output "nav lines written"
