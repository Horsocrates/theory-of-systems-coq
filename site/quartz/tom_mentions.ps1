# tom_mentions.ps1 — link the FIRST mention of each paradox in each tom chapter to its catalog page.
# Idempotent: skips pages already linking the name; skips matches inside code, math, wikilinks.
$ErrorActionPreference = "Stop"
$enc = New-Object System.Text.UTF8Encoding($false)
$tables = Join-Path $PSScriptRoot "tables"
$tom = "C:\Users\abary\quartz-put-mudrosti\content\Библиотека\Том Математика"

function San([string]$s) { ($s -replace '\s*/\s*', ' — ' -replace '[\\/:*?"<>|]', '').Trim() }
function Stem([string]$w) {
  while ($w.Length -gt 4 -and 'аеиоуыэюяьй'.Contains($w[$w.Length-1])) { $w = $w.Substring(0, $w.Length-1) }
  return $w
}

# build (pageName, regex) list from the paradox table
$pats = New-Object System.Collections.Generic.List[object]
[System.IO.File]::ReadAllLines((Join-Path $tables 'paradoxes--Классификация v4.tsv'), $enc) |
  Select-Object -Skip 1 | Where-Object { $_.Trim("`t").Trim() -ne '' } | ForEach-Object {
    $c = @($_ -split "`t")
    if ($c.Count -lt 3) { return }
    $page = San ([string]$c[1])
    $clean = ([string]$c[1] -replace '\s*\([^)]*\)', '').Trim()
    $words = $clean -split '\s+'
    if ($words.Count -lt 2) { return }   # single-word names too ambiguous
    # [^\S\r\n]+ = пробелы/табы БЕЗ переносов строк: викиссылка с \n внутри ломает рендер
    if ($words[0] -match '^[Пп]арадокс$') {
      $tail = ($words | Select-Object -Skip 1 | ForEach-Object { [regex]::Escape($_) }) -join '[^\S\r\n]+'
      $rx = '[Пп]арадокс\w*[^\S\r\n]+' + $tail
    } else {
      $first = Stem $words[0]
      $rest = ($words | Select-Object -Skip 1 | ForEach-Object { [regex]::Escape($_) }) -join '[^\S\r\n]+'
      $rx = [regex]::Escape($first) + '\w*[^\S\r\n]+' + $rest
    }
    $pats.Add(@{ Page = $page; Rx = $rx })
  }
Write-Output "patterns: $($pats.Count)"

$linked = 0; $pagesTouched = 0
Get-ChildItem $tom -Recurse -File -Filter *.md | Where-Object { $_.Name -ne 'index.md' } | ForEach-Object {
  $f = $_.FullName
  $t = [System.IO.File]::ReadAllText($f, $enc)
  # mask code fences, display math, inline math, existing wikilinks
  $masks = New-Object System.Collections.Generic.List[string]
  $mask = [System.Text.RegularExpressions.MatchEvaluator]{
    param($m); $script:masks.Add($m.Value); '§MASK' + ($script:masks.Count - 1) + '§'
  }
  $script:masks = $masks
  # mask frontmatter first: заголовок/description главы не должны получать викиссылку в YAML
  $w = [regex]::Replace($t, '(?s)\A---.*?\r?\n---', $mask)
  $w = [regex]::Replace($w, '(?s)```.*?```', $mask)
  $w = [regex]::Replace($w, '(?s)\$\$.*?\$\$', $mask)
  $w = [regex]::Replace($w, '\$[^$\n]*\$', $mask)
  $w = [regex]::Replace($w, '\[\[[^\]]*\]\]', $mask)
  $changed = $false
  foreach ($p in $pats) {
    # ВАЖНО: детектор «уже слинковано» смотрит в ИСХОДНЫЙ текст $t, не в $w —
    # в $w существующие викиссылки уже замаскированы, и проверка по $w всегда false
    # (сломанная идемпотентность: каждый прогон линковал ещё одно упоминание).
    if ($t.Contains('[[' + $p.Page)) { continue }
    $m = [regex]::Match($w, $p.Rx)
    if (-not $m.Success) { continue }
    $w = $w.Remove($m.Index, $m.Length).Insert($m.Index, '[[' + $p.Page + '|' + $m.Value + ']]')
    $changed = $true; $linked++
  }
  if ($changed) {
    for ($i = $masks.Count - 1; $i -ge 0; $i--) { $w = $w.Replace('§MASK' + $i + '§', $masks[$i]) }
    [System.IO.File]::WriteAllText($f, $w, $enc)
    $pagesTouched++
  }
}
Write-Output "links added: $linked in $pagesTouched chapters"
