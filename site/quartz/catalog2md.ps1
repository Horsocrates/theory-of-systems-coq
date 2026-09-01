# catalog2md.ps1 v3 — per-entry pages + per-type and per-subcategory group pages.
# Source of truth: docs/*.xlsx → dump_xlsx.ps1 → this script.
$ErrorActionPreference = "Stop"
$enc = New-Object System.Text.UTF8Encoding($false)
$tables = Join-Path $PSScriptRoot "tables"
$lib = "C:\Users\abary\quartz-put-mudrosti\content\Библиотека"

function Read-Tsv([string]$name) {
  $out = New-Object System.Collections.Generic.List[object]
  [System.IO.File]::ReadAllLines((Join-Path $tables $name), $enc) |
    Where-Object { $_.Trim("`t").Trim() -ne '' } |
    ForEach-Object { $out.Add(@($_ -split "`t")) }
  return ,$out
}
function Esc([string]$s) { if ($null -eq $s) { '' } else { $s.Replace('|', '\|').Trim() } }
function San([string]$s) { ($s -replace '\s*/\s*', ' — ' -replace '[\\/:*?"<>|]', '').Trim() }
function DescQ([string]$s) { $t = $s.Replace('"', '«').Trim(); if ($t.Length -gt 180) { $t.Substring(0,177) + '…' } else { $t } }
function SortKey([string]$id) {
  (($id -split '\.') | ForEach-Object { if ($_ -match '^\d+$') { $_.PadLeft(4, '0') } else { $_ } }) -join '.'
}
function Cell([object]$r, [int]$i) { if ($r.Count -gt $i -and $r[$i]) { ([string]$r[$i]).Trim() } else { '' } }
function NormSub([string]$s) { if ($s -like '4.x*') { '4.1 Когнитивный диссонанс' } else { $s } }
# Заголовок секции механизма: без формулы в скобках и без хвоста после «/» — чтобы якорь был чистым
# (полное имя и код остаются в подписи под заголовком).
function SubHead([string]$s) {
  $t = ($s -replace '\s*\([^)]*\)\s*', ' ')
  $t = ($t -split '\s*/\s*')[0]
  return $t.Trim()
}

# ---------- load ----------
$cat = Read-Tsv 'fallacies--Каталог ошибок.tsv'; $cat.RemoveAt(0)
$k5  = Read-Tsv 'fallacies--Кат5-Контекстные.tsv'; $k5.RemoveAt(0)
$par = Read-Tsv 'paradoxes--Классификация v4.tsv'; $par.RemoveAt(0)
$syn = Read-Tsv 'fallacies--Синдромы.tsv'; $syn.RemoveAt(0)
$clsMap = @{}
$clsRows = Read-Tsv 'fallacies--Классификатор.tsv'; $clsRows.RemoveAt(0)
foreach ($r in $clsRows) { $code = Cell $r 1; if ($code) { $clsMap[$code] = @{ Name = (Cell $r 2); Desc = (Cell $r 3); Principle = (Cell $r 5) } } }

$types = @{
  '1 - Условия'            = @{ Folder = '01 Нарушения условий';          Title = 'Нарушения условий (Тип 1)';          Intro = 'Рассуждение не начинается — его место занимает манипуляция, принуждение или дефектный вопрос.' }
  '2 - Домены'             = @{ Folder = '02 Нарушения доменов';           Title = 'Нарушения доменов (Тип 2)';           Intro = 'Рассуждение идёт, но отказывает внутри конкретного [[Домены рассуждения|домена]]. Крупнейшая категория каталога.' }
  '3 - Последовательность' = @{ Folder = '03 Нарушения последовательности'; Title = 'Нарушения последовательности (Тип 3)'; Intro = 'Рассуждение движется вспять, кругом или с перевёрнутыми ролями.' }
  '4 - Синдромы'           = @{ Folder = '04 Синдромы';                    Title = 'Синдромы (Тип 4)';                    Intro = 'Системные искажения всего процесса: всепроникающие, самоусиливающиеся, невидимые для поражённого.' }
}
$catDir = Join-Path $lib "Направления\Архитектура Рассуждения\Каталог ошибок"

# name maps
$k5ByName = @{}; foreach ($r in $k5) { $k5ByName[(San (Cell $r 2))] = $r }
$idToRu = @{}; $enToRu = @{}
foreach ($r in $cat) { $id = Cell $r 0; if ($id) { $ru = San (Cell $r 2); $idToRu[$id] = $ru; $en = Cell $r 1; if ($en -and -not $enToRu.ContainsKey($en)) { $enToRu[$en] = $ru } } }
foreach ($r in $k5) { $id = Cell $r 0; if ($id) { $idToRu[$id] = San (Cell $r 2) } }
$enCounts = @{}
foreach ($r in $cat) { $en = Cell $r 1; if ($en) { $enCounts[$en]++ } }
foreach ($r in $k5) { $en = Cell $r 1; if ($en) { $enCounts[$en]++ } }

function Link-Related([string]$raw) {
  if (-not $raw) { return '' }
  $parts = $raw -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ }
  $out = @()
  foreach ($p in $parts) {
    if ($idToRu.ContainsKey($p)) { $out += ('[[' + $idToRu[$p] + ']]') }
    elseif ($enToRu.ContainsKey($p)) { $out += ('[[' + $enToRu[$p] + '|' + $p + ']]') }
    else { $out += $p }
  }
  return $out -join ', '
}

# ---------- group (subcategory) registry, keyed by CODE ----------
$subPage = @{}
function SubCode([string]$sub) { ($sub -split ' ')[0] }
foreach ($r in $cat) {
  $catKey = Cell $r 3
  if (-not $types.ContainsKey($catKey)) { continue }
  $sub = NormSub (Cell $r 4)
  if (-not $sub) { continue }
  $code = SubCode $sub
  if ($subPage.ContainsKey($code)) { continue }
  $name = ($sub -replace ('^' + [regex]::Escape($code) + '\s*'), '')
  if ($clsMap.ContainsKey($code) -and $clsMap[$code].Name -and $clsMap[$code].Name -notmatch '^[A-Za-z]') { $name = $clsMap[$code].Name }
  $subPage[$code] = @{ Code = $code; PageName = (San ($code + ' ' + $name)); Label = $name; TypeKey = $catKey }
}
foreach ($r in $k5) {
  $sub = Cell $r 3
  if (-not $sub) { continue }
  $code = SubCode $sub
  if ($subPage.ContainsKey($code)) { continue }
  $name = ($sub -replace ('^' + [regex]::Escape($code) + '\s*'), '')
  $subPage[$code] = @{ Code = $code; PageName = (San ($code + ' ' + $name)); Label = $name; TypeKey = '5' }
}

# ---------- ПРОЗА-блоки: авторские главы (Том 2) на генерируемых страницах ----------
# Блок между <!-- ПРОЗА:НАЧАЛО --> и <!-- ПРОЗА:КОНЕЦ --> переживает перегенерацию:
# собирается здесь ДО очистки папок, возвращается при записи страницы.
# Ключ: "<папка типа>/<файл>.md"; индекс парадоксов — "парадоксы/index.md".
$proseRx = [regex]'(?s)<!-- ПРОЗА:НАЧАЛО -->.*?<!-- ПРОЗА:КОНЕЦ -->'
$proseBlocks = @{}
Get-ChildItem $catDir -Directory -ErrorAction SilentlyContinue | ForEach-Object {
  $tf = $_.Name
  Get-ChildItem $_.FullName -Filter *.md -ErrorAction SilentlyContinue | ForEach-Object {
    $m = $proseRx.Match([System.IO.File]::ReadAllText($_.FullName))
    if ($m.Success) { $proseBlocks[$tf + '/' + $_.Name] = $m.Value }
  }
}

# ---------- wipe & recreate ----------
Get-ChildItem $catDir -File -Filter *.md | Where-Object { $_.Name -ne 'index.md' } | Remove-Item -Force -Confirm:$false
Get-ChildItem $catDir -Directory -ErrorAction SilentlyContinue | Remove-Item -Recurse -Force -Confirm:$false
foreach ($t in $types.Values) { New-Item -ItemType Directory -Force (Join-Path $catDir $t.Folder) | Out-Null }
New-Item -ItemType Directory -Force (Join-Path $catDir '05 Контекстные методы') | Out-Null

$mergedNames = @{}
foreach ($r in $cat) { $n = San (Cell $r 2); if ($k5ByName.ContainsKey($n)) { $mergedNames[$n] = $true } }

function K5-Section($r) {
  $s = New-Object System.Text.StringBuilder
  [void]$s.AppendLine('')
  [void]$s.AppendLine('## Как метод (Тип 5)')
  [void]$s.AppendLine('')
  $sub = Cell $r 3
  $sc = SubCode $sub; $subLink = if ($subPage.ContainsKey($sc)) { '[[' + $subPage[$sc].PageName + '\|' + $sub + ']]' } else { $sub }
  [void]$s.AppendLine('**' + (Cell $r 0) + ' · ' + $subLink + '.** Метод валиден при своих условиях; задача — различение, а запретом он был бы только вне их.')
  [void]$s.AppendLine('')
  if (Cell $r 5) { [void]$s.AppendLine('**Когда валидно.** ' + (Cell $r 5)); [void]$s.AppendLine('') }
  if (Cell $r 6) { [void]$s.AppendLine('**Когда ошибка.** ' + (Cell $r 6)); [void]$s.AppendLine('') }
  if (Cell $r 7) { [void]$s.AppendLine('**Механизм различения.** ' + (Cell $r 7)); [void]$s.AppendLine('') }
  $ex = @()
  if (Cell $r 8) { $ex += ('**Валидно:** ' + (Cell $r 8)) }
  if (Cell $r 9) { $ex += ('**Ошибочно:** ' + (Cell $r 9)) }
  if ($ex) { [void]$s.AppendLine($ex -join "`n`n") }
  return $s.ToString()
}

# ---------- entry pages ----------
$pageCount = 0
foreach ($r in $cat) {
  $catKey = Cell $r 3
  if (-not $types.ContainsKey($catKey)) { continue }
  $ru = San (Cell $r 2); $en = Cell $r 1
  $sub = NormSub (Cell $r 4)
  $isMerged = $mergedNames.ContainsKey($ru)
  $folder = if ($isMerged) { '05 Контекстные методы' } else { $types[$catKey].Folder }
  $s = New-Object System.Text.StringBuilder
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('title: "' + $ru + '"')
  if ($en -and $enCounts[$en] -eq 1) { [void]$s.AppendLine('aliases: ["' + $en.Replace('"','') + '"]') }
  [void]$s.AppendLine('description: "' + (DescQ (Cell $r 7)) + '"')
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('')
  $sc = SubCode $sub; $subRef = if ($subPage.ContainsKey($sc)) { '[[' + $subPage[$sc].PageName + '|' + $sub + ']]' } else { $sub }
  $crumb = '**' + (Cell $r 0) + '** · [[' + $types[$catKey].Folder + '|' + $types[$catKey].Title + ']] → ' + $subRef
  if (Cell $r 5) { $crumb += ' · подтип: ' + (Cell $r 5) }
  if ($en) { $crumb += "`n`n*" + $en + '*' }
  [void]$s.AppendLine($crumb)
  [void]$s.AppendLine('')
  if (Cell $r 7) { [void]$s.AppendLine('**Формулировка.** ' + (Cell $r 7)); [void]$s.AppendLine('') }
  if (Cell $r 8) { [void]$s.AppendLine('**Механизм нарушения.** ' + (Cell $r 8)); [void]$s.AppendLine('') }
  if (Cell $r 9) { [void]$s.AppendLine('**Пример.** ' + (Cell $r 9)); [void]$s.AppendLine('') }
  if (Cell $r 11) { [void]$s.AppendLine('**Диагностический вопрос.** ' + (Cell $r 11)); [void]$s.AppendLine('') }
  if (Cell $r 12) { [void]$s.AppendLine('**Психологический источник.** ' + (Cell $r 12)); [void]$s.AppendLine('') }
  $rel = Link-Related (Cell $r 10)
  if ($rel) { [void]$s.AppendLine('**Связанные ошибки:** ' + $rel); [void]$s.AppendLine('') }
  if ($isMerged) { [void]$s.AppendLine((K5-Section $k5ByName[$ru])) }
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('')
  [void]$s.AppendLine('Каталог: [[Каталог ошибок]] · Концепт: [[Ошибки рассуждения]]')
  [System.IO.File]::WriteAllText((Join-Path (Join-Path $catDir $folder) ($ru + '.md')), $s.ToString(), $enc)
  $pageCount++
}
foreach ($r in $k5) {
  $ru = San (Cell $r 2)
  if ($mergedNames.ContainsKey($ru)) { continue }
  $en = Cell $r 1
  $s = New-Object System.Text.StringBuilder
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('title: "' + $ru + '"')
  if ($en -and $enCounts[$en] -eq 1) { [void]$s.AppendLine('aliases: ["' + $en.Replace('"','') + '"]') }
  [void]$s.AppendLine('description: "Контекстно-зависимый метод: валиден при своих условиях, ошибочен вне их."')
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('')
  [void]$s.AppendLine('**' + (Cell $r 0) + '** · [[05 Контекстные методы|Контекстно-зависимые методы (Тип 5)]]')
  if ($en) { [void]$s.AppendLine(''); [void]$s.AppendLine('*' + $en + '*') }
  [void]$s.AppendLine((K5-Section $r))
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('')
  [void]$s.AppendLine('Каталог: [[Каталог ошибок]] · Концепт: [[Ошибки рассуждения]]')
  [System.IO.File]::WriteAllText((Join-Path (Join-Path $catDir '05 Контекстные методы') ($ru + '.md')), $s.ToString(), $enc)
  $pageCount++
}
Write-Output "fallacy pages: $pageCount"

# ---------- subcategory group pages ----------
$groupCount = 0
foreach ($sub in $subPage.Keys) {
  $g = $subPage[$sub]
  $entries = New-Object System.Collections.Generic.List[object]
  if ($g.TypeKey -eq '5') {
    $k5 | Where-Object { (SubCode (Cell $_ 3)) -eq $g.Code } | Sort-Object { SortKey $_[0] } | ForEach-Object { $entries.Add($_) }
    $typeFolder = '05 Контекстные методы'; $typeTitle = 'Контекстно-зависимые методы (Тип 5)'
  } else {
    $cat | Where-Object { (Cell $_ 3) -eq $g.TypeKey -and (SubCode (NormSub (Cell $_ 4))) -eq $g.Code } | Sort-Object { SortKey $_[0] } | ForEach-Object { $entries.Add($_) }
    $typeFolder = $types[$g.TypeKey].Folder; $typeTitle = $types[$g.TypeKey].Title
  }
  $s = New-Object System.Text.StringBuilder
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('title: "' + $g.Code + ' ' + $g.Label + '"')
  $descLine = if ($clsMap.ContainsKey($g.Code) -and $clsMap[$g.Code].Desc) { DescQ $clsMap[$g.Code].Desc } else { 'Группа ошибок ' + $g.Code + ' — ' + $g.Label }
  [void]$s.AppendLine('description: "' + $descLine + '"')
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('')
  [void]$s.AppendLine('**Группа ' + $g.Code + '** · [[' + $typeFolder + '|' + $typeTitle + ']]')
  [void]$s.AppendLine('')
  $hasCls = $clsMap.ContainsKey($g.Code) -and $clsMap[$g.Code].Desc -and $clsMap[$g.Code].Name -notmatch '^[A-Za-z]'
  if ($hasCls) {
    [void]$s.AppendLine($clsMap[$g.Code].Desc + '.')
    if ($clsMap[$g.Code].Principle) { [void]$s.AppendLine(''); [void]$s.AppendLine('**Принцип:** ' + $clsMap[$g.Code].Principle + '.') }
  } else {
    [void]$s.AppendLine('*Описание группы задаётся в классификаторе таблицы-источника и появится здесь после заполнения.*')
  }
  [void]$s.AppendLine('')
  # Секция на каждый механизм (подтип): книга адресуется именно этому уровню.
  $bySub = @{}; $subOrder = New-Object System.Collections.Generic.List[string]
  foreach ($e in $entries) {
    $stc = if ($g.TypeKey -eq '5') { '' } else { Cell $e 6 }
    if (-not $stc) { $stc = '—' }
    if (-not $bySub.ContainsKey($stc)) { $bySub[$stc] = New-Object System.Collections.Generic.List[object]; $subOrder.Add($stc) }
    $bySub[$stc].Add($e)
  }
  $ordered = New-Object System.Collections.Generic.List[string]
  $subOrder | Sort-Object { SortKey $_ } | ForEach-Object { $ordered.Add($_) }
  $pk = $typeFolder + '/' + $g.PageName + '.md'
  if ($proseBlocks.ContainsKey($pk)) { [void]$s.AppendLine($proseBlocks[$pk]); [void]$s.AppendLine('') }
  [void]$s.AppendLine('Ошибок в группе: **' + $entries.Count + '**, по механизмам нарушения:')
  [void]$s.AppendLine('')
  foreach ($stc in $ordered) {
    $lst = $bySub[$stc]
    $stFull = if ($g.TypeKey -eq '5') { '' } else { Cell $lst[0] 5 }
    $head = if ($stFull) { SubHead $stFull } else { 'Ошибки группы' }
    [void]$s.AppendLine('## ' + $head)
    [void]$s.AppendLine('')
    if ($stc -ne '—' -and $stFull) {
      $sig = if ($stFull -ne $head) { ' · ' + $stFull } else { '' }
      [void]$s.AppendLine('**Механизм ' + $stc + $sig + '** · ошибок: ' + $lst.Count)
      [void]$s.AppendLine('')
    }
    [void]$s.AppendLine('| ID | Ошибка | Формулировка |')
    [void]$s.AppendLine('|---|---|---|')
    foreach ($e in $lst) {
      $ru = San (Cell $e 2)
      $form = Esc (Cell $e 7); if (-not $form) { $form = Esc (Cell $e 5) }
      if ($form.Length -gt 160) { $form = $form.Substring(0,157) + '…' }
      [void]$s.AppendLine('| ' + (Cell $e 0) + ' | [[' + $ru + ']] | ' + $form + ' |')
    }
    [void]$s.AppendLine('')
  }
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('')
  [void]$s.AppendLine('Тип: [[' + $typeFolder + '|' + $typeTitle + ']] · Каталог: [[Каталог ошибок]] · Концепт: [[Ошибки рассуждения]]')
  [System.IO.File]::WriteAllText((Join-Path (Join-Path $catDir $typeFolder) ($g.PageName + '.md')), $s.ToString(), $enc)
  $groupCount++
}
Write-Output "group pages: $groupCount"

# ---------- type indexes ----------
foreach ($catKey in $types.Keys) {
  $tt = $types[$catKey]
  $sel = New-Object System.Collections.Generic.List[object]
  $cat | Where-Object { $_[3] -eq $catKey } | ForEach-Object { $sel.Add($_) }
  $s = New-Object System.Text.StringBuilder
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('title: "' + $tt.Title + '"')
  [void]$s.AppendLine('description: "' + ($tt.Intro -replace '\[\[[^\]|]*\|', '' -replace '\]\]', '' -replace '\[\[', '') + '"')
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('')
  [void]$s.AppendLine($tt.Intro + ' Всего: **' + $sel.Count + '**. Обзор: [[Каталог ошибок]] · Концепт: [[Ошибки рассуждения]].')
  [void]$s.AppendLine('')
  $pk = $tt.Folder + '/index.md'
  if ($proseBlocks.ContainsKey($pk)) { [void]$s.AppendLine($proseBlocks[$pk]); [void]$s.AppendLine('') }
  [void]$s.AppendLine('## Группы')
  [void]$s.AppendLine('')
  [void]$s.AppendLine('| Код | Группа | Ошибок |')
  [void]$s.AppendLine('|---|---|---|')
  $subNames = New-Object System.Collections.Generic.List[object]
  $sel | ForEach-Object { SubCode (NormSub (Cell $_ 4)) } | Select-Object -Unique | Sort-Object { SortKey $_ } | ForEach-Object { $subNames.Add($_) }
  foreach ($sn in $subNames) {
    if (-not $subPage.ContainsKey($sn)) { continue }
    $g = $subPage[$sn]
    $cnt = @($sel | Where-Object { (SubCode (NormSub (Cell $_ 4))) -eq $sn }).Count
    [void]$s.AppendLine('| ' + $g.Code + ' | [[' + $g.PageName + '\|' + $g.Label + ']] | ' + $cnt + ' |')
  }
  if ($catKey -eq '4 - Синдромы') {
    [void]$s.AppendLine("`n## Где проявляются синдромы`n")
    [void]$s.AppendLine('| Код | Синдром | Домены проявления | Общая причина | Описание |')
    [void]$s.AppendLine('|---|---|---|---|---|')
    foreach ($r in $syn) { [void]$s.AppendLine(('| {0} | {1} | {2} | {3} | {4} |' -f (Esc (Cell $r 0)), (Esc (Cell $r 1)), (Esc (Cell $r 2)), (Esc (Cell $r 4)), (Esc (Cell $r 5)))) }
  }
  [void]$s.AppendLine("`n---`n")
  [void]$s.AppendLine('Каталог: [[Каталог ошибок|обзор]] · Источник: `docs/logical_fallacies_classification.xlsx`')
  [System.IO.File]::WriteAllText((Join-Path (Join-Path $catDir $tt.Folder) 'index.md'), $s.ToString(), $enc)
}
# 05 index
$s5 = New-Object System.Text.StringBuilder
[void]$s5.AppendLine(@"
---
title: "Контекстно-зависимые методы (Тип 5)"
description: "Методы, валидные в одних контекстах и ошибочные в других: задача — не запрет, а различение условий."
---

Методы, валидные при своих условиях и ошибочные вне их; четыре из шести имеют и «ошибочную» запись в доменах (двуликость — суть Типа 5). Всего: **$($k5.Count)**. Обзор: [[Каталог ошибок]] · Концепт: [[Ошибки рассуждения]].
"@)
if ($proseBlocks.ContainsKey('05 Контекстные методы/index.md')) { [void]$s5.AppendLine(''); [void]$s5.AppendLine($proseBlocks['05 Контекстные методы/index.md']) }
[void]$s5.AppendLine(@"

## Группы

| Код | Группа | Методов |
|---|---|---|
"@)
$k5subs = New-Object System.Collections.Generic.List[object]
$k5 | ForEach-Object { SubCode (Cell $_ 3) } | Select-Object -Unique | Sort-Object { SortKey $_ } | ForEach-Object { $k5subs.Add($_) }
foreach ($sn in $k5subs) {
  if (-not $subPage.ContainsKey($sn)) { continue }
  $g = $subPage[$sn]
  $cnt = @($k5 | Where-Object { (SubCode (Cell $_ 3)) -eq $sn }).Count
  [void]$s5.AppendLine('| ' + $g.Code + ' | [[' + $g.PageName + '\|' + $g.Label + ']] | ' + $cnt + ' |')
}
[void]$s5.AppendLine('')
[void]$s5.AppendLine('| Код | Метод |')
[void]$s5.AppendLine('|---|---|')
foreach ($r in ($k5 | Sort-Object { SortKey $_[0] })) {
  [void]$s5.AppendLine('| ' + (Cell $r 0) + ' | [[' + (San (Cell $r 2)) + ']] |')
}
[void]$s5.AppendLine("`n---`n")
[void]$s5.AppendLine('Каталог: [[Каталог ошибок|обзор]] · Источник: `docs/logical_fallacies_classification.xlsx`')
[System.IO.File]::WriteAllText((Join-Path (Join-Path $catDir '05 Контекстные методы') 'index.md'), $s5.ToString(), $enc)
Write-Output "type indexes written"

# ---------- Каталог парадоксов ----------
# ОТВЯЗАНО (2026-07-28, слово автора): страницы парадоксов ведутся РУКАМИ —
# обширная работа по каждому случаю (точная формулировка, исторический блок,
# разбор ошибки); таблица paradoxes--*.tsv больше НЕ источник этих страниц.
# Вернуть генерацию: $regenParadoxes = $true — СОТРЁТ ручную прозу карточек,
# не включать без слова автора.
$regenParadoxes = $false
if ($regenParadoxes) {
$parDir = Join-Path $lib "Направления\Архитектура Рассуждения\Каталог парадоксов"
$parIdxPath = Join-Path $parDir 'index.md'
if (Test-Path $parIdxPath) {
  $m = $proseRx.Match([System.IO.File]::ReadAllText($parIdxPath))
  if ($m.Success) { $proseBlocks['парадоксы/index.md'] = $m.Value }
}
# ПРОЗА-блоки на индексах категорий (папках) — собрать до очистки
Get-ChildItem $parDir -Directory -ErrorAction SilentlyContinue | ForEach-Object {
  $ci = Join-Path $_.FullName 'index.md'
  if (Test-Path $ci) {
    $m = $proseRx.Match([System.IO.File]::ReadAllText($ci))
    if ($m.Success) { $proseBlocks['парадоксы/' + $_.Name + '/index.md'] = $m.Value }
  }
}
if (Test-Path $parDir) {
  Get-ChildItem $parDir -File | Remove-Item -Force -Confirm:$false
  Get-ChildItem $parDir -Directory -ErrorAction SilentlyContinue | Remove-Item -Recurse -Force -Confirm:$false
} else { New-Item -ItemType Directory -Force $parDir | Out-Null }
$groups = @(
  @{ Key = 'Структурный'; Page = 'Структурные парадоксы'; Note = 'Конструкция сама смешивает уровни — нарушена вертикаль Закона Порядка ([[Порядок]]): операция берёт себя как объект, элемент выступает собственным правилом. Растворение — вскрыть нарушение иерархии: конструкция не парадоксальна, она не сформирована.'; Dom = $false; Label = 'структурный парадокс' },
  @{ Key = 'Дефектный';   Page = 'Дефектные парадоксы';   Note = 'Конструкция корректна — дефект в посылках: непроя́сненное понятие, скрытое противоречие, ложное допущение или ошибка рассуждения. Колонка «Домен» — адрес изъяна в [[Домены рассуждения|доменах рассуждения]]. Растворение — вскрыть дефект посылки.'; Dom = $true; Label = 'дефектный парадокс' },
  @{ Key = 'Не-парадокс'; Page = 'Не-парадоксы';          Note = 'Результат корректен — отстаёт интуиция. Лечение — поправить интуицию, а результат в лечении и не нуждался.'; Dom = $false; Label = 'не-парадокс' }
)
foreach ($g in $groups) {
  $sel = New-Object System.Collections.Generic.List[object]
  $par | Where-Object { $_[3] -eq $g.Key } | Sort-Object { SortKey $_[0] } | ForEach-Object { $sel.Add($_) }
  # category folder + index (по логике типов Каталога ошибок)
  $gDir = Join-Path $parDir $g.Page
  New-Item -ItemType Directory -Force $gDir | Out-Null
  $s = New-Object System.Text.StringBuilder
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('title: "' + $g.Page + '"')
  [void]$s.AppendLine('description: "' + (DescQ ($g.Note -replace '\[\[[^\]|]*\|', '' -replace '\]\]', '' -replace '\[\[', '')) + '"')
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('')
  [void]$s.AppendLine('**Категория** · [[Каталог парадоксов]]')
  [void]$s.AppendLine('')
  [void]$s.AppendLine($g.Note)
  [void]$s.AppendLine('')
  $pk = 'парадоксы/' + $g.Page + '/index.md'
  if ($proseBlocks.ContainsKey($pk)) { [void]$s.AppendLine($proseBlocks[$pk]); [void]$s.AppendLine('') }
  [void]$s.AppendLine('Всего: **' + $sel.Count + '**, по подтипам изъяна. Концепт: [[Парадокс]]. **Жирным** — центральные разборы.')
  [void]$s.AppendLine('')
  # секция на каждый подтип — тот же уровень, что механизмы у групп ошибок
  $bySub = @{}; $subOrder = New-Object System.Collections.Generic.List[string]
  foreach ($r in $sel) {
    $st = Cell $r 4; if (-not $st) { $st = 'Прочее' }
    if (-not $bySub.ContainsKey($st)) { $bySub[$st] = New-Object System.Collections.Generic.List[object]; $subOrder.Add($st) }
    $bySub[$st].Add($r)
  }
  foreach ($st in $subOrder) {
    $lst = $bySub[$st]
    [void]$s.AppendLine('## ' + $st)
    [void]$s.AppendLine('')
    [void]$s.AppendLine('**Подтип** · парадоксов: ' + $lst.Count)
    [void]$s.AppendLine('')
    if ($g.Dom) { [void]$s.AppendLine('| ID | Парадокс | Домен | Суть ошибки |'); [void]$s.AppendLine('|---|---|---|---|') }
    else { [void]$s.AppendLine('| ID | Парадокс | Суть ошибки |'); [void]$s.AppendLine('|---|---|---|') }
    foreach ($r in $lst) {
      $ru = San (Cell $r 1)
      $link = '[[' + $ru + ']]'
      if ((Cell $r 8) -eq 'Центральный') { $link = '**' + $link + '**' }
      if ($g.Dom) { [void]$s.AppendLine('| ' + (Cell $r 0) + ' | ' + $link + ' | ' + (Esc (Cell $r 5)) + ' | ' + (Esc (Cell $r 6)) + ' |') }
      else { [void]$s.AppendLine('| ' + (Cell $r 0) + ' | ' + $link + ' | ' + (Esc (Cell $r 6)) + ' |') }
    }
    [void]$s.AppendLine('')
  }
  [void]$s.AppendLine('---')
  [void]$s.AppendLine('')
  [void]$s.AppendLine('Каталог: [[Каталог парадоксов]] · Концепт: [[Парадокс]] · Источник: `docs/paradoxes_classification_v4.xlsx`')
  [System.IO.File]::WriteAllText((Join-Path $gDir 'index.md'), $s.ToString(), $enc)
  # entry pages
  foreach ($r in $sel) {
    $ru = San (Cell $r 1)
    $s2 = New-Object System.Text.StringBuilder
    [void]$s2.AppendLine('---')
    [void]$s2.AppendLine('title: "' + $ru + '"')
    $en = Cell $r 2
    if ($en) { [void]$s2.AppendLine('aliases: ["' + $en.Replace('"','') + '"]') }
    [void]$s2.AppendLine('description: "' + (DescQ (Cell $r 6)) + '"')
    [void]$s2.AppendLine('---')
    [void]$s2.AppendLine('')
    $head = '**' + (Cell $r 0) + '** · [[' + $g.Page + '|' + $g.Label + ']] · подтип: ' + (Cell $r 4)
    if ($en) { $head += "`n`n*" + $en + '*' }
    [void]$s2.AppendLine($head)
    [void]$s2.AppendLine('')
    [void]$s2.AppendLine('**Суть ошибки.** ' + (Cell $r 6))
    [void]$s2.AppendLine('')
    if ($g.Dom -and (Cell $r 5) -and (Cell $r 5) -ne '—') { [void]$s2.AppendLine('**Домен изъяна:** ' + (Cell $r 5) + ' ([[Домены рассуждения]]).'); [void]$s2.AppendLine('') }
    if ((Cell $r 8) -eq 'Центральный') { [void]$s2.AppendLine('Развёрнутое растворение — на концепт-странице [[Парадокс]].'); [void]$s2.AppendLine('') }
    elseif ($g.Key -ne 'Не-парадокс') { [void]$s2.AppendLine('Метод растворения: [[Парадокс|доменный анализ]].'); [void]$s2.AppendLine('') }
    [void]$s2.AppendLine('---')
    [void]$s2.AppendLine('')
    [void]$s2.AppendLine('Категория: [[' + $g.Page + ']] · Каталог: [[Каталог парадоксов]] · Концепт: [[Парадокс]]')
    [System.IO.File]::WriteAllText((Join-Path $gDir ($ru + '.md')), $s2.ToString(), $enc)
  }
}
# index
$pi = New-Object System.Text.StringBuilder
[void]$pi.AppendLine(@"
---
title: Каталог парадоксов
aliases: ["Парадокс"]
description: "Парадокс — диагностический сигнал, не тайна: 46 классических случаев по трём категориям, каждый со своей страницей."
деривация: "[[Порядок|Закон Порядка (L5)]], вертикаль → иерархия уровней → парадокс = диагностический сигнал → три категории → 46 случаев, каждый со страницей"
---

**Парадоксы — не глубокие тайны, обнажающие пределы разума, а диагностические сигналы**: они указывают, где нарушена архитектура рассуждения или где посылки несут нераспознанный дефект. Правильно построенное высказывание делает парадокс невозможным — **в реальности парадоксов нет**; потому парадоксы **растворяются, а не решаются**. Прежняя классификация (истинные/псевдо/мнимые) вытеснена структурной: категория называет род ошибки, а не впечатление.
"@)
if ($proseBlocks.ContainsKey('парадоксы/index.md')) { [void]$pi.AppendLine(''); [void]$pi.AppendLine($proseBlocks['парадоксы/index.md']) }
[void]$pi.AppendLine(@"

| Категория | Счёт | Корень |
|---|---|---|
| [[Структурные парадоксы]] | 13 | смешение уровней (вертикаль L5) |
| [[Дефектные парадоксы]] | 25 | изъян в посылках |
| [[Не-парадоксы]] | 8 | корректный результат, отстающая интуиция |

---

Раздел: [[Архитектура Рассуждения]] · Ошибки: [[Каталог ошибок]] · Источник: ``docs/paradoxes_classification_v4.xlsx``
"@)
[System.IO.File]::WriteAllText((Join-Path $parDir 'index.md'), $pi.ToString(), $enc)
Write-Output "paradox: 3 category pages + $($par.Count) entries + index"
} else { Write-Output "paradox: DETACHED - pages are hand-maintained, generation skipped" }

# ---------- дерево классификации: генерируется из данных, инжектится в корневой index ----------
# Лист «Дерево классификации» в xlsx больше НЕ источник (снапшот v2.1 разошёлся с данными);
# дерево строится из листа «Каталог ошибок» и подменяется в index.md между маркерами
# <!-- ДЕРЕВО:НАЧАЛО --> … <!-- ДЕРЕВО:КОНЕЦ --> при каждом прогоне.
$tw = New-Object System.Text.StringBuilder
[void]$tw.AppendLine('## Дерево классификации')
[void]$tw.AppendLine('')
[void]$tw.AppendLine('Пять типов → группы → механизмы нарушения; каждый узел — ссылка. *(Генерируется из листа «Каталог ошибок» скриптом `catalog2md.ps1`.)*')
[void]$tw.AppendLine('')
$typeOrder = @('1 - Условия', '2 - Домены', '3 - Последовательность', '4 - Синдромы')
foreach ($catKey in $typeOrder) {
  $tt = $types[$catKey]
  $sel = @($cat | Where-Object { (Cell $_ 3) -eq $catKey })
  $tname = ($tt.Title -replace '\s*\(Тип \d\)\s*$', '')
  $tnum = $catKey.Substring(0, 1)
  [void]$tw.AppendLine('- **[[' + $tt.Folder + '|Тип ' + $tnum + ' · ' + $tname + ']]** — ' + $sel.Count)
  $gcodes = New-Object System.Collections.Generic.List[string]
  $sel | ForEach-Object { SubCode (NormSub (Cell $_ 4)) } | Select-Object -Unique | Sort-Object { SortKey $_ } | ForEach-Object { $gcodes.Add($_) }
  foreach ($gc in $gcodes) {
    $ge = @($sel | Where-Object { (SubCode (NormSub (Cell $_ 4))) -eq $gc })
    $glabel = if ($subPage.ContainsKey($gc)) { $subPage[$gc].Label } else { $gc }
    $gpage = if ($subPage.ContainsKey($gc)) { $subPage[$gc].PageName } else { '' }
    $glink = if ($gpage) { '[[' + $gpage + '|' + $gc + ' · ' + $glabel + ']]' } else { $gc + ' · ' + $glabel }
    [void]$tw.AppendLine('  - ' + $glink + ' — ' + $ge.Count)
    $mcodes = New-Object System.Collections.Generic.List[string]
    $ge | ForEach-Object { $c6 = Cell $_ 6; if ($c6) { $c6 } else { '—' } } | Select-Object -Unique | Sort-Object { SortKey $_ } | ForEach-Object { $mcodes.Add($_) }
    foreach ($mc in $mcodes) {
      if ($mc -eq '—' -or $mc -eq $gc) { continue }
      $me = @($ge | Where-Object { $c = Cell $_ 6; if (-not $c) { $c = '—' }; $c -eq $mc })
      $mfull = Cell $me[0] 5
      $mlabel = if ($mfull) { SubHead $mfull } else { '' }
      $mtext = if ($mlabel) { $mc + ' · ' + $mlabel } else { $mc }
      $mlink = if ($gpage -and $mlabel) { '[[' + $gpage + '#' + $mlabel + '|' + $mtext + ']]' } else { $mtext }
      [void]$tw.AppendLine('    - ' + $mlink + ' — ' + $me.Count)
    }
  }
}
[void]$tw.AppendLine('- **[[05 Контекстные методы|Тип 5 · Контекстно-зависимые методы]]** — ' + $k5.Count)
$g5codes = New-Object System.Collections.Generic.List[string]
$k5 | ForEach-Object { SubCode (Cell $_ 3) } | Select-Object -Unique | Sort-Object { SortKey $_ } | ForEach-Object { $g5codes.Add($_) }
foreach ($gc in $g5codes) {
  $ge = @($k5 | Where-Object { (SubCode (Cell $_ 3)) -eq $gc })
  $glabel = if ($subPage.ContainsKey($gc)) { $subPage[$gc].Label } else { $gc }
  $gpage = if ($subPage.ContainsKey($gc)) { $subPage[$gc].PageName } else { '' }
  $glink = if ($gpage) { '[[' + $gpage + '|' + $gc + ' · ' + $glabel + ']]' } else { $gc + ' · ' + $glabel }
  [void]$tw.AppendLine('  - ' + $glink + ' — ' + $ge.Count)
  foreach ($m in $ge) {
    $mru = San (Cell $m 2)
    [void]$tw.AppendLine('    - [[' + $mru + '|' + (Cell $m 0) + ' · ' + $mru + ']]')
  }
}

$idxPath = Join-Path $catDir 'index.md'
if (Test-Path $idxPath) {
  $it = [System.IO.File]::ReadAllText($idxPath, $enc)
  if ($it -match '<!-- ДЕРЕВО:НАЧАЛО -->') {
    $block = "<!-- ДЕРЕВО:НАЧАЛО -->`n" + $tw.ToString().TrimEnd() + "`n<!-- ДЕРЕВО:КОНЕЦ -->"
    $it2 = [regex]::Replace($it, '(?s)<!-- ДЕРЕВО:НАЧАЛО -->.*?<!-- ДЕРЕВО:КОНЕЦ -->', $block.Replace('$', '$$'))
    [System.IO.File]::WriteAllText($idxPath, $it2, $enc)
    Write-Output "tree: injected into catalog index"
  } else {
    Write-Output "tree: MARKERS NOT FOUND in catalog index - tree NOT updated"
  }
}
