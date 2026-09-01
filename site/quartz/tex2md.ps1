# tex2md.ps1 — convert book chapter .tex (self-contained or fragment) to Quartz markdown.
# Pilot driver at the bottom converts Часть I (7 chapters + методологическое введение).

$ErrorActionPreference = "Stop"
$enc = New-Object System.Text.UTF8Encoding($false)

# --- balanced-brace command replacer -----------------------------------------
function Convert-Cmd {
  param([string]$text, [string]$cmd, [scriptblock]$fmt)
  $pattern = '\\' + $cmd + '\{(?<c>(?:[^{}]|(?<o>\{)|(?<-o>\}))*(?(o)(?!)))\}'
  $ev = [System.Text.RegularExpressions.MatchEvaluator]{ param($m) & $fmt $m.Groups['c'].Value }
  $prev = $null
  while ($prev -ne $text) { $prev = $text; $text = [regex]::Replace($text, $pattern, $ev) }
  return $text
}

function Convert-Inline {
  param([string]$t)
  # text-style commands (repeat for nesting handled inside Convert-Cmd)
  $t = Convert-Cmd $t 'emph'    { param($c) '*' + $c + '*' }
  $t = Convert-Cmd $t 'textit'  { param($c) '*' + $c + '*' }
  $t = Convert-Cmd $t 'textbf'  { param($c) '**' + $c + '**' }
  $t = Convert-Cmd $t 'texttt'  { param($c) '`' + $c + '`' }
  $t = Convert-Cmd $t 'textsc'  { param($c) $c }
  $t = Convert-Cmd $t 'textrm'  { param($c) $c }
  $t = Convert-Cmd $t 'textnormal' { param($c) $c }
  $t = Convert-Cmd $t 'mbox'    { param($c) $c }
  $t = Convert-Cmd $t 'index'   { param($c) '' }
  # links
  $t = [regex]::Replace($t, '\\href\{([^}]*)\}\{([^}]*)\}', '[$2]($1)')
  $t = [regex]::Replace($t, '\\url\{([^}]*)\}', '<$1>')
  return $t
}

function Convert-MathToPlain {
  # for frontmatter titles / filenames: $A = \exists$ -> A = ∃
  param([string]$t)
  # \texorpdfstring{tex}{plain} -> plain
  $t = [regex]::Replace($t, '\\texorpdfstring\{(?:[^{}]|\{[^{}]*\})*\}\{([^}]*)\}', '$1')
  $t = $t.Replace('~---', ' —').Replace('---', '—').Replace('--', '–').Replace('~', ' ')
  $pairs = @(
    @('\mathbb{Q}','ℚ'), @('\mathbb{R}','ℝ'), @('\mathbb{N}','ℕ'), @('\mathbb{Z}','ℤ'), @('\mathbb{C}','ℂ'),
    @('\exists','∃'), @('\rightarrow','→'), @('\subseteq','⊆'), @('\circ','∘'), @('\infty','∞'),
    @('\times','×'), @('\cdot','·'), @('\neg','¬'), @('\wedge','∧'), @('\vee','∨'), @('\sqrt{2}','√2'),
    @('\RR','ℝ'), @('\QQ','ℚ'), @('\NN','ℕ'), @('\ZZ','ℤ'), @('\CC','ℂ'),
    @('\exp','exp'), @('\eval','eval'), @('\log','log'), @('\to','→'), @('\in','∈')
  )
  foreach ($p in $pairs) { $t = $t.Replace($p[0], $p[1]) }
  $t = [regex]::Replace($t, '\$([^$]*)\$', '$1')
  $t = [regex]::Replace($t, '\\mathbf\{([^}]*)\}', '$1')
  $t = [regex]::Replace($t, '\\mathrm\{([^}]*)\}', '$1')
  $t = [regex]::Replace($t, '\\[a-zA-Z]+', '')
  return ($t -replace '[{}]', '').Trim()
}

function Convert-Tabular {
  param([string]$body)
  $body = $body -replace '\\(toprule|midrule|bottomrule|hline)', ''
  $body = [regex]::Replace($body, '\\cmidrule(\([^)]*\))?\{[^}]*\}', '')
  $body = [regex]::Replace($body, '\\multicolumn\{\d+\}\{[^}]*\}\{([^}]*)\}', '$1')
  $body = $body -replace '\\\\\[[^\]]*\]', '\\'
  $rows = $body -split '\\\\'
  $out = New-Object System.Collections.Generic.List[string]
  $first = $true
  foreach ($r in $rows) {
    $cells = $r -split '(?<!\\)&' | ForEach-Object { $_.Trim() -replace '\r?\n', ' ' }
    if (($cells -join '').Trim() -eq '') { continue }
    $out.Add('| ' + ($cells -join ' | ') + ' |')
    if ($first) { $out.Add('|' + (('@@SEP@@|' * $cells.Count))); $first = $false }
  }
  return "`n" + ($out -join "`n") + "`n"
}

function Convert-TexToMd {
  param([string]$texPath, [string]$titlePrefix)

  $t = [System.IO.File]::ReadAllText($texPath, $enc)
  $t = $t -replace "`r`n", "`n"

  # body extraction
  $mDoc = [regex]::Match($t, '(?s)\\begin\{document\}(.*?)\\end\{document\}')
  if ($mDoc.Success) { $t = $mDoc.Groups[1].Value }

  # chapter title
  $chTitle = ''
  $mCh = [regex]::Match($t, '\\chapter\*?\{(?<c>(?:[^{}]|(?<o>\{)|(?<-o>\}))*(?(o)(?!)))\}')
  if ($mCh.Success) { $chTitle = $mCh.Groups['c'].Value; $t = $t.Remove($mCh.Index, $mCh.Length) }

  # protect listings
  $listings = New-Object System.Collections.Generic.List[string]
  $evLst = [System.Text.RegularExpressions.MatchEvaluator]{
    param($m); $script:listings.Add($m.Groups[1].Value.Trim("`n")); '@@LST' + ($script:listings.Count - 1) + '@@'
  }
  $script:listings = $listings
  $t = [regex]::Replace($t, '(?s)\\begin\{lstlisting\}(?:\[[^\]]*\])?\n?(.*?)\\end\{lstlisting\}', $evLst)

  # strip comments
  $t = [regex]::Replace($t, '(?m)^[ \t]*%.*$', '')
  $t = [regex]::Replace($t, '(?m)(?<!\\)%[^\n]*$', '')

  # label map (label -> nearest preceding section-like title), then refs
  $labelMap = @{}
  $headPattern = '\\(section|subsection|subsubsection|paragraph)\*?\{(?<c>(?:[^{}]|(?<o>\{)|(?<-o>\}))*(?(o)(?!)))\}'
  $heads = [regex]::Matches($t, $headPattern)
  foreach ($lm in [regex]::Matches($t, '\\label\{([^}]*)\}')) {
    $lbl = $lm.Groups[1].Value; $title = $chTitle
    foreach ($h in $heads) { if ($h.Index -lt $lm.Index) { $title = $h.Groups['c'].Value } else { break } }
    $labelMap[$lbl] = $title
  }
  $t = [regex]::Replace($t, '\\label\{[^}]*\}', '')
  $evRef = [System.Text.RegularExpressions.MatchEvaluator]{
    param($m); $lbl = $m.Groups[1].Value
    if ($script:labelMap.ContainsKey($lbl)) { '«' + (Convert-MathToPlain $script:labelMap[$lbl]) + '»' } else { '(см. соответствующую главу)' }
  }
  $script:labelMap = $labelMap
  $t = [regex]::Replace($t, '(?:§~?)?\\(?:auto|v|page|eq)?ref\{([^}]*)\}', $evRef)

  # macros
  $t = [regex]::Replace($t, '\\us(\{\})?\s*', '_')
  $t = $t -replace '\\Rocq(\{\})?', 'Rocq' -replace '\\CIC(\{\})?', 'CIC' -replace '\\ToS(\{\})?', 'ToS' -replace '\\ZFC(\{\})?', 'ZFC'
  $t = [regex]::Replace($t, '\\motiv\{[^}]*\}', '')
  # unicode/plain forms — valid both in prose and inside KaTeX math
  $t = $t -replace '\\QQ(\{\})?', 'ℚ' -replace '\\RR(\{\})?', 'ℝ' -replace '\\NN(\{\})?', 'ℕ' -replace '\\ZZ(\{\})?', 'ℤ' -replace '\\CC(\{\})?', 'ℂ'
  $t = $t -replace '\\Prop(\{\})?', 'Prop'
  foreach ($i in 1..5) { $t = $t -replace ('\\L' + @('one','two','three','four','five')[$i-1] + '(\{\})?'), ('L' + $i) }
  foreach ($i in 1..4) { $t = $t -replace ('\\P' + @('one','two','three','four')[$i-1] + '(\{\})?'), ('P' + $i) }
  $t = Convert-Cmd $t 'texorpdfstring' { param($c) $c }
  $t = $t.Replace('\textasciitilde', '~~TILDE~~').Replace('\textbackslash', '~~BSLASH~~')
  $t = $t -replace '\\(sloppy|addlinespace|itshape|footnotesize|scriptsize|normalsize|allowbreak|raggedright|arraybackslash|small|large)\b', ''
  $t = [regex]::Replace($t, '\\emergencystretch\s*=\s*\S+', '')
  $t = [regex]::Replace($t, '\\linebreak(\[\d\])?', ' ')
  $t = Convert-Cmd $t 'parbox\{[^}]*\}' { param($c) $c }
  $t = Convert-Cmd $t 'fbox' { param($c) "`n> " + (($c.Trim() -split "`n" | ForEach-Object { $_.Trim() }) -join "`n> ") + "`n" }
  $t = [regex]::Replace($t, '\\part\*?\{[^}]*\}', '')
  $t = Convert-Cmd $t 'textsuperscript' { param($c) '<sup>' + $c + '</sup>' }
  $t = [regex]::Replace($t, '\\S(?![a-zA-Z])', '§')
  $t = [regex]::Replace($t, '(?s)\\begin\{minipage\}\{[^}]*\}', '')
  $t = $t -replace '\\end\{minipage\}', ''

  # footnotes -> markers (after macros/refs so bodies are already processed)
  $foots = New-Object System.Collections.Generic.List[string]
  $fnPattern = '\\footnote\{(?<c>(?:[^{}]|(?<o>\{)|(?<-o>\}))*(?(o)(?!)))\}'
  while ($true) {
    $m = [regex]::Match($t, $fnPattern)
    if (-not $m.Success) { break }
    $foots.Add($m.Groups['c'].Value)
    $t = $t.Remove($m.Index, $m.Length).Insert($m.Index, '[^' + $foots.Count + ']')
  }

  # structure
  $t = Convert-Cmd $t 'section\*?'       { param($c) "`n## " + $c + "`n" }
  $t = Convert-Cmd $t 'subsection\*?'    { param($c) "`n### " + $c + "`n" }
  $t = Convert-Cmd $t 'subsubsection\*?' { param($c) "`n#### " + $c + "`n" }
  $t = Convert-Cmd $t 'paragraph\*?'     { param($c) "`n**" + $c + "** " }

  # environments
  $t = [regex]::Replace($t, '\\begin\{(center|small|flushleft|flushright|sloppypar)\}', '')
  $t = [regex]::Replace($t, '\\end\{(center|small|flushleft|flushright|sloppypar)\}', '')
  # amsthm-style blocks -> bold lead-ins
  $thm = @{ 'proposition'='Утверждение'; 'theorem'='Теорема'; 'lemma'='Лемма'; 'definition'='Определение';
            'remark'='Замечание'; 'example'='Пример'; 'corollary'='Следствие' }
  foreach ($k in $thm.Keys) {
    $t = [regex]::Replace($t, ('\\begin\{' + $k + '\}(\[[^\]]*\])?'), ("`n**" + $thm[$k] + '.** '))
    $t = $t -replace ('\\end\{' + $k + '\}'), "`n"
  }
  # lists (innermost-first loop)
  $listPat = '(?s)\\begin\{(itemize|enumerate)\}((?:(?!\\begin\{(?:itemize|enumerate)\}).)*?)\\end\{\1\}'
  while ([regex]::IsMatch($t, $listPat)) {
    $t = [regex]::Replace($t, $listPat, [System.Text.RegularExpressions.MatchEvaluator]{
      param($m)
      $kind = $m.Groups[1].Value
      $items = ($m.Groups[2].Value -split '\\item') | Where-Object { $_.Trim() -ne '' }
      $n = 1; $lines = @()
      foreach ($it in $items) {
        $body = ($it.Trim() -replace '\s*\n\s*', ' ')
        if ($kind -eq 'itemize') { $lines += ('- ' + $body) } else { $lines += ("$n. " + $body); $n++ }
      }
      "`n" + ($lines -join "`n") + "`n"
    })
  }
  # quote
  $t = [regex]::Replace($t, '(?s)\\begin\{quote\}(.*?)\\end\{quote\}', [System.Text.RegularExpressions.MatchEvaluator]{
    param($m)
    $inner = $m.Groups[1].Value.Trim()
    "`n" + (($inner -split "`n" | ForEach-Object { '> ' + $_.Trim() }) -join "`n") + "`n"
  })
  # tables (column spec may contain nested braces: p{0.3\textwidth} etc.)
  $t = [regex]::Replace($t, '(?s)\\begin\{tabular\}\{(?:[^{}]|\{[^{}]*\})*\}(.*?)\\end\{tabular\}', [System.Text.RegularExpressions.MatchEvaluator]{
    param($m); Convert-Tabular $m.Groups[1].Value
  })
  # display math ($$ delimiters on their own lines — required by remark-math)
  $t = [regex]::Replace($t, '(?s)\\begin\{equation\*?\}(.*?)\\end\{equation\*?\}', { param($m) "`n`$`$`n" + $m.Groups[1].Value.Trim() + "`n`$`$`n" })
  $t = [regex]::Replace($t, '(?s)\\begin\{gather\*?\}(.*?)\\end\{gather\*?\}', { param($m) "`n`$`$`n\begin{gathered}`n" + $m.Groups[1].Value.Trim() + "`n\end{gathered}`n`$`$`n" })
  $t = [regex]::Replace($t, '(?s)\\begin\{align\*?\}(.*?)\\end\{align\*?\}', { param($m) "`n`$`$`n\begin{aligned}`n" + $m.Groups[1].Value.Trim() + "`n\end{aligned}`n`$`$`n" })
  $t = [regex]::Replace($t, '(?s)\\\[(.*?)\\\]', { param($m) "`n`$`$`n" + $m.Groups[1].Value.Trim() + "`n`$`$`n" })
  $t = [regex]::Replace($t, '\\\((.*?)\\\)', { param($m) '$' + $m.Groups[1].Value.Trim() + '$' })

  # inline styles + links
  $t = Convert-Inline $t

  # cleanup commands
  $t = [regex]::Replace($t, '\\(addcontentsline|markboth|setcounter|renewcommand|newcommand)\{[^}]*\}(\{[^}]*\})*', '')
  $t = [regex]::Replace($t, '\\(noindent|bigskip|medskip|smallskip|newpage|clearpage|tableofcontents|centering|par)\b', '')
  $t = [regex]::Replace($t, '\\(vspace|hspace)\*?\{[^}]*\}', '')

  # typography (outside math this is right; inside math these sequences are rare)
  $t = $t.Replace('~---', ' —').Replace('---', '—').Replace('--', '–')
  $t = [regex]::Replace($t, '(?<!\\)~', ' ')
  $t = $t.Replace('``', '«').Replace("''", '»')
  $t = $t -replace '\\(dots|ldots)\b', '…'
  $t = $t.Replace('\%', '%').Replace('\&', '&').Replace('\_', '_').Replace('\#', '#')
  $t = $t.Replace('~~TILDE~~', '~').Replace('~~BSLASH~~', '\').Replace('@@SEP@@', '---')

  # footnote bodies
  if ($foots.Count -gt 0) {
    $t += "`n`n---`n"
    for ($i = 0; $i -lt $foots.Count; $i++) {
      $fb = Convert-Inline $foots[$i]
      $fb = $fb.Replace('~---', ' —').Replace('---', '—').Replace('--', '–')
      $fb = $fb.Replace('\_', '_').Replace('\%', '%').Replace('\&', '&').Replace('\#', '#')
      $fb = [regex]::Replace($fb, '(?<!\\)~', ' ')
      $fb = ($fb -replace '\s*\n\s*', ' ').Trim()
      $t += "`n[^" + ($i+1) + "]: " + $fb
    }
  }

  # collapse blanks, restore listings
  $t = [regex]::Replace($t, "`n{3,}", "`n`n")
  for ($i = 0; $i -lt $listings.Count; $i++) {
    $t = $t.Replace('@@LST' + $i + '@@', "``````coq`n" + $listings[$i] + "`n``````")
  }

  return @{ Title = $chTitle; Body = $t.Trim() }
}

# --- pilot driver: Часть I ----------------------------------------------------
$bookPart = "C:\Users\abary\OneDrive\Desktop\theory-of-systems-coq\Книги\Математика\Часть I"
$sitePart = "C:\Users\abary\quartz-put-mudrosti\content\Библиотека\Том Математика\01 Перво-различие и законы логики"
$tomRoot  = "C:\Users\abary\quartz-put-mudrosti\content\Библиотека\Том Математика"
New-Item -ItemType Directory -Force $sitePart | Out-Null

$partTitle = "Часть I. Перво-различие и законы логики"
$chFiles = @(
  @{ N = 1; F = "Глава 1\chapter-01-full.tex" },
  @{ N = 2; F = "Глава 2\chapter-02-full.tex" },
  @{ N = 3; F = "Глава 3\chapter-03-full.tex" },
  @{ N = 4; F = "Глава 4\chapter-4-erro.tex" },
  @{ N = 5; F = "Глава 5\chapter-05-full.tex" },
  @{ N = 6; F = "Глава 6\chapter-06-full.tex" },
  @{ N = 7; F = "Глава 7\chapter-07-full.tex" }
)

$chapterLinks = @()
foreach ($ch in $chFiles) {
  $res = Convert-TexToMd -texPath (Join-Path $bookPart $ch.F)
  $plainTitle = Convert-MathToPlain $res.Title
  $fname = ("{0:d2} {1}" -f $ch.N, ($plainTitle -replace '[\\/:*?"<>|]', '')).Trim()
  $md = "---`n" +
        ("title: `"Глава {0}. {1}`"`n" -f $ch.N, $plainTitle) +
        "---`n`n" + $res.Body + "`n`n---`n`n" +
        ("Часть: [[01 Перво-различие и законы логики|{0}]] · Том: [[Том Математика|«Математика»]]`n" -f $partTitle)
  [System.IO.File]::WriteAllText((Join-Path $sitePart "$fname.md"), $md, $enc)
  $chapterLinks += ("{0}. [[{1}|Глава {0}. {2}]]" -f $ch.N, $fname, $plainTitle)
  Write-Output ("ch {0}: {1} ({2} KB md)" -f $ch.N, $plainTitle, [math]::Round($md.Length/1kb))
}

# методологическое введение -> том root
$intro = Convert-TexToMd -texPath (Join-Path $bookPart "Глава 1\methodological-introduction.tex")
$mdIntro = "---`ntitle: Методологическое введение`n---`n`n" + $intro.Body + "`n`n---`n`nТом: [[Том Математика|«Математика»]]`n"
[System.IO.File]::WriteAllText((Join-Path $tomRoot "00 Методологическое введение.md"), $mdIntro, $enc)
Write-Output ("intro: {0} KB md" -f [math]::Round($mdIntro.Length/1kb))

# part index.md (replaces flat part page)
$oldFlat = Join-Path $tomRoot "01 Перво-различие и законы логики.md"
$desc = "Исходная точка тома: акт бытия, первое различие и вывод законов логики из него; онтология системы — Элементы, Роли, Правила."
$idx = "---`n" +
       "title: `"$partTitle`"`n" +
       "description: `"$desc`"`n" +
       "---`n`n" + $desc + "`n`n**Главы:**`n`n" + ($chapterLinks -join "`n") + "`n`n---`n`n" +
       "Том: [[Том Математика|«Математика»]] · Направление: [[Математика]]`n"
if (Test-Path $oldFlat) { Remove-Item $oldFlat -Force -Confirm:$false }
[System.IO.File]::WriteAllText((Join-Path $sitePart "index.md"), $idx, $enc)
Write-Output "part index written; flat page removed"

# leftover-command report
$left = @{}
Get-ChildItem $sitePart -Filter *.md | ForEach-Object {
  $c = [System.IO.File]::ReadAllText($_.FullName, $enc)
  $c = [regex]::Replace($c, '(?s)```.*?```', '')
  $c = [regex]::Replace($c, '\$\$?[^$]*\$\$?', '')
  foreach ($m in [regex]::Matches($c, '\\[a-zA-Z]+')) { $left[$m.Value]++ }
}
"=== leftover commands outside math/code ==="
$left.GetEnumerator() | Sort-Object Value -Descending | Select-Object -First 15 | ForEach-Object { "{0}: {1}" -f $_.Key, $_.Value }
