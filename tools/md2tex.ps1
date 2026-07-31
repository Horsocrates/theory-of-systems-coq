# md2tex.ps1 - general Markdown -> LaTeX (Tom II stack: T2A/cm-super, babel-russian, listings, booktabs).
# Usage: powershell -File tools/md2tex.ps1 -Src <in.md> -Dst <out.tex>
# ASCII-only source; all Unicode symbols built from codepoints (PowerShell 5.1 reads .ps1 as ANSI).
param([Parameter(Mandatory=$true)][string]$Src, [Parameter(Mandatory=$true)][string]$Dst)
$ErrorActionPreference = 'Stop'
$src  = $Src
$dst  = $Dst
$enc  = New-Object System.Text.UTF8Encoding($false)
$raw  = [System.IO.File]::ReadAllText($src, [System.Text.Encoding]::UTF8)

# remove combining marks + variation selector
$raw = $raw.Replace([string][char]0x0301,'').Replace([string][char]0x0304,'').Replace([string][char]0xFE0F,'')
# strip HTML comment blocks (metadata headers) so they don't render as body text
$raw = [regex]::Replace($raw, '(?s)<!--.*?-->', '')

# prose symbol map as parallel arrays from codepoints (-> LaTeX math/text)
$pairsCp = @(
 0x00A7,'\S{}', 0x00AB,'<<', 0x00BB,'>>', 0x201E,'<<', 0x201C,'>>',
 0x2026,'\ldots{}', 0x2013,'--', 0x2014,'---', 0x2212,'$-$',
 0x00AC,'$\neg$', 0x00B7,'$\cdot$', 0x00D7,'$\times$',
 0x00B2,'\textsuperscript{2}', 0x00B9,'\textsuperscript{1}', 0x207F,'\textsuperscript{n}',
 0x2080,'\textsubscript{0}', 0x2081,'\textsubscript{1}', 0x2084,'\textsubscript{4}',
 0x0394,'$\Delta$', 0x03A0,'$\Pi$', 0x03A3,'$\Sigma$', 0x03B1,'$\alpha$',
 0x03B5,'$\varepsilon$', 0x03BB,'$\lambda$', 0x03C3,'$\sigma$', 0x03C6,'$\varphi$', 0x03C9,'$\omega$',
 0x2115,'$\mathbb{N}$', 0x211A,'$\mathbb{Q}$', 0x211D,'$\mathbb{R}$', 0x2135,'$\aleph$',
 0x1D4AB,'$\mathcal{P}$',
 0x2192,'$\to$', 0x2194,'$\leftrightarrow$', 0x21A6,'$\mapsto$',
 0x2200,'$\forall$', 0x2203,'$\exists$', 0x2205,'$\emptyset$', 0x2208,'$\in$', 0x2209,'$\notin$',
 0x221A,'$\surd$', 0x2227,'$\land$', 0x2228,'$\lor$', 0x2229,'$\cap$', 0x222A,'$\cup$', 0x22C3,'$\bigcup$',
 0x2245,'$\cong$', 0x2260,'$\ne$', 0x2261,'$\equiv$', 0x2264,'$\le$', 0x2265,'$\ge$', 0x2286,'$\subseteq$',
 0x27E8,'$\langle$', 0x27E9,'$\rangle$', 0x27F9,'$\Longrightarrow$', 0x27FA,'$\Longleftrightarrow$',
 0x2605,'$\bigstar$', 0x26A0,'[!]', 0x2705,'[OK]', 0x270D,'[ed.]', 0x1F536,'[~]',
 0x2713,'$\checkmark$', 0x2714,'$\checkmark$', 0x25C7,'$\Diamond$', 0x22A5,'$\perp$', 0x2295,'$\oplus$', 0x22B3,'$\vartriangleright$',
 0x03B2,'$\beta$', 0x03B3,'$\gamma$', 0x03B4,'$\delta$', 0x27F8,'$\Longleftarrow$', 0x2248,'$\approx$',
 0x21D2,'$\Rightarrow$', 0x21D0,'$\Leftarrow$', 0x2194,'$\leftrightarrow$', 0x2032,"'", 0x2033,"''"
)
$symFrom = New-Object System.Collections.ArrayList
$symTo   = New-Object System.Collections.ArrayList
for ($k=0; $k -lt $pairsCp.Count; $k+=2) {
  [void]$symFrom.Add([System.Char]::ConvertFromUtf32([int]$pairsCp[$k]))
  [void]$symTo.Add([string]$pairsCp[$k+1])
}

function Map-Symbols([string]$s) {
  for ($j=0; $j -lt $symFrom.Count; $j++) { $s = $s.Replace($symFrom[$j], $symTo[$j]) }
  return $s
}
function Esc-Prose([string]$s) {
  $s = $s.Replace('\','<<BSL>>')
  $s = $s -replace '([&%#_{}])','\$1'
  $s = $s.Replace('~','\textasciitilde{}').Replace('^','\textasciicircum{}')
  $s = $s.Replace('<<BSL>>','\textbackslash{}')
  return $s
}
function Esc-Code([string]$s) {
  $s = $s.Replace('\','<<BSL>>')
  $s = $s -replace '([&%#_{}$])','\$1'
  $s = $s.Replace('~','\textasciitilde{}').Replace('^','\textasciicircum{}')
  $s = $s.Replace('<<BSL>>','\textbackslash{}')
  # let long code tokens break across lines (no global \sloppy): after _, /, comma
  $s = $s.Replace('\_','\_\allowbreak{}')
  $s = $s.Replace('/','/\allowbreak{}')
  $s = $s.Replace(',',',\allowbreak{}')
  # break long CamelCase identifiers at lowercase->uppercase boundaries
  $s = [regex]::Replace($s, '(?<=[a-z])(?=[A-Z])', '\allowbreak{}')
  $s = Map-Symbols $s
  return $s
}
function MakeFootnote([string]$runText) {
  $parts = [regex]::Matches($runText, '`([^`]*)`')
  $items = @()
  foreach ($mm in $parts) { $items += ('\texttt{' + (Esc-Code $mm.Groups[1].Value) + '}') }
  return '\footnote{' + ($items -join ', ') + '}'
}
function Inline([string]$line) {
  $codes = New-Object System.Collections.ArrayList
  if (-not $script:NoFootnote) {
    # File refs (code spans with .v) only go to a FOOTNOTE when they sit IN PARENTHESES
    # = a supporting citation ("...текст (file.v)"); parens are consumed.
    # A bare/grammatical ref ("в файле X", "доказано в X", enumerations) stays INLINE as \texttt
    # = a concrete reference the sentence needs. (Tables/headers: NoFootnote, all inline.)
    $line = [regex]::Replace($line, '\(\s*(`[^`]*\.v[^`]*`(?:\s*[,;]\s*`[^`]*\.v[^`]*`)*)\s*\)', {
      param($m); $idx = $codes.Add((MakeFootnote $m.Groups[1].Value)); "ZZZCODE${idx}ZZZ" })
  }
  $line = [regex]::Replace($line, '`([^`]*)`', {
    param($m)
    $idx = $codes.Add('\texttt{' + (Esc-Code $m.Groups[1].Value) + '}')
    "ZZZCODE${idx}ZZZ"
  })
  $line = Esc-Prose $line
  $line = [regex]::Replace($line, '\*\*(.+?)\*\*', { param($m) '\textbf{' + $m.Groups[1].Value + '}' })
  $line = [regex]::Replace($line, '(?<!\*)\*([^*]+?)\*', { param($m) '\emph{' + $m.Groups[1].Value + '}' })
  $line = Map-Symbols $line
  for ($z=0; $z -lt $codes.Count; $z++) { $line = $line.Replace("ZZZCODE${z}ZZZ", $codes[$z]) }
  return $line
}
# numbered \section/\subsection for digit-led headings (number stripped, LaTeX re-numbers);
# starred (unnumbered) for non-digit headings (subtitle, appendix).
function Header([string]$txt, [int]$lvl) {
  $m = [regex]::Match($txt, '^\d+(\.\d+)*\.\s+')
  $hasNum = $m.Success
  $clean = if ($hasNum) { $txt.Substring($m.Length) } else { $txt }
  $script:NoFootnote = $true
  $t = Inline $clean
  $script:NoFootnote = $false
  switch ($lvl) {
    1 { return "\begin{center}{\LARGE\bfseries $t}\end{center}`n\vspace{0.5em}" }
    2 { if ($hasNum) { return "\section{$t}" }    else { return "\section*{$t}" } }
    3 { if ($hasNum) { return "\subsection{$t}" } else { return "\subsection*{$t}" } }
    default { if ($hasNum) { return "\subsubsection{$t}" } else { return "\subsubsection*{$t}" } }
  }
}

# --- join soft-wrapped lines into logical lines (so bold/code spans survive wraps) ---
$rawLines = $raw -split "`r?`n"
$lines = New-Object System.Collections.ArrayList
$fence = $false
foreach ($rl in $rawLines) {
  $fl = $rl -replace '^\s*> ?',''
  if ($fl -match '^```') { $fence = -not $fence; [void]$lines.Add($fl); continue }
  if ($fence) { [void]$lines.Add($fl); continue }
  $isB = ($fl.Trim() -eq '') -or ($fl -match '^#') -or ($fl -match '^\s*\|') -or ($fl -match '^---+\s*$') -or ($fl -match '^\s*([-*]|\d+\.)\s')
  if ($lines.Count -eq 0 -or $isB) { [void]$lines.Add($fl); continue }
  $prev = $lines[$lines.Count-1]
  $guard = ($prev -match '^#') -or ($prev.Trim() -eq '') -or ($prev -match '^---+\s*$') -or ($prev -match '^\s*\|')
  if ($guard) { [void]$lines.Add($fl) } else { $lines[$lines.Count-1] = $prev + ' ' + $fl.TrimStart() }
}

$out = New-Object System.Collections.ArrayList
@(
 '% Build: pdflatex -interaction=nonstopmode SHOWCASE.tex  (run x3).',
 '% cmap = ToUnicode (copyable/searchable Cyrillic); paratype = PT Serif/Sans/Mono.',
 '\documentclass[11pt,a4paper]{article}',
 '\usepackage{cmap}',
 '\usepackage[T2A]{fontenc}',
 '\usepackage[utf8]{inputenc}',
 '\usepackage{paratype}',
 '\usepackage[main=russian,english]{babel}',
 '\usepackage[a4paper,top=2.5cm,bottom=2.5cm,left=2.7cm,right=2.7cm]{geometry}',
 '\usepackage{amsmath,amssymb,amsthm}',
 '\usepackage{mathtools}',
 '\usepackage{array}',
 '\usepackage{booktabs}',
 '\usepackage{tabularx}',
 '\usepackage{xcolor}',
 '\usepackage{listings}',
 '\definecolor{lstbg}{rgb}{0.97,0.97,0.97}',
 '\lstset{basicstyle=\ttfamily\small,backgroundcolor=\color{lstbg},frame=single,framerule=0pt,rulecolor=\color{lstbg},numbers=left,numberstyle=\tiny\color{gray},numbersep=8pt,breaklines=true,keepspaces=true,showstringspaces=false,language=ML,',
 '  morekeywords={Theorem,Proof,Qed,Defined,Definition,Lemma,Fixpoint,Record,Inductive,Axiom,Parameter,Variable,forall,exists,Prop,Type,Set,match,with,end,fun,nat,list,bool,classic,L4_witness,intros,exact,destruct,apply,reflexivity,induction,lia,split,intro,Section,End}}',
 '\usepackage{hyperref}',
 '\hypersetup{colorlinks=true,linkcolor=black,citecolor=black,urlcolor=black}',
 '\usepackage{xspace}',
 '\newcommand{\Rocq}{\textsc{Rocq}\xspace}',
 '\newcommand{\CIC}{\textsc{CIC}\xspace}',
 '\newcommand{\ToS}{\textsc{ToS}\xspace}',
 '\newcommand{\NN}{\ensuremath{\mathbb{N}}}',
 '\newcommand{\QQ}{\ensuremath{\mathbb{Q}}}',
 '\newcommand{\ZZ}{\ensuremath{\mathbb{Z}}}',
 '\newcommand{\RR}{\ensuremath{\mathbb{R}}}',
 '\newcommand{\CC}{\ensuremath{\mathbb{C}}}',
 '\providecommand{\Prop}{\ensuremath{\mathrm{Prop}}}',
 '\setlength{\parindent}{1.2em}',
 '\setlength{\parskip}{0pt}',
 '\tolerance=1500',
 '\emergencystretch=3em',
 '\begin{document}'
) | ForEach-Object { [void]$out.Add($_) }

$inCode = $false
$script:NoFootnote = $false
$listStack = New-Object System.Collections.ArrayList
function Close-Lists {
  while ($listStack.Count -gt 0) {
    $env = $listStack[$listStack.Count-1]
    [void]$out.Add("\end{$env}")
    $listStack.RemoveAt($listStack.Count-1)
  }
}

$i = 0
while ($i -lt $lines.Count) {
  $ln = $lines[$i]
  $stripped = $ln -replace '^\s*> ?', ''
  if ($stripped -match '^```') {
    if (-not $inCode) { Close-Lists; $inCode=$true; [void]$out.Add('\begin{lstlisting}') }
    else { $inCode=$false; [void]$out.Add('\end{lstlisting}') }
    $i++; continue
  }
  if ($inCode) { [void]$out.Add($stripped); $i++; continue }
  if ($stripped.Trim() -eq '') { Close-Lists; [void]$out.Add(''); $i++; continue }
  if ($stripped -match '^---+\s*$') { Close-Lists; [void]$out.Add('\bigskip\hrule\bigskip'); $i++; continue }
  if ($stripped -match '^(#{1,6})\s+(.*)$') { Close-Lists; [void]$out.Add((Header $Matches[2] $Matches[1].Length)); $i++; continue }
  if ($stripped -match '^\s*\|') {
    Close-Lists
    $script:NoFootnote = $true
    $tbl = New-Object System.Collections.ArrayList
    while ($i -lt $lines.Count) {
      $s2 = $lines[$i] -replace '^\s*> ?',''
      if ($s2 -notmatch '^\s*\|') { break }
      [void]$tbl.Add($s2.Trim()); $i++
    }
    $cells = ($tbl[0].Trim('|') -split '\|')
    $ncol = $cells.Count
    $colspec = '|' + (('X|') * $ncol)
    $fs = if ($ncol -ge 4) { '\scriptsize' } else { '\footnotesize' }
    [void]$out.Add("{$fs\setlength{\tabcolsep}{4pt}\renewcommand{\arraystretch}{1.2}\begin{tabularx}{\linewidth}{$colspec}")
    [void]$out.Add('\hline')
    $hc = ($cells | ForEach-Object { '\textbf{' + (Inline $_.Trim()) + '}' }) -join ' & '
    [void]$out.Add("$hc \\ \hline")
    for ($r=2; $r -lt $tbl.Count; $r++) {
      $rc = ($tbl[$r].Trim('|') -split '\|')
      $vals = @()
      for ($c=0; $c -lt $ncol; $c++) { if ($c -lt $rc.Count) { $vals += (Inline $rc[$c].Trim()) } else { $vals += '' } }
      [void]$out.Add(($vals -join ' & ') + ' \\ \hline')
    }
    [void]$out.Add('\end{tabularx}}')
    $script:NoFootnote = $false
    continue
  }
  if ($stripped -match '^(\s*)([-*]|\d+\.)\s+(.*)$') {
    $indent = $Matches[1].Length
    $want = if ($Matches[2] -match '\d') { 'enumerate' } else { 'itemize' }
    $depth = [math]::Floor($indent / 2) + 1
    while ($listStack.Count -lt $depth) { [void]$out.Add("\begin{$want}"); [void]$listStack.Add($want) }
    while ($listStack.Count -gt $depth) { $env=$listStack[$listStack.Count-1]; [void]$out.Add("\end{$env}"); $listStack.RemoveAt($listStack.Count-1) }
    [void]$out.Add('\item ' + (Inline $Matches[3]))
    $i++; continue
  }
  if ($listStack.Count -gt 0 -and $ln -match '^\s+\S') { [void]$out.Add((Inline $stripped)) }
  else { Close-Lists; [void]$out.Add((Inline $stripped)) }
  $i++
}
Close-Lists
if ($inCode) { [void]$out.Add('\end{lstlisting}') }
[void]$out.Add('\end{document}')
[System.IO.File]::WriteAllText($dst, ($out -join "`n"), $enc)
Write-Host ("wrote " + $dst + " (" + $out.Count + " lines)")
