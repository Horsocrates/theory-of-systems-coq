# tom_concepts.ps1 — post-pass: add «Понятия: [[...]]» footer line to tom chapters
# based on keyword detection. Idempotent: re-running replaces the line.
$ErrorActionPreference = "Stop"
$enc = New-Object System.Text.UTF8Encoding($false)
$tom = "C:\Users\abary\quartz-put-mudrosti\content\Библиотека\Том Математика"

$rules = @(
  @{ Term = 'Порядок';            Pattern = 'Закон[а-я]* Порядка|Принцип[а-я]* Иерархии|Принцип[а-я]* Последовательности'; Min = 1 },
  @{ Term = 'Парадокс';           Pattern = '[Пп]арадокс'; Min = 2 },
  @{ Term = 'Логика';             Pattern = '[Зз]акон(ы|ов|ам)? логики'; Min = 1 },
  @{ Term = 'Формализация';       Pattern = 'Rocq'; Min = 2 },
  @{ Term = 'Домены рассуждения'; Pattern = '[Дд]омен(ы|ов|ах|а)? рассуждени'; Min = 1 }
)

$stats = @{}
$touched = 0
Get-ChildItem $tom -Directory | ForEach-Object {
  Get-ChildItem $_.FullName -File -Filter *.md | Where-Object { $_.Name -ne 'index.md' } | ForEach-Object {
    $f = $_.FullName
    $t = [System.IO.File]::ReadAllText($f, $enc)
    $plain = [regex]::Replace($t, '(?s)```.*?```', '')
    $plain = [regex]::Replace($plain, '(?s)\$\$.*?\$\$', '')
    $terms = @()
    foreach ($r in $rules) {
      if (([regex]::Matches($plain, $r.Pattern)).Count -ge $r.Min) { $terms += $r.Term; $stats[$r.Term]++ }
    }
    # remove existing line (idempotency)
    $t = [regex]::Replace($t, "(?m)^Понятия: .*`n?", '')
    if ($terms.Count -gt 0) {
      $line = 'Понятия: ' + (($terms | ForEach-Object { '[[' + $_ + ']]' }) -join ' · ')
      # insert after the «Часть: ...» nav line
      $t = [regex]::Replace($t, '(?m)^(Часть: \[\[.*)$', ('$1' + "`n`n" + $line))
      $touched++
    }
    [System.IO.File]::WriteAllText($f, $t, $enc)
  }
}
Write-Output "chapters with concept links: $touched"
$stats.GetEnumerator() | Sort-Object Value -Descending | ForEach-Object { "{0}: {1}" -f $_.Key, $_.Value }
