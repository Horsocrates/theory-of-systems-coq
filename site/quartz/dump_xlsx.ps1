# dump_xlsx.ps1 — dump each sheet of the two classification tables to UTF-8 CSV (tab-separated)
$ErrorActionPreference = "Stop"
$docs = "C:\Users\abary\OneDrive\Desktop\theory-of-systems-coq\docs"
$outDir = Join-Path $PSScriptRoot "tables"
New-Item -ItemType Directory -Force $outDir | Out-Null
$enc = New-Object System.Text.UTF8Encoding($false)

$files = @("paradoxes_classification_v4.xlsx", "logical_fallacies_classification (3).xlsx")
$xl = New-Object -ComObject Excel.Application
$xl.Visible = $false
$xl.DisplayAlerts = $false
try {
  foreach ($f in $files) {
    $wb = $xl.Workbooks.Open((Join-Path $docs $f), 0, $true)
    $tag = if ($f -match 'paradox') { 'paradoxes' } else { 'fallacies' }
    foreach ($ws in $wb.Worksheets) {
      $ur = $ws.UsedRange
      $rows = $ur.Rows.Count; $cols = $ur.Columns.Count
      $sb = New-Object System.Text.StringBuilder
      $data = $ur.Value2
      for ($r = 1; $r -le $rows; $r++) {
        $line = @()
        for ($c = 1; $c -le $cols; $c++) {
          $v = if ($rows -eq 1 -and $cols -eq 1) { $data } else { $data[$r, $c] }
          $s = if ($null -eq $v) { '' } else { [string]$v }
          $line += ($s -replace "[`t`r`n]+", ' ')
        }
        [void]$sb.AppendLine($line -join "`t")
      }
      $safe = $ws.Name -replace '[\\/:*?"<>|]', '_'
      [System.IO.File]::WriteAllText((Join-Path $outDir "$tag--$safe.tsv"), $sb.ToString(), $enc)
      Write-Output ("{0} :: sheet '{1}': {2} rows x {3} cols" -f $tag, $ws.Name, $rows, $cols)
      [void][System.Runtime.InteropServices.Marshal]::ReleaseComObject($ur)
      [void][System.Runtime.InteropServices.Marshal]::ReleaseComObject($ws)
    }
    $wb.Close($false)
    [void][System.Runtime.InteropServices.Marshal]::ReleaseComObject($wb)
  }
}
finally {
  $xl.Quit()
  [void][System.Runtime.InteropServices.Marshal]::ReleaseComObject($xl)
  [GC]::Collect(); [GC]::WaitForPendingFinalizers()
}
