# regen_coqproject.ps1 — deterministically rebuild _CoqProject from disk.
#
# Output = the non-entry header lines of the current _CoqProject (the -Q
# mappings etc., kept verbatim in order) + ALL .v files under src/ and
# Architecture_of_Reasoning/, sorted, deduplicated, forward slashes —
# minus deliberate exclusions (scratch/junk).
#
# Use after a suspected lost-update clobber (see tools/check_coqproject.ps1).
# The output is deterministic, so reruns are idempotent and diffs reviewable.

$ErrorActionPreference = 'Stop'
$root = Split-Path $PSScriptRoot -Parent
Set-Location $root

$excludePatterns = @('(^|/)_scratch_', '(^|/)TestNode\.v$')
function Is-Excluded($path) {
  foreach ($p in $excludePatterns) { if ($path -match $p) { return $true } }
  return $false
}

$header = Get-Content "_CoqProject" | Where-Object { $_ -notmatch '\.v\s*$' -and $_.Trim() -ne '' }

$prefix = (Get-Location).Path.Length + 1
$disk = Get-ChildItem -Recurse -Filter *.v -Path src, Architecture_of_Reasoning |
  ForEach-Object { ($_.FullName.Substring($prefix)) -replace '\\','/' } |
  Where-Object { -not (Is-Excluded $_) } |
  Sort-Object -Unique

$enc = New-Object System.Text.UTF8Encoding($false)
$content = (($header + $disk) -join "`n") + "`n"
[System.IO.File]::WriteAllText((Join-Path (Get-Location) "_CoqProject"), $content, $enc)
Write-Host ("_CoqProject regenerated: " + $header.Count + " header lines + " + $disk.Count + " entries.")
