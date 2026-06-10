# check_coqproject.ps1 — reconcile _CoqProject against the .v files on disk.
#
# WHY THIS EXISTS (June 2026 forensics): _CoqProject is a shared lost-update
# hotspot. Parallel sessions + OneDrive sync repeatedly committed the file
# from a STALE base, silently deleting other sessions' fresh registrations
# (commits 20712aa and e2c0cd9 each wiped the src/nonstandard block: +8/-13
# and +9/-14 line diffs). There is NO regenerator script — the old guess
# "regeneration had dropped them" (4b3478d) was wrong; it was a write race.
#
# Usage:  powershell -File tools/check_coqproject.ps1
# Exit 0 = registry exactly matches disk. Exit 1 = mismatch (printed).
# Run this BEFORE every commit that touches .v files or _CoqProject.

$ErrorActionPreference = 'Stop'
$root = Split-Path $PSScriptRoot -Parent
Set-Location $root

# Deliberate exclusions: junk / scratch files that must NOT be in the build.
$excludePatterns = @('(^|/)_scratch_', '(^|/)TestNode\.v$')

function Is-Excluded($path) {
  foreach ($p in $excludePatterns) { if ($path -match $p) { return $true } }
  return $false
}

$entriesRaw = Get-Content "_CoqProject" | Where-Object { $_ -match '\.v\s*$' } |
  ForEach-Object { ($_.Trim()) -replace '\\','/' }

$fail = $false

# 1. duplicates inside the registry
$dupes = $entriesRaw | Group-Object | Where-Object { $_.Count -gt 1 }
if ($dupes.Count -gt 0) {
  $fail = $true
  Write-Host ("DUPLICATE entries in _CoqProject: " + $dupes.Count)
  $dupes | ForEach-Object { Write-Host ("  dup: " + $_.Name) }
}

$reg = @{}
foreach ($e in $entriesRaw) { $reg[$e] = $true }

$prefix = (Get-Location).Path.Length + 1
$disk = Get-ChildItem -Recurse -Filter *.v -Path src, Architecture_of_Reasoning |
  ForEach-Object { ($_.FullName.Substring($prefix)) -replace '\\','/' } |
  Where-Object { -not (Is-Excluded $_) }

# 2. on disk but not registered (the lost-update symptom)
$missing = $disk | Where-Object { -not $reg.ContainsKey($_) } | Sort-Object
if ($missing.Count -gt 0) {
  $fail = $true
  Write-Host ("MISSING from _CoqProject (on disk, not in build): " + $missing.Count)
  $missing | ForEach-Object { Write-Host ("  missing: " + $_) }
}

# 3. registered but absent on disk
$diskSet = @{}
foreach ($d in $disk) { $diskSet[$d] = $true }
$ghost = $entriesRaw | Sort-Object -Unique |
  Where-Object { (-not $diskSet.ContainsKey($_)) -and (-not (Is-Excluded $_)) }
if ($ghost.Count -gt 0) {
  $fail = $true
  Write-Host ("GHOST entries in _CoqProject (no such file on disk): " + $ghost.Count)
  $ghost | ForEach-Object { Write-Host ("  ghost: " + $_) }
}

if ($fail) {
  Write-Host ""
  Write-Host "MISMATCH. If files were silently dropped by a stale-base write,"
  Write-Host "restore with: powershell -File tools/regen_coqproject.ps1"
  exit 1
}
Write-Host ("OK: _CoqProject matches disk (" + $disk.Count + " .v files, 0 dupes, 0 ghosts).")
exit 0
