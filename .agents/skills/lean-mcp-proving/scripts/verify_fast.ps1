$ErrorActionPreference = "Stop"
Set-Location "c:\Four Color Theorem"

Write-Host "=== [1/3] Checking for 'sorry' across FourColorTheorem/Math ===" -ForegroundColor Cyan
$sorries = Select-String -Path "FourColorTheorem\Math\*.lean", "FourColorTheorem\Math\Soundness\*.lean", "FourColorTheorem\Math\CheckerSoundness\*.lean", "FourColorTheorem\Math\Topology\*.lean", "FourColorTheorem\Math\KernelSoundness\*.lean", "FourColorTheorem\Math\Unavoidability\*.lean" -Pattern "\bsorry\b" |
    Where-Object { $_.Line -notmatch "^\s*--" }

if ($sorries) {
    Write-Host "ERROR: Found 'sorry' occurrences:" -ForegroundColor Red
    $sorries | ForEach-Object { Write-Host "  $($_.Path):$($_.LineNumber): $($_.Line.Trim())" -ForegroundColor Red }
    exit 1
}
Write-Host "  0 sorry found." -ForegroundColor Green

Write-Host "=== [2/3] Building Core Math & Soundness Targets ===" -ForegroundColor Cyan
lake build `
    FourColorTheorem.Math.Soundness.ExtendSoundness `
    FourColorTheorem.Math.Soundness.Representation `
    FourColorTheorem.Math.Soundness.DReduce `
    FourColorTheorem.Math.Soundness.CReduce `
    FourColorTheorem.Math.Soundness.ContractSoundness `
    FourColorTheorem.Math.Soundness.StructuralVerification `
    FourColorTheorem.Math.CheckerSoundness.MatchingExtraction `
    FourColorTheorem.Math.CheckerSoundness.BuildSMDataSoundness `
    FourColorTheorem.Math.CheckerSoundness.InitialLiveProof `
    FourColorTheorem.Math.CheckerSoundness.IterationElimination `
    FourColorTheorem.Math.Topology.SubtypeSurgery `
    FourColorTheorem.Math.Unavoidability.CheckIsoSoundness `
    FourColorTheorem.Math.Unavoidability.FreeCompletionProjection `
    FourColorTheorem.Math.Unavoidability `
    FourColorTheorem.Math.MasterCertificate `
    FourColorTheorem.Math.MainTheorem

if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: Targeted lake build failed." -ForegroundColor Red
    exit $LASTEXITCODE
}

Write-Host "=== [3/3] Auditing Axiom Footprint of Math.four_color_theorem ===" -ForegroundColor Cyan
lake env lean ".agents\skills\lean-mcp-proving\scripts\AxiomCheck.lean"
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: Axiom audit failed." -ForegroundColor Red
    exit $LASTEXITCODE
}
Write-Host "=== Fast Verification Passed! ===" -ForegroundColor Green
