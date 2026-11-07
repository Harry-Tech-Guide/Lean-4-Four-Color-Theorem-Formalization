param(
    [Parameter(Mandatory=$true, ValueFromRemainingArguments=$true)]
    [string[]]$Targets
)

$ErrorActionPreference = "Stop"

# Throttle priority to BelowNormal and restrict affinity to 2 logical cores (0x03)
# so 6 of 8 logical cores and >7 GB RAM remain 100% free for the user's UI/mouse.
$curProc = [System.Diagnostics.Process]::GetCurrentProcess()
$curProc.PriorityClass = [System.Diagnostics.ProcessPriorityClass]::BelowNormal
$curProc.ProcessorAffinity = [IntPtr]0x03

Set-Location "c:\Four Color Theorem"

foreach ($t in $Targets) {
    Write-Host "[build_safe] Building $t (1 thread, 4096 MB cap, BelowNormal priority)..."
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    & lake build $t
    if ($LASTEXITCODE -ne 0) {
        throw "lake build $t failed with exit code $LASTEXITCODE"
    }
    $sw.Stop()
    Write-Host ("[build_safe] Completed {0} in {1:N1}s" -f $t, $sw.Elapsed.TotalSeconds)
}
