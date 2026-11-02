$ErrorActionPreference = "SilentlyContinue"
$inputJson = [Console]::In.ReadToEnd()
if (-not $inputJson) {
    Write-Output '{"decision":"allow"}'
    exit 0
}

try {
    $payload = $inputJson | ConvertFrom-Json
    $cmd = $payload.toolCall.args.CommandLine
    if ($cmd -match "\blake\s+build\b") {
        $runningLake = Get-Process -Name "lake" -ErrorAction SilentlyContinue
        if ($runningLake) {
            $resp = @{
                decision = "deny"
                reason   = "Another 'lake' process is already running (PID: $($runningLake.Id -join ', ')). Never run concurrent lake builds as they corrupt .lake cache. Use lean-lsp MCP tools (lean_goal, lean_diagnostic_messages) or wait for the active build to finish."
            } | ConvertTo-Json -Compress
            Write-Output $resp
            exit 0
        }
    }
} catch {
    # Fallback allow on parse error
}

Write-Output '{"decision":"allow"}'
exit 0
