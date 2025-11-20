# FM Playground - Service Manager (PowerShell)
# Requires PowerShell 5.1 or higher

# Project root directory
$ProjectRoot = $PSScriptRoot

# Error handling
$ErrorActionPreference = "Stop"

# Arrays to store job information
$Global:Jobs = @()
$Global:ServiceNames = @()

# Cleanup function
function Stop-AllServices {
    Write-Host "`nStopping all services..." -ForegroundColor Yellow
    foreach ($job in $Global:Jobs) {
        if ($job -and (Get-Job -Id $job.Id -ErrorAction SilentlyContinue)) {
            Write-Host "Stopping $($job.Name)..." -ForegroundColor Yellow
            Stop-Job -Id $job.Id -PassThru -ErrorAction SilentlyContinue | Out-Null
            Wait-Job -Id $job.Id -Timeout 3 -ErrorAction SilentlyContinue | Out-Null
            Remove-Job -Id $job.Id -Force -ErrorAction SilentlyContinue
        }
    }
    Write-Host "All services stopped." -ForegroundColor Green
}

# Register cleanup on exit
Register-EngineEvent -SourceIdentifier PowerShell.Exiting -Action { Stop-AllServices } | Out-Null

# Trap Ctrl+C using a simpler approach
try {
    $null = Register-EngineEvent -SourceIdentifier ConsoleControl.CancelKeyPress -Action {
        Stop-AllServices
        exit 0
    } -ErrorAction SilentlyContinue
} catch {
    # Fallback - Ctrl+C will be handled by the finally block
}

# Helper functions
function Global:Show-ErrorMsg {
    param([string]$Message)
    Write-Host "ERROR: $Message" -ForegroundColor Red
    exit 1
}

function Global:Show-Success {
    param([string]$Message)
    Write-Host "[OK] $Message" -ForegroundColor Green
}

function Global:Show-Info {
    param([string]$Message)
    Write-Host "[INFO] $Message" -ForegroundColor Cyan
}

function Global:Show-WarningMsg {
    param([string]$Message)
    Write-Host "[WARN] $Message" -ForegroundColor Yellow
}

# Function to check if a port is in use
function Test-Port {
    param(
        [int]$Port,
        [string]$ServiceName
    )
    
    $connection = Get-NetTCPConnection -LocalPort $Port -State Listen -ErrorAction SilentlyContinue
    
    if ($connection) {
        Write-Host "ERROR: `Port $Port is already in use (required for $ServiceName). Please stop the service using this port first." -ForegroundColor Red; exit 1
    }
}

# Function to check if Java is installed and get version
function Test-Java {
    try {
        $javaVersionOutput = & java -version 2>&1
        if ($LASTEXITCODE -ne 0) {
            Write-Host "ERROR: `Java is not installed. Please install Java 17 or higher." -ForegroundColor Red; exit 1
        }
        
        # Parse Java version
        $versionLine = $javaVersionOutput | Select-String -Pattern 'version "(\d+)' | Select-Object -First 1
        if ($versionLine -match 'version "(\d+)') {
            $javaVersion = [int]$matches[1]
        } else {
            Write-Host "ERROR: `Unable to determine Java version." -ForegroundColor Red; exit 1
        }
        
        if ($javaVersion -lt 17) {
            Write-Host "ERROR: `Java version $javaVersion is installed, but version 17 or higher is required." -ForegroundColor Red; exit 1
        }
        
        Write-Host "[OK] Java version $javaVersion detected" -ForegroundColor Green
        return $javaVersion
    } catch {
        Write-Host "ERROR: `Java is not installed. Please install Java 17 or higher." -ForegroundColor Red; exit 1
    }
}

# Function to update build.gradle with Java version
function Update-BuildGradle {
    param([int]$JavaVersion)
    
    $buildFile = Join-Path $ProjectRoot "alloy-api\build.gradle"
    
    if (Test-Path $buildFile) {
        $content = Get-Content $buildFile -Raw
        $content = $content -replace 'languageVersion = JavaLanguageVersion\.of\(\d+\)', "languageVersion = JavaLanguageVersion.of($JavaVersion)"
        Set-Content -Path $buildFile -Value $content -NoNewline
        Write-Host "[OK] Updated build.gradle to use Java $JavaVersion" -ForegroundColor Green
    }
}

# Function to check if Poetry is installed
function Test-Poetry {
    try {
        $null = & poetry --version 2>&1
        if ($LASTEXITCODE -ne 0) {
            Write-Host "ERROR: `Poetry is not installed. Please install Poetry: https://python-poetry.org/docs/#installation" -ForegroundColor Red; exit 1
        }
        Write-Host "[OK] Poetry is installed" -ForegroundColor Green
    } catch {
        Write-Host "ERROR: `Poetry is not installed. Please install Poetry: https://python-poetry.org/docs/#installation" -ForegroundColor Red; exit 1
    }
}

# Function to check if npm is installed
function Test-Npm {
    try {
        $null = & npm --version 2>&1
        if ($LASTEXITCODE -ne 0) {
            Write-Host "ERROR: `npm is not installed. Please install Node.js and npm." -ForegroundColor Red; exit 1
        }
        Write-Host "[OK] npm is installed" -ForegroundColor Green
    } catch {
        Write-Host "ERROR: `npm is not installed. Please install Node.js and npm." -ForegroundColor Red; exit 1
    }
}

# Function to check Node version
function Test-NodeVersion {
    try {
        $nodeVersionOutput = & node --version 2>&1
        if ($nodeVersionOutput -match 'v(\d+)\.') {
            $nodeVersion = [int]$matches[1]
        } else {
            Write-Host "ERROR: `Unable to determine Node.js version." -ForegroundColor Red; exit 1
        }
        
        if ($nodeVersion -lt 20) {
            Write-Host "ERROR: `Node version $nodeVersion is installed, but version 20 or higher is required." -ForegroundColor Red; exit 1
        }
        Write-Host "[OK] Node version $nodeVersion detected" -ForegroundColor Green
    } catch {
        Write-Host "ERROR: `Unable to determine Node.js version." -ForegroundColor Red; exit 1
    }
}

# Function to setup .env file
function Initialize-EnvFile {
    param(
        [string]$ServiceDir,
        [string]$ApiUrl = ""
    )
    
    $envFile = Join-Path $ServiceDir ".env"
    $envExampleFile = Join-Path $ServiceDir ".env.example"
    
    if (!(Test-Path $envFile) -and (Test-Path $envExampleFile)) {
        Copy-Item $envExampleFile $envFile
        
        # If API_URL is specified, update it
        if ($ApiUrl) {
            $content = Get-Content $envFile -Raw
            $content = $content -replace 'API_URL=.*', "API_URL=$ApiUrl"
            Set-Content -Path $envFile -Value $content -NoNewline
        }
        
        Write-Host "[OK] Created .env file for $(Split-Path $ServiceDir -Leaf)" -ForegroundColor Green
    }
}

# Service functions
function Start-AlloyApi {
    Write-Host "[INFO] Starting alloy-api..." -ForegroundColor Cyan
    $serviceDir = Join-Path $ProjectRoot "alloy-api"
    
    if (!(Test-Path $serviceDir)) {
        Write-Host "ERROR: `Cannot find alloy-api directory" -ForegroundColor Red; exit 1
    }
    
    $javaVersion = Test-Java
    
    if ($javaVersion -gt 17) {
        Update-BuildGradle -JavaVersion $javaVersion
    }
    
    Write-Host "[INFO] Building and starting alloy-api on port 8080..." -ForegroundColor Cyan
    
    $job = Start-Job -Name "alloy-api" -ScriptBlock {
        param($dir)
        Set-Location $dir
        & .\gradlew.bat bootRun
    } -ArgumentList $serviceDir
    
    $Global:Jobs += $job
    Write-Host "[OK] alloy-api started (Job ID: $($job.Id))" -ForegroundColor Green
}

function Start-Backend {
    Write-Host "[INFO] Starting backend..." -ForegroundColor Cyan
    $serviceDir = Join-Path $ProjectRoot "backend"
    
    if (!(Test-Path $serviceDir)) {
        Write-Host "ERROR: `Cannot find backend directory" -ForegroundColor Red; exit 1
    }
    
    Initialize-EnvFile -ServiceDir $serviceDir
    Test-Poetry
    
    Write-Host "[INFO] Installing dependencies and starting backend on port 8000..." -ForegroundColor Cyan
    
    $job = Start-Job -Name "backend" -ScriptBlock {
        param($dir)
        Set-Location $dir
        & poetry install
        & poetry run python app.py
    } -ArgumentList $serviceDir
    
    $Global:Jobs += $job
    Write-Host "[OK] backend started (Job ID: $($job.Id))" -ForegroundColor Green
}

function Start-Frontend {
    Write-Host "[INFO] Starting frontend..." -ForegroundColor Cyan
    $serviceDir = Join-Path $ProjectRoot "frontend"
    
    if (!(Test-Path $serviceDir)) {
        Write-Host "ERROR: `Cannot find frontend directory" -ForegroundColor Red; exit 1
    }
    
    Initialize-EnvFile -ServiceDir $serviceDir
    Test-Npm
    Test-NodeVersion
    
    Write-Host "[INFO] Installing dependencies..." -ForegroundColor Cyan
    Push-Location $serviceDir
    & npm install | Out-Null
    Pop-Location
    
    Write-Host "[INFO] Starting frontend on port 5173..." -ForegroundColor Cyan
    
    $job = Start-Job -Name "frontend" -ScriptBlock {
        param($dir)
        Set-Location $dir
        & npm run dev
    } -ArgumentList $serviceDir
    
    $Global:Jobs += $job
    Write-Host "[OK] frontend started (Job ID: $($job.Id))" -ForegroundColor Green
}

function Start-LimbooleApi {
    Write-Host "[INFO] Starting limboole-api..." -ForegroundColor Cyan
    $serviceDir = Join-Path $ProjectRoot "limboole-api"
    
    if (!(Test-Path $serviceDir)) {
        Write-Host "ERROR: `Cannot find limboole-api directory" -ForegroundColor Red; exit 1
    }
    
    Initialize-EnvFile -ServiceDir $serviceDir -ApiUrl "http://localhost:8000"
    
    Write-Host "[INFO] Installing dependencies and starting limboole-api on port 8084..." -ForegroundColor Cyan
    
    $job = Start-Job -Name "limboole-api" -ScriptBlock {
        param($dir)
        Set-Location $dir
        & poetry install
        & poetry run uvicorn main:app --reload --port 8084
    } -ArgumentList $serviceDir
    
    $Global:Jobs += $job
    Write-Host "[OK] limboole-api started (Job ID: $($job.Id))" -ForegroundColor Green
}

function Start-LimbooleDiffApi {
    Write-Host "[INFO] Starting limboole-diff-api..." -ForegroundColor Cyan
    $serviceDir = Join-Path $ProjectRoot "limboole-diff-api"
    
    if (!(Test-Path $serviceDir)) {
        Write-Host "ERROR: `Cannot find limboole-diff-api directory" -ForegroundColor Red; exit 1
    }
    
    Initialize-EnvFile -ServiceDir $serviceDir -ApiUrl "http://localhost:8000"
    
    Write-Host "[INFO] Installing dependencies and starting limboole-diff-api on port 8051..." -ForegroundColor Cyan
    
    $job = Start-Job -Name "limboole-diff-api" -ScriptBlock {
        param($dir)
        Set-Location $dir
        & poetry install
        & poetry run uvicorn main:app --reload --port 8051
    } -ArgumentList $serviceDir
    
    $Global:Jobs += $job
    Write-Host "[OK] limboole-diff-api started (Job ID: $($job.Id))" -ForegroundColor Green
}

function Start-NuxmvApi {
    Write-Host "[INFO] Starting nuxmv-api..." -ForegroundColor Cyan
    $serviceDir = Join-Path $ProjectRoot "nuxmv-api"
    
    if (!(Test-Path $serviceDir)) {
        Write-Host "ERROR: `Cannot find nuxmv-api directory" -ForegroundColor Red; exit 1
    }
    
    Initialize-EnvFile -ServiceDir $serviceDir -ApiUrl "http://localhost:8000"
    
    Write-Host "[INFO] Installing dependencies and starting nuxmv-api on port 8081..." -ForegroundColor Cyan
    
    $job = Start-Job -Name "nuxmv-api" -ScriptBlock {
        param($dir)
        Set-Location $dir
        & poetry install
        & poetry run uvicorn main:app --reload --port 8081
    } -ArgumentList $serviceDir
    
    $Global:Jobs += $job
    Write-Host "[OK] nuxmv-api started (Job ID: $($job.Id))" -ForegroundColor Green
}

function Start-SmtDiffApi {
    Write-Host "[INFO] Starting smt-diff-api..." -ForegroundColor Cyan
    $serviceDir = Join-Path $ProjectRoot "smt-diff-api"
    
    if (!(Test-Path $serviceDir)) {
        Write-Host "ERROR: `Cannot find smt-diff-api directory" -ForegroundColor Red; exit 1
    }
    
    Initialize-EnvFile -ServiceDir $serviceDir -ApiUrl "http://localhost:8000"
    
    Write-Host "[INFO] Installing dependencies and starting smt-diff-api on port 8052..." -ForegroundColor Cyan
    
    $job = Start-Job -Name "smt-diff-api" -ScriptBlock {
        param($dir)
        Set-Location $dir
        & poetry install
        & poetry run uvicorn main:app --reload --port 8052
    } -ArgumentList $serviceDir
    
    $Global:Jobs += $job
    Write-Host "[OK] smt-diff-api started (Job ID: $($job.Id))" -ForegroundColor Green
}

function Start-SpectraApi {
    Write-Host "[INFO] Starting spectra-api..." -ForegroundColor Cyan
    $serviceDir = Join-Path $ProjectRoot "spectra-api"
    
    if (!(Test-Path $serviceDir)) {
        Write-Host "ERROR: `Cannot find spectra-api directory" -ForegroundColor Red; exit 1
    }
    
    Initialize-EnvFile -ServiceDir $serviceDir -ApiUrl "http://localhost:8000"
    
    Write-Host "[INFO] Installing dependencies and starting spectra-api on port 8083..." -ForegroundColor Cyan
    
    $job = Start-Job -Name "spectra-api" -ScriptBlock {
        param($dir)
        Set-Location $dir
        & poetry install
        & poetry run uvicorn main:app --reload --port 8083
    } -ArgumentList $serviceDir
    
    $Global:Jobs += $job
    Write-Host "[OK] spectra-api started (Job ID: $($job.Id))" -ForegroundColor Green
}

function Start-Z3Api {
    Write-Host "[INFO] Starting z3-api..." -ForegroundColor Cyan
    $serviceDir = Join-Path $ProjectRoot "z3-api"
    
    if (!(Test-Path $serviceDir)) {
        Write-Host "ERROR: `Cannot find z3-api directory" -ForegroundColor Red; exit 1
    }
    
    Initialize-EnvFile -ServiceDir $serviceDir -ApiUrl "http://localhost:8000"
    
    Write-Host "[INFO] Installing dependencies and starting z3-api on port 8082..." -ForegroundColor Cyan
    
    $job = Start-Job -Name "z3-api" -ScriptBlock {
        param($dir)
        Set-Location $dir
        & poetry install
        & poetry run uvicorn main:app --reload --port 8082
    } -ArgumentList $serviceDir
    
    $Global:Jobs += $job
    Write-Host "[OK] z3-api started (Job ID: $($job.Id))" -ForegroundColor Green
}

# Main menu
function Show-Menu {
    Write-Host "`n==========================================" -ForegroundColor Cyan
    Write-Host "[OK]  FM Playground - Service Manager" -ForegroundColor Cyan
    Write-Host "==========================================" -ForegroundColor Cyan
    Write-Host "`nSelect services to start (comma-separated numbers or 'all'):`n"
    Write-Host "[OK]  1) backend           (Port 8000) [Required for API services]"
    Write-Host "[OK]  2) frontend          (Port 5173)"
    Write-Host "[OK]  3) alloy-api         (Port 8080)"
    Write-Host "[OK]  4) limboole-api      (Port 8084)"
    Write-Host "[OK]  5) limboole-diff-api (Port 8051)"
    Write-Host "[OK]  6) z3-api            (Port 8082)"
    Write-Host "[OK]  7) smt-diff-api      (Port 8052)"
    Write-Host "[OK]  8) nuxmv-api         (Port 8081)"
    Write-Host "[OK]  9) spectra-api       (Port 8083)"
    Write-Host ""
    Write-Host "[OK]  all) Start all services"
    Write-Host "[OK]  q) Quit"
    Write-Host ""
}

# Create logs directory if it doesn't exist
$logsDir = Join-Path $ProjectRoot "logs"
if (!(Test-Path $logsDir)) {
    New-Item -ItemType Directory -Path $logsDir | Out-Null
}

# Main execution
Show-Menu
$choice = Read-Host "Enter your choice"

# Parse selection
if ($choice -eq "q" -or $choice -eq "Q") {
    Write-Host "Exiting..."
    exit 0
}

# Convert comma-separated input to array
$selections = $choice -split ',' | ForEach-Object { $_.Trim() }

# Determine which services to start
$servicesToStart = @()

if ($choice -eq "all" -or $choice -eq "ALL") {
    $servicesToStart = @("backend", "frontend", "alloy-api", "limboole-api", "limboole-diff-api", "z3-api", "smt-diff-api", "nuxmv-api", "spectra-api")
} else {
    foreach ($selection in $selections) {
        switch ($selection) {
            "1" { $servicesToStart += "backend" }
            "2" { $servicesToStart += "frontend" }
            "3" { $servicesToStart += "alloy-api" }
            "4" { $servicesToStart += "limboole-api" }
            "5" { $servicesToStart += "limboole-diff-api" }
            "6" { $servicesToStart += "z3-api" }
            "7" { $servicesToStart += "smt-diff-api" }
            "8" { $servicesToStart += "nuxmv-api" }
            "9" { $servicesToStart += "spectra-api" }
            default { Write-Host "[WARN] Invalid selection: $selection" -ForegroundColor Yellow }
        }
    }
}

# Check if any API services are selected without backend
$apiServices = @("limboole-api", "limboole-diff-api", "nuxmv-api", "smt-diff-api", "spectra-api", "z3-api")
$needsBackend = $false

foreach ($service in $servicesToStart) {
    if ($service -in $apiServices) {
        $needsBackend = $true
        break
    }
}

if ($needsBackend -and "backend" -notin $servicesToStart) {
    Write-Host "[WARN] API services require backend. Adding backend to startup sequence..." -ForegroundColor Yellow
    $servicesToStart = @("backend") + $servicesToStart
}

# Remove duplicates while preserving order
$uniqueServices = @()
foreach ($service in $servicesToStart) {
    if ($service -notin $uniqueServices) {
        $uniqueServices += $service
    }
}

if ($uniqueServices.Count -eq 0) {
    Write-Host "ERROR: `No valid services selected" -ForegroundColor Red; exit 1
}

# Display selected services
Write-Host "`nStarting the following services:" -ForegroundColor Green
foreach ($service in $uniqueServices) {
    Write-Host "  * $service" -ForegroundColor Green
}
Write-Host ""

# Check if required ports are available
Write-Host "[INFO] Checking port availability..." -ForegroundColor Cyan
foreach ($service in $uniqueServices) {
    switch ($service) {
        "alloy-api" { Test-Port -Port 8080 -ServiceName "alloy-api" }
        "backend" { Test-Port -Port 8000 -ServiceName "backend" }
        "frontend" { Test-Port -Port 5173 -ServiceName "frontend" }
        "limboole-api" { Test-Port -Port 8084 -ServiceName "limboole-api" }
        "limboole-diff-api" { Test-Port -Port 8051 -ServiceName "limboole-diff-api" }
        "nuxmv-api" { Test-Port -Port 8081 -ServiceName "nuxmv-api" }
        "smt-diff-api" { Test-Port -Port 8052 -ServiceName "smt-diff-api" }
        "spectra-api" { Test-Port -Port 8083 -ServiceName "spectra-api" }
        "z3-api" { Test-Port -Port 8082 -ServiceName "z3-api" }
    }
}
Write-Host "[OK] All required ports are available" -ForegroundColor Green
Write-Host ""

# Start services
foreach ($service in $uniqueServices) {
    switch ($service) {
        "alloy-api" { Start-AlloyApi }
        "backend" { Start-Backend }
        "frontend" { Start-Frontend }
        "limboole-api" { Start-LimbooleApi }
        "limboole-diff-api" { Start-LimbooleDiffApi }
        "nuxmv-api" { Start-NuxmvApi }
        "smt-diff-api" { Start-SmtDiffApi }
        "spectra-api" { Start-SpectraApi }
        "z3-api" { Start-Z3Api }
    }
    # Small delay between service starts
    Start-Sleep -Seconds 2
}

# Summary
Write-Host "`n==========================================" -ForegroundColor Green
Write-Host "All selected services started!" -ForegroundColor Green
Write-Host "==========================================" -ForegroundColor Green
Write-Host "`nLogs directory: $logsDir" -ForegroundColor Cyan
Write-Host "`nRunning services:"
foreach ($job in $Global:Jobs) {
    Write-Host "  * $($job.Name) (Job ID: $($job.Id))" -ForegroundColor Green
}
Write-Host "`nPress Ctrl+C to stop all services" -ForegroundColor Yellow
Write-Host "Or use 'Get-Job' and 'Stop-Job' to manage services individually`n"

# Monitor jobs
try {
    Write-Host "Monitoring services... (Press Ctrl+C to stop)" -ForegroundColor Cyan
    while ($true) {
        Start-Sleep -Seconds 5
        
        # Check if any jobs have failed
        foreach ($job in $Global:Jobs) {
            $jobState = (Get-Job -Id $job.Id -ErrorAction SilentlyContinue).State
            if ($jobState -eq "Failed") {
                Write-Host "`n$($job.Name) has failed!" -ForegroundColor Red
                Receive-Job -Id $job.Id
            }
        }
    }
} finally {
    Stop-AllServices
}
