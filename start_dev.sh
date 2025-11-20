#!/bin/bash

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Project root directory
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Array to store PIDs of background processes
declare -a PIDS=()
declare -a SERVICE_NAMES=()

# Cleanup function
cleanup() {
    echo -e "\n${YELLOW}Stopping all services...${NC}"
    for i in "${!PIDS[@]}"; do
        if ps -p "${PIDS[$i]}" > /dev/null 2>&1; then
            echo -e "${YELLOW}Stopping ${SERVICE_NAMES[$i]} (PID: ${PIDS[$i]})${NC}"
            kill -TERM "${PIDS[$i]}" 2>/dev/null
        fi
    done
    wait
    echo -e "${GREEN}All services stopped.${NC}"
    exit 0
}

trap cleanup SIGINT SIGTERM

# Helper function to print error and exit
error_exit() {
    echo -e "${RED}ERROR: $1${NC}" >&2
    exit 1
}

# Helper function to print success
success_msg() {
    echo -e "${GREEN}✓ $1${NC}"
}

# Helper function to print info
info_msg() {
    echo -e "${BLUE}ℹ $1${NC}"
}

# Helper function to print warning
warn_msg() {
    echo -e "${YELLOW}⚠ $1${NC}"
}

# Function to check if a port is in use
check_port() {
    local port=$1
    local service_name=$2
    
    if lsof -Pi :$port -sTCP:LISTEN -t >/dev/null 2>&1 ; then
        error_exit "Port $port is already in use (required for $service_name). Please stop the service using this port first."
    fi
}

# Function to check if Java is installed and get version
check_java() {
    if ! command -v java &> /dev/null; then
        error_exit "Java is not installed. Please install Java 17 or higher."
    fi
    
    # Get Java version
    java_version=$(java -version 2>&1 | awk -F '"' '/version/ {print $2}' | cut -d. -f1)
    
    if [ "$java_version" -lt 17 ]; then
        error_exit "Java version $java_version is installed, but version 17 or higher is required."
    fi
    
    success_msg "Java version $java_version detected"
    echo "$java_version"
}

# Function to update build.gradle with Java version
update_build_gradle() {
    local java_version=$1
    local build_file="$PROJECT_ROOT/alloy-api/build.gradle"
    
    if [ -f "$build_file" ]; then
        # Update the languageVersion in build.gradle
        sed -i.bak "s/languageVersion = JavaLanguageVersion.of([0-9]*)/languageVersion = JavaLanguageVersion.of($java_version)/" "$build_file"
        rm -f "$build_file.bak"
        success_msg "Updated build.gradle to use Java $java_version"
    fi
}

# Function to check if Poetry is installed
check_poetry() {
    if ! command -v poetry &> /dev/null; then
        error_exit "Poetry is not installed. Please install Poetry: https://python-poetry.org/docs/#installation"
    fi
    success_msg "Poetry is installed"
}

# Function to check if npm is installed
check_npm() {
    if ! command -v npm &> /dev/null; then
        error_exit "npm is not installed. Please install Node.js and npm."
    fi
    success_msg "npm is installed"
}

# Function to check Node version
check_node_version() {
    local node_version=$(node -v | cut -d'v' -f2 | cut -d'.' -f1)
    if [ "$node_version" -lt 20 ]; then
        error_exit "Node version $node_version is installed, but version 20 or higher is required."
    fi
    success_msg "Node version $node_version detected"
}

# Function to setup .env file
setup_env() {
    local service_dir=$1
    local api_url=${2:-""}
    
    if [ ! -f "$service_dir/.env" ] && [ -f "$service_dir/.env.example" ]; then
        cp "$service_dir/.env.example" "$service_dir/.env"
        
        # If API_URL is specified, update it
        if [ -n "$api_url" ]; then
            if [[ "$OSTYPE" == "darwin"* ]]; then
                sed -i '' "s|API_URL=.*|API_URL=$api_url|g" "$service_dir/.env"
            else
                sed -i "s|API_URL=.*|API_URL=$api_url|g" "$service_dir/.env"
            fi
        fi
        
        success_msg "Created .env file for $(basename $service_dir)"
    fi
}

# Service functions
start_alloy_api() {
    info_msg "Starting alloy-api..."
    cd "$PROJECT_ROOT/alloy-api" || error_exit "Cannot find alloy-api directory"
    
    local java_version=$(check_java)
    
    if [ "$java_version" -gt 17 ]; then
        update_build_gradle "$java_version"
    fi
    
    info_msg "Building and starting alloy-api on port 8080..."
    ./gradlew bootRun > "$PROJECT_ROOT/logs/alloy-api.log" 2>&1 &
    PIDS+=($!)
    SERVICE_NAMES+=("alloy-api")
    success_msg "alloy-api started (PID: $!)"
}

start_backend() {
    info_msg "Starting backend..."
    cd "$PROJECT_ROOT/backend" || error_exit "Cannot find backend directory"
    
    setup_env "$PROJECT_ROOT/backend"
    check_poetry
    
    info_msg "Installing dependencies and starting backend on port 8000..."
    poetry install > "$PROJECT_ROOT/logs/backend-install.log" 2>&1
    poetry run python app.py > "$PROJECT_ROOT/logs/backend.log" 2>&1 &
    PIDS+=($!)
    SERVICE_NAMES+=("backend")
    success_msg "backend started (PID: $!)"
}

start_frontend() {
    info_msg "Starting frontend..."
    cd "$PROJECT_ROOT/frontend" || error_exit "Cannot find frontend directory"
    
    setup_env "$PROJECT_ROOT/frontend"
    check_npm
    check_node_version
    
    info_msg "Installing dependencies..."
    npm install > "$PROJECT_ROOT/logs/frontend-install.log" 2>&1
    
    info_msg "Starting frontend on port 5173..."
    npm run dev > "$PROJECT_ROOT/logs/frontend.log" 2>&1 &
    PIDS+=($!)
    SERVICE_NAMES+=("frontend")
    success_msg "frontend started (PID: $!)"
}

start_limboole_api() {
    info_msg "Starting limboole-api..."
    cd "$PROJECT_ROOT/limboole-api" || error_exit "Cannot find limboole-api directory"
    
    setup_env "$PROJECT_ROOT/limboole-api" "http://localhost:8000"
    
    info_msg "Installing dependencies and starting limboole-api on port 8084..."
    poetry install > "$PROJECT_ROOT/logs/limboole-api-install.log" 2>&1
    poetry run uvicorn main:app --reload --port 8084 > "$PROJECT_ROOT/logs/limboole-api.log" 2>&1 &
    PIDS+=($!)
    SERVICE_NAMES+=("limboole-api")
    success_msg "limboole-api started (PID: $!)"
}

start_limboole_diff_api() {
    info_msg "Starting limboole-diff-api..."
    cd "$PROJECT_ROOT/limboole-diff-api" || error_exit "Cannot find limboole-diff-api directory"
    
    setup_env "$PROJECT_ROOT/limboole-diff-api" "http://localhost:8000"
    
    info_msg "Installing dependencies and starting limboole-diff-api on port 8051..."
    poetry install > "$PROJECT_ROOT/logs/limboole-diff-api-install.log" 2>&1
    poetry run uvicorn main:app --reload --port 8051 > "$PROJECT_ROOT/logs/limboole-diff-api.log" 2>&1 &
    PIDS+=($!)
    SERVICE_NAMES+=("limboole-diff-api")
    success_msg "limboole-diff-api started (PID: $!)"
}

start_nuxmv_api() {
    info_msg "Starting nuxmv-api..."
    cd "$PROJECT_ROOT/nuxmv-api" || error_exit "Cannot find nuxmv-api directory"
    
    setup_env "$PROJECT_ROOT/nuxmv-api" "http://localhost:8000"
    
    info_msg "Installing dependencies and starting nuxmv-api on port 8081..."
    poetry install > "$PROJECT_ROOT/logs/nuxmv-api-install.log" 2>&1
    poetry run uvicorn main:app --reload --port 8081 > "$PROJECT_ROOT/logs/nuxmv-api.log" 2>&1 &
    PIDS+=($!)
    SERVICE_NAMES+=("nuxmv-api")
    success_msg "nuxmv-api started (PID: $!)"
}

start_smt_diff_api() {
    info_msg "Starting smt-diff-api..."
    cd "$PROJECT_ROOT/smt-diff-api" || error_exit "Cannot find smt-diff-api directory"
    
    setup_env "$PROJECT_ROOT/smt-diff-api" "http://localhost:8000"
    
    info_msg "Installing dependencies and starting smt-diff-api on port 8052..."
    poetry install > "$PROJECT_ROOT/logs/smt-diff-api-install.log" 2>&1
    poetry run uvicorn main:app --reload --port 8052 > "$PROJECT_ROOT/logs/smt-diff-api.log" 2>&1 &
    PIDS+=($!)
    SERVICE_NAMES+=("smt-diff-api")
    success_msg "smt-diff-api started (PID: $!)"
}

start_spectra_api() {
    info_msg "Starting spectra-api..."
    cd "$PROJECT_ROOT/spectra-api" || error_exit "Cannot find spectra-api directory"
    
    setup_env "$PROJECT_ROOT/spectra-api" "http://localhost:8000"
    
    info_msg "Installing dependencies and starting spectra-api on port 8083..."
    poetry install > "$PROJECT_ROOT/logs/spectra-api-install.log" 2>&1
    poetry run uvicorn main:app --reload --port 8083 > "$PROJECT_ROOT/logs/spectra-api.log" 2>&1 &
    PIDS+=($!)
    SERVICE_NAMES+=("spectra-api")
    success_msg "spectra-api started (PID: $!)"
}

start_z3_api() {
    info_msg "Starting z3-api..."
    cd "$PROJECT_ROOT/z3-api" || error_exit "Cannot find z3-api directory"
    
    setup_env "$PROJECT_ROOT/z3-api" "http://localhost:8000"
    
    info_msg "Installing dependencies and starting z3-api on port 8082..."
    poetry install > "$PROJECT_ROOT/logs/z3-api-install.log" 2>&1
    poetry run uvicorn main:app --reload --port 8082 > "$PROJECT_ROOT/logs/z3-api.log" 2>&1 &
    PIDS+=($!)
    SERVICE_NAMES+=("z3-api")
    success_msg "z3-api started (PID: $!)"
}

# Main menu
show_menu() {
    echo -e "\n${BLUE}═══════════════════════════════════════════${NC}"
    echo -e "${BLUE}  FM Playground - Service Manager${NC}"
    echo -e "${BLUE}═══════════════════════════════════════════${NC}\n"
    echo "Select services to start (comma-separated numbers or 'all'):"
    echo ""
    echo "  1) backend           (Port 8000) [Required for API services]"
    echo "  2) frontend          (Port 5173)"
    echo "  3) alloy-api         (Port 8080)"
    echo "  4) limboole-api      (Port 8084)"
    echo "  5) limboole-diff-api (Port 8051)"
    echo "  6) z3-api            (Port 8082)"
    echo "  7) smt-diff-api      (Port 8052)"
    echo "  8) nuxmv-api         (Port 8081)"
    echo "  9) spectra-api       (Port 8083)"
    echo ""
    echo "  all) Start all services"
    echo "  q) Quit"
    echo ""
}

# Create logs directory if it doesn't exist
mkdir -p "$PROJECT_ROOT/logs"

# Main execution
show_menu
read -p "Enter your choice: " choice

# Parse selection
if [ "$choice" = "q" ] || [ "$choice" = "Q" ]; then
    echo "Exiting..."
    exit 0
fi

# Convert comma-separated input to array
IFS=',' read -ra SELECTIONS <<< "$choice"

# Determine which services to start
declare -a services_to_start=()

if [ "$choice" = "all" ] || [ "$choice" = "ALL" ]; then
    services_to_start=("backend" "frontend" "alloy-api" "limboole-api" "limboole-diff-api" "z3-api" "smt-diff-api" "nuxmv-api" "spectra-api")
else
    for selection in "${SELECTIONS[@]}"; do
        selection=$(echo "$selection" | xargs) # Trim whitespace
        case $selection in
            1) services_to_start+=("backend") ;;
            2) services_to_start+=("frontend") ;;
            3) services_to_start+=("alloy-api") ;;
            4) services_to_start+=("limboole-api") ;;
            5) services_to_start+=("limboole-diff-api") ;;
            6) services_to_start+=("z3-api") ;;
            7) services_to_start+=("smt-diff-api") ;;
            8) services_to_start+=("nuxmv-api") ;;
            9) services_to_start+=("spectra-api") ;;
            *) warn_msg "Invalid selection: $selection" ;;
        esac
    done
fi

# Check if any API services are selected without backend
api_services=("limboole-api" "limboole-diff-api" "nuxmv-api" "smt-diff-api" "spectra-api" "z3-api")
needs_backend=false

for service in "${services_to_start[@]}"; do
    if [[ " ${api_services[@]} " =~ " ${service} " ]]; then
        needs_backend=true
        break
    fi
done

if [ "$needs_backend" = true ]; then
    if [[ ! " ${services_to_start[@]} " =~ " backend " ]]; then
        warn_msg "API services require backend. Adding backend to startup sequence..."
        services_to_start=("backend" "${services_to_start[@]}")
    fi
fi

# Remove duplicates while preserving order
declare -a unique_services=()
for service in "${services_to_start[@]}"; do
    if [[ ! " ${unique_services[@]} " =~ " ${service} " ]]; then
        unique_services+=("$service")
    fi
done

if [ ${#unique_services[@]} -eq 0 ]; then
    error_exit "No valid services selected"
fi

# Display selected services
echo -e "\n${GREEN}Starting the following services:${NC}"
for service in "${unique_services[@]}"; do
    echo -e "  ${GREEN}•${NC} $service"
done
echo ""

# Check if required ports are available
info_msg "Checking port availability..."
for service in "${unique_services[@]}"; do
    case $service in
        alloy-api) check_port 8080 "alloy-api" ;;
        backend) check_port 8000 "backend" ;;
        frontend) check_port 5173 "frontend" ;;
        limboole-api) check_port 8084 "limboole-api" ;;
        limboole-diff-api) check_port 8051 "limboole-diff-api" ;;
        nuxmv-api) check_port 8081 "nuxmv-api" ;;
        smt-diff-api) check_port 8052 "smt-diff-api" ;;
        spectra-api) check_port 8083 "spectra-api" ;;
        z3-api) check_port 8082 "z3-api" ;;
    esac
done
success_msg "All required ports are available"
echo ""

# Start services
for service in "${unique_services[@]}"; do
    case $service in
        alloy-api) start_alloy_api ;;
        backend) start_backend ;;
        frontend) start_frontend ;;
        limboole-api) start_limboole_api ;;
        limboole-diff-api) start_limboole_diff_api ;;
        nuxmv-api) start_nuxmv_api ;;
        smt-diff-api) start_smt_diff_api ;;
        spectra-api) start_spectra_api ;;
        z3-api) start_z3_api ;;
    esac
    # Small delay between service starts
    sleep 2
done

# Summary
echo -e "\n${GREEN}═══════════════════════════════════════════${NC}"
echo -e "${GREEN}All selected services started!${NC}"
echo -e "${GREEN}═══════════════════════════════════════════${NC}"
echo -e "\nLogs are available in: ${BLUE}$PROJECT_ROOT/logs/${NC}"
echo -e "\nRunning services:"
for i in "${!SERVICE_NAMES[@]}"; do
    echo -e "  ${GREEN}•${NC} ${SERVICE_NAMES[$i]} (PID: ${PIDS[$i]})"
done
echo -e "\n${YELLOW}Press Ctrl+C to stop all services${NC}\n"

# Wait for all background processes
wait
