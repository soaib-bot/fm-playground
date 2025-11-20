# Installation Guide for FM Playground VSCode Extension

This guide provides detailed instructions for installing and using the FM Playground VSCode extension.

## Prerequisites

1. **Visual Studio Code** version 1.93.0 or higher
2. **Node.js** version 20.0.0 or higher (for development)
3. **Backend API Servers** (optional, see Backend Setup section)

## Installation Methods

### Method 1: Install from VSIX Package

1. **Build the VSIX package**:
   ```bash
   cd vscode-extension
   npm install
   npm run compile
   npm run package
   ```
   This will create a `.vsix` file in the `vscode-extension` directory.

2. **Install in VSCode**:
   - Open Visual Studio Code
   - Press `Ctrl+Shift+P` (Windows/Linux) or `Cmd+Shift+P` (Mac)
   - Type "Extensions: Install from VSIX"
   - Select the generated `.vsix` file
   - Reload VSCode when prompted

### Method 2: Run from Source (Development)

1. **Navigate to the extension directory**:
   ```bash
   cd vscode-extension
   ```

2. **Install dependencies**:
   ```bash
   npm install
   ```

3. **Compile the extension**:
   ```bash
   npm run compile
   ```

4. **Open in VSCode**:
   - Open the `vscode-extension` folder in VSCode
   - Press `F5` to launch the Extension Development Host
   - A new VSCode window will open with the extension loaded

## Backend Setup

The extension requires backend API servers to execute formal methods tools. You have two options:

### Option 1: Use Docker Compose (Recommended)

1. **Navigate to the repository root**:
   ```bash
   cd /path/to/fm-playground
   ```

2. **Copy environment configuration**:
   ```bash
   cp .env.example .env
   ```

3. **Start all services**:
   ```bash
   docker compose up -d
   ```

This will start all backend API servers on their default ports:
- Limboole Diff API: http://localhost:8055
- Z3 API: http://localhost:8080
- nuXmv API: http://localhost:8080
- Spectra API: http://localhost:8080

### Option 2: Use Remote API Endpoints

If you have access to remote API endpoints, you can configure them in VSCode settings:

1. Open VSCode Settings (File > Preferences > Settings)
2. Search for "FM Playground"
3. Configure the API URLs:
   - `fm-playground.limboole.apiUrl`
   - `fm-playground.z3.apiUrl`
   - `fm-playground.nuxmv.apiUrl`
   - `fm-playground.spectra.apiUrl`

## Verification

### 1. Check Extension Installation

1. Open VSCode
2. Press `Ctrl+Shift+X` (or `Cmd+Shift+X` on Mac)
3. Search for "FM Playground" in the installed extensions
4. Verify it's enabled

### 2. Test Syntax Highlighting

1. Open one of the example files from the `examples` directory:
   - `example.limboole`
   - `example.smt2`
   - `example.smv`
   - `example.spectra`
2. Verify that syntax highlighting is working

### 3. Test Tool Execution

**Prerequisites**: Backend API servers must be running (see Backend Setup)

1. Open an example file (e.g., `example.smt2`)
2. Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac)
3. Type "FM Playground: Run Z3"
4. Press Enter
5. Check the "FM Playground - Z3" output channel for results

## Using the Extension

### Opening the Playground View

1. Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac)
2. Type "FM Playground: Open Playground"
3. Press Enter
4. A webview panel will open with information about available tools

### Running Tools

1. **Create a new file** with the appropriate extension:
   - `.limboole` for Limboole
   - `.smt2` or `.smt` for Z3
   - `.smv` for nuXmv
   - `.spectra` for Spectra

2. **Write your specification** in the file

3. **Execute the tool**:
   - Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac)
   - Type the command:
     - "FM Playground: Run Limboole"
     - "FM Playground: Run Z3"
     - "FM Playground: Run nuXmv"
     - "FM Playground: Run Spectra"
   - Press Enter

4. **View results** in the corresponding output channel:
   - View > Output
   - Select the appropriate channel from the dropdown

## Configuration

### VSCode Settings

Configure the extension through VSCode settings:

1. **Open Settings**:
   - File > Preferences > Settings (Windows/Linux)
   - Code > Preferences > Settings (Mac)
   - Or press `Ctrl+,` (Windows/Linux) or `Cmd+,` (Mac)

2. **Search for "FM Playground"**

3. **Available Settings**:
   ```json
   {
     "fm-playground.limboole.apiUrl": "http://localhost:8055",
     "fm-playground.z3.apiUrl": "http://localhost:8080",
     "fm-playground.nuxmv.apiUrl": "http://localhost:8080",
     "fm-playground.spectra.apiUrl": "http://localhost:8080"
   }
   ```

### Workspace Settings

For project-specific configuration, create a `.vscode/settings.json` file in your workspace:

```json
{
  "fm-playground.limboole.apiUrl": "https://api.example.com/limboole",
  "fm-playground.z3.apiUrl": "https://api.example.com/z3",
  "fm-playground.nuxmv.apiUrl": "https://api.example.com/nuxmv",
  "fm-playground.spectra.apiUrl": "https://api.example.com/spectra"
}
```

## Troubleshooting

### Extension Not Loading

1. Check VSCode version (should be 1.93.0 or higher)
2. Reload VSCode: Press `Ctrl+Shift+P` > "Developer: Reload Window"
3. Check the Output panel for errors: View > Output > Select "FM Playground"

### Tool Execution Fails

1. **Verify backend services are running**:
   ```bash
   # Check if services are accessible
   curl http://localhost:8055/health  # Limboole
   curl http://localhost:8080/health  # Z3, nuXmv, Spectra
   ```

2. **Check API URLs in settings**:
   - Ensure the configured URLs are correct and accessible
   - Check for firewall or network issues

3. **Check output channel for detailed error messages**:
   - View > Output
   - Select the appropriate tool channel

### Syntax Highlighting Not Working

1. **Verify file extension**: Make sure the file has the correct extension
2. **Reload VSCode**: Press `Ctrl+Shift+P` > "Developer: Reload Window"
3. **Check language mode**: Click on the language indicator in the status bar and select the correct language

### Backend Connection Issues

1. **Check network connectivity**:
   ```bash
   ping localhost
   ```

2. **Verify Docker containers are running** (if using Docker):
   ```bash
   docker compose ps
   ```

3. **Check logs**:
   ```bash
   docker compose logs -f
   ```

## Uninstallation

1. Open VSCode
2. Press `Ctrl+Shift+X` (or `Cmd+Shift+X` on Mac)
3. Find "FM Playground" in the installed extensions
4. Click "Uninstall"
5. Reload VSCode when prompted

## Development

### Building from Source

```bash
cd vscode-extension
npm install
npm run compile
```

### Watch Mode

For continuous compilation during development:

```bash
npm run watch
```

### Packaging

To create a VSIX package:

```bash
npm run package
```

## Support

For issues, questions, or contributions:
- Visit the [GitHub repository](https://github.com/fm4se/fm-playground)
- Check existing issues or create a new one
- See the main README for contribution guidelines

## License

This extension is part of the FM Playground project and is licensed under the MIT License.
