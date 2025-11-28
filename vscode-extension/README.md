# FM Playground VSCode Extension

Formal Methods Playground extension for Visual Studio Code that provides support for multiple formal verification tools including Limboole, Z3, nuXmv, Alloy, and Spectra.

## Features

- **Syntax Highlighting**: Support for Limboole, SMT-LIB, Spectra, and nuXmv file formats
- **Execute Formal Methods Tools**: Run verification tools directly from VSCode
- **Output Panel Integration**: View results in dedicated output channels
- **Language Server Protocol**: Enhanced editing experience with language support
- **Configurable API Endpoints**: Connect to local or remote verification servers

## Supported Languages

- **Limboole** (.limboole) - Boolean satisfiability solver
- **SMT-LIB** (.smt2, .smt) - Z3 SMT solver
- **Spectra** (.spectra) - Reactive synthesis tool
- **nuXmv** (.smv) - Symbolic model checker

## Installation

### From VSIX

1. Download the `.vsix` file from the releases page
2. Open VSCode
3. Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac)
4. Type "Extensions: Install from VSIX"
5. Select the downloaded `.vsix` file

### From Source

1. Clone the repository
2. Navigate to the `vscode-extension` directory
3. Run `npm install`
4. Run `npm run compile`
5. Press F5 to open a new VSCode window with the extension loaded

## Usage

### Opening the Playground

1. Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac)
2. Type "FM Playground: Open Playground"
3. Press Enter

### Running Tools

1. Open a file with the appropriate extension (.limboole, .smt2, .smv, .spectra)
2. Write your formal specification
3. Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac)
4. Type the command for the tool you want to run:
   - `FM Playground: Run Limboole`
   - `FM Playground: Run Z3`
   - `FM Playground: Run nuXmv`
   - `FM Playground: Run Spectra`
5. View the results in the output panel

## Configuration

Configure API endpoints in VSCode settings:

1. Open Settings (File > Preferences > Settings)
2. Search for "FM Playground"
3. Configure the following settings:
   - `fm-playground.limboole.apiUrl`: URL of the Limboole API server (default: http://localhost:8055)
   - `fm-playground.z3.apiUrl`: URL of the Z3 API server (default: http://localhost:8080)
   - `fm-playground.nuxmv.apiUrl`: URL of the nuXmv API server (default: http://localhost:8080)
   - `fm-playground.spectra.apiUrl`: URL of the Spectra API server (default: http://localhost:8080)

## Requirements

The extension requires backend API servers for each tool to be running. You can either:
- Run the servers locally using Docker Compose (see main repository)
- Connect to remote API endpoints by configuring the URLs in settings

## Known Issues

- API servers must be running and accessible for tool execution
- Some features require network connectivity

## Contributing

Contributions are welcome! Please visit the [main repository](https://github.com/fm4se/fm-playground) for contribution guidelines.

## License

This project is licensed under the MIT License - see the LICENSE file in the main repository for details.

## Third-Party Licenses

- Limboole - https://github.com/maximaximal/limboole/blob/master/LICENSE
- Z3 - https://github.com/Z3Prover/z3/blob/master/LICENSE.txt
- nuXmv - https://nuxmv.fbk.eu/downloads/LICENSE.txt
- Alloy - https://github.com/AlloyTools/org.alloytools.alloy/blob/master/LICENSE
- Spectra - https://github.com/SpectraSynthesizer/spectra-synt/blob/master/LICENSE

## Release Notes

### 2.7.10

- Initial release of VSCode extension
- Support for Limboole, Z3, nuXmv, and Spectra
- Syntax highlighting for all supported languages
- Command palette integration for running tools
- Configurable API endpoints
