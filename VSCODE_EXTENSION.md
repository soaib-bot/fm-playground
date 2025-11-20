# FM Playground VSCode Extension

This document provides information about the FM Playground VSCode extension, which allows you to use the Formal Methods Playground directly within Visual Studio Code.

## Overview

The FM Playground VSCode extension brings the power of formal verification tools directly into your code editor. Instead of using the web interface, you can now:

- Edit formal specifications with syntax highlighting
- Execute verification tools from the command palette
- View results in dedicated output channels
- Configure API endpoints for local or remote servers

## Features

### Supported Languages

The extension provides full language support for:

1. **Limboole** (`.limboole` files)
   - Boolean satisfiability solver
   - Syntax highlighting
   - Direct execution via command palette

2. **SMT-LIB** (`.smt2`, `.smt` files)
   - Z3 SMT solver support
   - S-expression syntax highlighting
   - Model generation and satisfiability checking

3. **Spectra** (`.spectra` files)
   - Reactive synthesis specifications
   - Syntax highlighting for Spectra syntax
   - Direct synthesis execution

4. **nuXmv** (`.smv` files)
   - Model checking specifications
   - Syntax highlighting
   - LTL/CTL property verification

### Commands

Access these commands via the Command Palette (`Ctrl+Shift+P` or `Cmd+Shift+P`):

- `FM Playground: Open Playground` - Opens an overview panel
- `FM Playground: Run Limboole` - Execute Limboole on the current file
- `FM Playground: Run Z3` - Execute Z3 on the current file
- `FM Playground: Run nuXmv` - Execute nuXmv on the current file
- `FM Playground: Run Spectra` - Execute Spectra on the current file

### Configuration

Configure API endpoints in VSCode settings:

```json
{
  "fm-playground.limboole.apiUrl": "http://localhost:8055",
  "fm-playground.z3.apiUrl": "http://localhost:8080",
  "fm-playground.nuxmv.apiUrl": "http://localhost:8080",
  "fm-playground.spectra.apiUrl": "http://localhost:8080"
}
```

## Installation

### Quick Install

1. **Build the extension**:
   ```bash
   cd vscode-extension
   npm install
   npm run package
   ```

2. **Install in VSCode**:
   - Open Visual Studio Code
   - Press `Ctrl+Shift+P` (Windows/Linux) or `Cmd+Shift+P` (Mac)
   - Type "Extensions: Install from VSIX"
   - Select `fm-playground-vscode-2.7.10.vsix`

For detailed installation instructions, see [vscode-extension/INSTALL.md](vscode-extension/INSTALL.md).

## Backend Requirements

The extension requires backend API servers to execute the formal verification tools. You can set these up using Docker Compose:

```bash
# From the repository root
docker compose up -d
```

This will start all required services:
- Limboole Diff API on port 8055
- Z3 API on port 8080
- nuXmv API on port 8080
- Spectra API on port 8080

Alternatively, configure the extension to use remote API endpoints in your VSCode settings.

## Usage Example

1. **Create a new file** `example.smt2`:
   ```smt
   (declare-const x Int)
   (declare-const y Int)
   (assert (= (+ x y) 10))
   (assert (= (- x y) 2))
   (check-sat)
   (get-model)
   ```

2. **Run Z3**:
   - Press `Ctrl+Shift+P` (or `Cmd+Shift+P`)
   - Type "FM Playground: Run Z3"
   - Press Enter

3. **View Results**:
   - Open the Output panel (View > Output)
   - Select "FM Playground - Z3" from the dropdown
   - See the satisfiability result and model

## Directory Structure

```
vscode-extension/
├── src/                          # TypeScript source files
│   ├── extension.ts              # Main extension entry point
│   ├── playgroundPanel.ts        # Webview panel implementation
│   └── executors/                # Tool executor implementations
│       ├── limbooleExecutor.ts
│       ├── z3Executor.ts
│       ├── nuxmvExecutor.ts
│       └── spectraExecutor.ts
├── syntaxes/                     # TextMate grammars for syntax highlighting
│   ├── limboole.tmLanguage.json
│   ├── smt.tmLanguage.json
│   └── spectra.tmLanguage.json
├── language-configurations/      # Language configurations
│   ├── limboole-language-configuration.json
│   ├── smt-language-configuration.json
│   ├── spectra-language-configuration.json
│   └── nuxmv-language-configuration.json
├── examples/                     # Example files for each language
│   ├── example.limboole
│   ├── example.smt2
│   ├── example.smv
│   └── example.spectra
├── dist/                         # Compiled JavaScript (generated)
├── package.json                  # Extension manifest
├── tsconfig.json                 # TypeScript configuration
├── webpack.config.js             # Webpack bundling configuration
├── README.md                     # Extension documentation
├── INSTALL.md                    # Detailed installation guide
├── CHANGELOG.md                  # Version history
└── LICENSE                       # MIT License
```

## Development

### Building from Source

```bash
cd vscode-extension
npm install
npm run compile
```

### Watch Mode

For continuous development with auto-recompilation:

```bash
npm run watch
```

### Testing

1. Open the `vscode-extension` folder in VSCode
2. Press `F5` to launch the Extension Development Host
3. A new VSCode window opens with the extension loaded
4. Test the extension features

### Packaging

To create a distributable VSIX package:

```bash
npm run package
```

This creates `fm-playground-vscode-2.7.10.vsix` in the `vscode-extension` directory.

## Comparison: Web vs VSCode Extension

### Web Application (Current)
- ✅ No installation required
- ✅ Works in any browser
- ✅ Full UI with visualizations
- ❌ Requires switching between editor and browser
- ❌ Limited editor features

### VSCode Extension (New)
- ✅ Integrated into your editor workflow
- ✅ Powerful VSCode editing features
- ✅ Keyboard shortcuts and command palette
- ✅ Works offline (with local servers)
- ✅ Git integration
- ❌ Requires installation
- ❌ Limited visualizations (terminal output only)

## Future Enhancements

Planned improvements for the VSCode extension:

- [ ] Enhanced Language Server Protocol (LSP) integration
- [ ] Inline diagnostics and error highlighting
- [ ] Autocomplete for language constructs
- [ ] Interactive visualization panels for results
- [ ] Debugging support for formal specifications
- [ ] Snippet support for common patterns
- [ ] Documentation on hover
- [ ] Support for Alloy language
- [ ] Integration with proof/verification history
- [ ] Custom themes for each language

## Contributing

Contributions to the VSCode extension are welcome! Here's how you can help:

1. **Report Issues**: Found a bug? Open an issue on GitHub
2. **Suggest Features**: Have an idea? Create a feature request
3. **Submit Pull Requests**: Fix bugs or add features
4. **Improve Documentation**: Help make the docs better

See the main [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

## Troubleshooting

### Extension Won't Load
- Check VSCode version (must be 1.93.0+)
- Reload window: `Ctrl+Shift+P` > "Developer: Reload Window"

### Tool Execution Fails
- Verify backend services are running
- Check API URLs in settings
- Check firewall settings

### No Syntax Highlighting
- Verify file extension is correct
- Check language mode in status bar
- Reload window

For more troubleshooting steps, see [vscode-extension/INSTALL.md](vscode-extension/INSTALL.md#troubleshooting).

## License

The FM Playground VSCode extension is licensed under the MIT License, same as the main FM Playground project.

## Support

- GitHub Issues: [fm-playground issues](https://github.com/fm4se/fm-playground/issues)
- Documentation: [formal-methods.net](https://formal-methods.net)
- Main Repository: [fm-playground](https://github.com/fm4se/fm-playground)
