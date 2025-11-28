# Change Log

All notable changes to the "FM Playground" extension will be documented in this file.

## [2.7.10] - 2025-11-20

### Added
- Initial release of FM Playground VSCode extension
- Support for Limboole language (.limboole files)
  - Syntax highlighting via TextMate grammar
  - Command to execute Limboole code
  - Language configuration for auto-closing brackets and comments
- Support for SMT-LIB language (.smt2, .smt files)
  - Syntax highlighting via TextMate grammar
  - Command to execute Z3 solver
  - Language configuration for S-expressions
- Support for Spectra language (.spectra files)
  - Syntax highlighting via TextMate grammar
  - Command to execute Spectra synthesis
  - Language configuration
- Support for nuXmv language (.smv files)
  - Basic language configuration
  - Command to execute nuXmv model checker
- Extension commands:
  - `FM Playground: Open Playground` - Opens webview with tool information
  - `FM Playground: Run Limboole` - Executes Limboole on current file
  - `FM Playground: Run Z3` - Executes Z3 on current file
  - `FM Playground: Run nuXmv` - Executes nuXmv on current file
  - `FM Playground: Run Spectra` - Executes Spectra on current file
- Configuration settings for API endpoints:
  - `fm-playground.limboole.apiUrl`
  - `fm-playground.z3.apiUrl`
  - `fm-playground.nuxmv.apiUrl`
  - `fm-playground.spectra.apiUrl`
- Dedicated output channels for each tool
- Example files for all supported languages
- Comprehensive documentation:
  - README with features and usage instructions
  - INSTALL guide with detailed setup instructions
  - CHANGELOG

### Features
- Execute formal methods tools directly from VSCode
- View results in dedicated output channels
- Syntax highlighting for all supported languages
- Configurable API endpoints for backend services
- Webview panel with tool overview and quick start guide

### Technical Details
- Built with TypeScript
- Webpack bundling for production
- Language Server Protocol ready
- Compatible with VSCode 1.93.0 and higher

## Future Improvements

Planned features for future releases:
- Enhanced language server integration with autocomplete
- Inline diagnostics and error highlighting
- Support for Alloy language
- Interactive result visualization
- Debugging support for formal specifications
- Integration with version control for proof/verification history
- Snippet support for common patterns
- Documentation hover support
