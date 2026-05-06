# HWML Language Support for Visual Studio Code

Language support for HWML (Hardware Modeling Language) including syntax highlighting, diagnostics, and language server integration.

## Features

- **Syntax Highlighting** - Full syntax highlighting for `.hwml` files
- **Language Server Integration** - Real-time diagnostics and error checking
- **Workspace Support** - Automatic detection of `hwml.toml` workspace files
- **Library Support** - Multi-library workspace support with dependency management

## Requirements

1. **HWML LSP Server** - The language server binary must be built and available

   Build the LSP server from the project root:
   ```bash
   cargo build --package hwml_lsp_server
   ```

2. **Rust Toolchain** - Required to build the LSP server (if not pre-built)

## Installation

### Method 1: Install from VSIX (Recommended)

1. Build the LSP server:
   ```bash
   cargo build --package hwml_lsp_server
   ```

2. Package the extension:
   ```bash
   cd hwml-vscode
   npx vsce package
   ```

3. Install the generated `.vsix` file:
   - In VSCode: Extensions → ... menu → Install from VSIX
   - Or via command line: `code --install-extension hwml-vscode-0.0.1.vsix`

### Method 2: Development Mode

1. Build the LSP server (see above)

2. Compile the extension:
   ```bash
   cd hwml-vscode
   npm install
   npm run compile
   ```

3. Open the `hwml-rust` workspace in VSCode

4. Press F5 to launch the Extension Development Host

## Configuration

This extension contributes the following settings:

* `hwml.server_path` - Path to the `hwml_lsp_server` executable (default: `hwml_lsp_server`)
  - The extension automatically looks for the server in `target/debug/hwml_lsp_server` when working in the workspace
  - For system-wide installation, ensure the binary is in your PATH or provide the full path

* `hwml.trace.server` - Trace communication between VSCode and the language server
  - Options: `off`, `messages`, `verbose`
  - Default: `off`

* `hwml.maxNumberOfProblems` - Maximum number of problems to show (default: 100)

## Commands

* `HWML: Restart Language Server` - Restart the HWML language server

## Usage

1. Open a folder containing a `hwml.toml` workspace file
2. The extension will activate automatically when you open a `.hwml` file
3. The LSP server will load all libraries defined in the workspace

## Workspace Structure

```
my-project/
├── hwml.toml          # Workspace manifest
└── src/
    ├── main.hwml
    └── util.hwml
```

Example `hwml.toml`:
```toml
[library]
name = "my-project"
edition = 2024
```

## Release Notes

### 0.0.1

Initial release with:
- Syntax highlighting for `.hwml` files
- Language server integration with diagnostics
- Workspace and library support
- Auto-detection of `hwml.toml` files
