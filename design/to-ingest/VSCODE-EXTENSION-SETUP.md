# HWML VSCode Extension - Complete Setup Guide

This document provides a complete overview of the HWML VSCode extension setup, including LSP server integration and workspace support.

## Overview

The HWML VSCode extension provides:
- ✅ Syntax highlighting for `.hwml` files
- ✅ Language Server Protocol (LSP) integration
- ✅ Real-time diagnostics and error checking
- ✅ Workspace file (`hwml.toml`) support
- ✅ Multi-library dependency resolution

## Architecture

```
┌─────────────────┐
│   VSCode IDE    │
│                 │
│  ┌───────────┐  │
│  │ Extension │  │ ← hwml-vscode/
│  └─────┬─────┘  │
└────────┼────────┘
         │ LSP Protocol (stdio)
         │
    ┌────▼────┐
    │   LSP   │
    │  Server │ ← crates/hwml-lsp-server/
    └────┬────┘
         │
    ┌────▼────┐
    │ HWML DB │ ← crates/hwml-db/
    │   VFS   │    crates/hwml-vfs/
    │ Parser  │    crates/hwml-workspace/
    └─────────┘
```

## Quick Start

### 1. Build the LSP Server

```bash
cargo build --package hwml_lsp_server
```

This creates: `target/debug/hwml_lsp_server`

### 2. Install the Extension

The extension is pre-packaged at: `hwml-vscode/hwml-vscode-0.0.1.vsix`

**Install via VSCode:**
1. Extensions → ... menu → Install from VSIX
2. Select `hwml-vscode/hwml-vscode-0.0.1.vsix`

**Install via command line:**
```bash
code --install-extension hwml-vscode/hwml-vscode-0.0.1.vsix
```

### 3. Test with Example Workspace

```bash
code examples/simple-workspace
```

Open `src/main.hwml` and verify:
- Syntax highlighting works
- LSP server activates (check Output → "HWML Language Server")
- Workspace manifest is detected

## Configuration

The extension uses these settings:

### `hwml.server_path` (default: `"hwml_lsp_server"`)

Path to the LSP server binary. The extension searches in this order:
1. Configured path in settings
2. `<workspace>/target/debug/hwml_lsp_server` (auto-detected for development)
3. `hwml_lsp_server` in system PATH

**Example:**
```json
{
  "hwml.server_path": "/usr/local/bin/hwml_lsp_server"
}
```

### `hwml.trace.server` (default: `"off"`)

Enable LSP protocol tracing for debugging:
- `"off"` - No tracing
- `"messages"` - Log message headers
- `"verbose"` - Log full message content

### `hwml.maxNumberOfProblems` (default: `100`)

Maximum number of diagnostics to show per file.

## Workspace Support

The LSP server automatically detects and loads `hwml.toml` workspace files.

### Example Workspace Structure

```
my-project/
├── hwml.toml              # Workspace manifest
└── src/
    ├── main.hwml
    └── util.hwml
```

### Example `hwml.toml`

```toml
[library]
name = "my-project"
edition = 2024

[sources]
files = ["src/main.hwml", "src/util.hwml"]

[[dependencies]]
name = "stdlib"
path = "../stdlib"
```

### How It Works

1. **Extension Activation:** Triggers when opening a `.hwml` file or when `hwml.toml` exists in workspace
2. **LSP Server Launch:** Extension spawns `hwml_lsp_server` and connects via stdio
3. **Workspace Discovery:** Server receives workspace root from VSCode initialization
4. **Manifest Loading:** Server looks for `hwml.toml` in workspace root
5. **Library Resolution:** Server loads all libraries and dependencies in topological order
6. **File Watching:** Extension watches `**/hwml.toml` for changes

## Commands

### HWML: Restart Language Server

Stops and restarts the LSP server. Useful when:
- Server becomes unresponsive
- Configuration changes require restart
- Workspace manifest is modified

Access via: `Cmd+Shift+P` → "HWML: Restart Language Server"

## Development

### Rebuilding the Extension

If you modify extension code:

```bash
cd hwml-vscode
npm run compile
npx vsce package --allow-missing-repository
```

Then reinstall the new `.vsix` file.

### Development Mode (F5)

For live extension development:

```bash
cd hwml-vscode
npm install
npm run compile
```

Then in VSCode:
- Open `hwml-vscode/src/extension.ts`
- Press F5
- This launches Extension Development Host with live reloading

### Debugging the LSP Server

The LSP server logs to stderr, which VSCode captures. To see logs:

1. View → Output
2. Select "HWML Language Server" from dropdown
3. Enable tracing: set `"hwml.trace.server": "verbose"` in settings

## File Locations

```
hwml-rust/
├── crates/
│   ├── hwml-lsp-server/     # LSP server implementation
│   ├── hwml-db/             # Database and queries
│   ├── hwml-vfs/            # Virtual file system (includes LspVfs)
│   └── hwml-workspace/      # Workspace loading
│
├── hwml-vscode/             # VSCode extension
│   ├── src/extension.ts     # Extension entry point
│   ├── package.json         # Extension manifest
│   ├── syntaxes/            # Syntax highlighting grammar
│   ├── out/                 # Compiled JavaScript
│   ├── hwml-vscode-0.0.1.vsix  # Packaged extension
│   ├── README.md            # User documentation
│   ├── INSTALL.md           # Installation guide
│   └── TEST.md              # Testing guide
│
├── examples/
│   └── simple-workspace/    # Test workspace
│
└── target/
    └── debug/
        └── hwml_lsp_server  # LSP server binary
```

## Troubleshooting

See `hwml-vscode/TEST.md` for detailed testing procedures.

Common issues:
- **Extension doesn't activate:** Check a `.hwml` file is open or `hwml.toml` exists
- **LSP server not found:** Build it with `cargo build --package hwml_lsp_server`
- **No diagnostics:** Check Output panel for server errors, try restart command

## Next Steps

1. Install the extension (see Quick Start above)
2. Test with `examples/simple-workspace`
3. Review `hwml-vscode/TEST.md` for comprehensive testing
4. Read `hwml-vscode/INSTALL.md` for detailed installation options
5. Explore workspace features by creating your own `hwml.toml` project
