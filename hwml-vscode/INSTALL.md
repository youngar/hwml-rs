# HWML VSCode Extension Installation Guide

This guide covers installation and setup of the HWML language extension for Visual Studio Code.

## Prerequisites

- Visual Studio Code (version 1.87.0 or later)
- Rust toolchain (for building the LSP server)

## Quick Installation

### Step 1: Build the LSP Server

From the project root (`hwml-rust/`):

```bash
cargo build --package hwml_lsp_server
```

This creates the language server binary at `target/debug/hwml_lsp_server`.

### Step 2: Install the Extension

**Option A: Install from VSIX file**

The VSIX file is already built at `hwml-vscode/hwml-vscode-0.0.1.vsix`.

In VSCode:
1. Open the Extensions view (Cmd+Shift+X on macOS, Ctrl+Shift+X on Linux/Windows)
2. Click the "..." menu at the top of the Extensions view
3. Select "Install from VSIX..."
4. Navigate to `hwml-rust/hwml-vscode/` and select `hwml-vscode-0.0.1.vsix`

**Option B: Install via command line**

```bash
code --install-extension hwml-vscode/hwml-vscode-0.0.1.vsix
```

### Step 3: Verify Installation

1. Open the `examples/simple-workspace` directory in VSCode
2. Open any `.hwml` file
3. You should see:
   - Syntax highlighting
   - The HWML language server activating (check the Output panel → "HWML Language Server")
   - Any parsing errors showing up as diagnostics

## Configuration

The extension looks for the LSP server in this order:

1. The configured path in `hwml.server_path` setting
2. `<workspace>/target/debug/hwml_lsp_server` (for development)
3. `hwml_lsp_server` in your system PATH

### Setting a Custom Server Path

If the LSP server is not automatically found:

1. Open VSCode Settings (Cmd+, on macOS, Ctrl+, on Linux/Windows)
2. Search for "hwml"
3. Set "Hwml: Server Path" to the full path to your `hwml_lsp_server` binary

Example:
```json
{
  "hwml.server_path": "/Users/yourname/hwml-rust/target/debug/hwml_lsp_server"
}
```

## Development Mode (For Extension Development)

If you're working on the extension itself:

1. Build the LSP server (see Step 1 above)

2. Install dependencies and compile:
   ```bash
   cd hwml-vscode
   npm install
   npm run compile
   ```

3. Open the `hwml-rust` workspace in VSCode

4. Open `hwml-vscode/src/extension.ts`

5. Press F5 to launch Extension Development Host

This opens a new VSCode window with the extension loaded from source.

## Troubleshooting

### Extension doesn't activate

- Check that you have a `.hwml` file open or a `hwml.toml` in your workspace
- Look for activation errors in: View → Output → "HWML Language Server"

### LSP server not found

- Verify the server is built: `ls -l target/debug/hwml_lsp_server`
- Check the extension output: View → Output → "HWML Language Server"
- Set an explicit path in settings (see Configuration above)

### No diagnostics/errors showing

- Ensure the LSP server is running (check Output panel)
- Try the "HWML: Restart Language Server" command
- Check for errors in the LSP server output

## Rebuilding the Extension

If you make changes to the extension or need to rebuild:

```bash
cd hwml-vscode
npm run compile
npx vsce package --allow-missing-repository
```

Then reinstall the new `.vsix` file.

## Uninstalling

1. Open Extensions view
2. Find "HWML Language Support"
3. Click the gear icon → Uninstall

Or via command line:
```bash
code --uninstall-extension hwml.hwml-vscode
```

## Next Steps

- See [README.md](README.md) for feature documentation
- Check out [examples/simple-workspace](../examples/simple-workspace) for a sample project
- Read the [HWML documentation](../docs) to learn the language
