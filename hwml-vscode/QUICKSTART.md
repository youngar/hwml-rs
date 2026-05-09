# HWML VSCode Extension - Quick Start

Get up and running with the HWML VSCode extension in 3 steps.

## Step 1: Build the LSP Server

From the project root:

```bash
cargo build --package hwml_lsp_server
```

✅ This creates: `target/debug/hwml_lsp_server`

## Step 2: Install the Extension

**Option A: Use the pre-built VSIX**

```bash
code --install-extension hwml-vscode/hwml-vscode-0.0.1.vsix
```

**Option B: Install via VSCode UI**

1. Open VSCode
2. Extensions → ... (three dots) → Install from VSIX
3. Select `hwml-vscode/hwml-vscode-0.0.1.vsix`

## Step 3: Test It

```bash
code examples/simple-workspace
```

Then:
1. Open `src/main.hwml`
2. Check syntax highlighting works
3. Open Output panel (View → Output)
4. Select "HWML Language Server" from dropdown
5. Verify you see:
   ```
   Using LSP server: /path/to/hwml-rust/target/debug/hwml_lsp_server
   LSP workspace root: /path/to/examples/simple-workspace
   Found workspace manifest: .../hwml.toml
   ```

## ✨ You're Done!

The extension is now:
- ✅ Syntax highlighting `.hwml` files
- ✅ Running the LSP server
- ✅ Detecting workspace files (`hwml.toml`)
- ✅ Providing diagnostics in real-time

## Next Steps

- **Create your own project:** Make a folder with `hwml.toml` and `.hwml` files
- **Configure settings:** Set `hwml.server_path` if the binary isn't auto-detected
- **Try commands:** `Cmd/Ctrl+Shift+P` → "HWML: Restart Language Server"
- **Read full docs:** See `README.md`, `INSTALL.md`, and `TEST.md`

## Troubleshooting

**Extension not activating?**
- Make sure you have a `.hwml` file open or `hwml.toml` in your workspace
- Reload VSCode window: `Cmd/Ctrl+Shift+P` → "Reload Window"

**LSP server not found?**
- Verify: `ls -l target/debug/hwml_lsp_server`
- Set explicit path: Settings → `hwml.server_path`

**No diagnostics showing?**
- Check Output → "HWML Language Server" for errors
- Try: `Cmd/Ctrl+Shift+P` → "HWML: Restart Language Server"

---

For comprehensive documentation, see [`VSCODE-EXTENSION-SETUP.md`](../VSCODE-EXTENSION-SETUP.md) in the project root.
