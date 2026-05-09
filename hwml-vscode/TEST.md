# Testing the HWML VSCode Extension

This document describes how to test the HWML VSCode extension after installation.

## Pre-Test Checklist

- [ ] LSP server is built: `cargo build --package hwml_lsp_server`
- [ ] Extension is installed (see INSTALL.md)
- [ ] VSCode is restarted after installation

## Test 1: Extension Activation

1. Open VSCode
2. Open the `examples/simple-workspace` folder
3. Open the Output panel (View → Output)
4. Select "HWML Language Server" from the dropdown
5. You should see a message like:
   ```
   Using LSP server: /path/to/hwml-rust/target/debug/hwml_lsp_server
   ```

**Expected Result:** The extension activates when the workspace contains a `hwml.toml` file.

## Test 2: Syntax Highlighting

1. Open `examples/simple-workspace/src/main.hwml`
2. Verify syntax highlighting is applied:
   - Keywords (`namespace`, `def`) should be highlighted
   - Comments (`//`) should be styled as comments
   - Identifiers and types should have appropriate colors

**Expected Result:** Syntax highlighting works for `.hwml` files.

## Test 3: Workspace Detection

1. With `examples/simple-workspace` open
2. Check the LSP server output panel
3. Look for messages about workspace initialization:
   ```
   LSP workspace root: /path/to/examples/simple-workspace
   Found workspace manifest: /path/to/examples/simple-workspace/hwml.toml
   Workspace manifest ready: /path/to/examples/simple-workspace/hwml.toml
   ```

**Expected Result:** The LSP server finds and loads the `hwml.toml` workspace file.

## Test 4: File Opening and Diagnostics

1. Open `examples/simple-workspace/src/main.hwml`
2. The LSP server should parse the file
3. Check the LSP server output for compilation messages
4. Any syntax errors should appear in the Problems panel (View → Problems)

**Expected Result:** Files are parsed and diagnostics are shown.

## Test 5: Restart Command

1. Open the Command Palette (Cmd+Shift+P or Ctrl+Shift+P)
2. Type "HWML: Restart Language Server"
3. Execute the command
4. Check the Output panel for restart confirmation

**Expected Result:** 
- Message "Restarting HWML Language Server..." appears
- LSP server restarts successfully
- Notification: "HWML Language Server restarted"

## Test 6: Configuration

1. Open Settings (Cmd+, or Ctrl+,)
2. Search for "hwml"
3. Verify these settings are available:
   - `hwml.server_path`
   - `hwml.trace.server`
   - `hwml.maxNumberOfProblems`

**Expected Result:** All HWML settings are visible and configurable.

## Test 7: File Watching (Workspace Changes)

1. Open `examples/simple-workspace`
2. Open `hwml.toml`
3. Make a change (e.g., change the name)
4. Save the file
5. Check the LSP server output

**Expected Result:** The LSP server should detect changes to `hwml.toml` (file watcher is configured).

## Test 8: Creating a New HWML File

1. In `examples/simple-workspace/src/`, create a new file: `test.hwml`
2. Add some content:
   ```hwml
   namespace Test {
       def Value : Bit = i1
   }
   ```
3. Save the file
4. Verify syntax highlighting and parsing

**Expected Result:** New `.hwml` files are recognized and parsed.

## Troubleshooting Test Failures

### Extension doesn't activate
- Check activation events in package.json
- Verify a `.hwml` file is open or `hwml.toml` exists in workspace
- Reload VSCode window

### No LSP server output
- Check server is built: `ls -l target/debug/hwml_lsp_server`
- Check configured server path in settings
- Look for errors in Developer Tools console (Help → Toggle Developer Tools)

### Syntax highlighting not working
- Verify the file has `.hwml` extension
- Check language mode in bottom-right of VSCode (should say "HWML")
- If it says "Plain Text", click it and select "HWML"

### Diagnostics not showing
- Check Problems panel is open (View → Problems)
- Verify LSP server is running (check Output panel)
- Try restarting the language server

## Manual LSP Server Test

To test the LSP server independently:

```bash
# The server expects LSP protocol on stdin
# It will log to stderr

echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}' | \
  ./target/debug/hwml_lsp_server 2>&1
```

This should produce LSP protocol responses on stdout and log messages on stderr.

## Reporting Issues

When reporting issues, include:

1. VSCode version
2. Extension version (check Extensions view)
3. LSP server output (from Output panel)
4. VSCode developer console output (Help → Toggle Developer Tools)
5. Steps to reproduce
6. Expected vs actual behavior
