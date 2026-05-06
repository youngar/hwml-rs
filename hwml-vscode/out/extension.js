"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.deactivate = exports.activate = void 0;
const path = require("path");
const vscode_1 = require("vscode");
const vscode = require("vscode");
const node_1 = require("vscode-languageclient/node");
let client;
function activate(context) {
    const outputChannel = vscode.window.createOutputChannel('HWML Language Server');
    context.subscriptions.push(outputChannel);
    // Get server path from configuration
    const config = vscode_1.workspace.getConfiguration('hwml');
    let serverPath = config.get('server_path', 'hwml_lsp_server');
    // If server_path is just a binary name (no path separators),
    // try to find it relative to the extension or in PATH
    if (!serverPath.includes('/') && !serverPath.includes('\\')) {
        // Try to find in workspace first (for development)
        const workspaceFolders = vscode_1.workspace.workspaceFolders;
        if (workspaceFolders && workspaceFolders.length > 0) {
            const wsPath = workspaceFolders[0].uri.fsPath;
            const localServerPath = path.join(wsPath, 'target', 'debug', 'hwml_lsp_server');
            const fs = require('fs');
            if (fs.existsSync(localServerPath)) {
                serverPath = localServerPath;
                outputChannel.appendLine(`Found LSP server in workspace: ${serverPath}`);
            }
        }
    }
    outputChannel.appendLine(`Using LSP server: ${serverPath}`);
    // Get the path to the language server.
    let serverOptions = {
        command: serverPath
    };
    // Options to control the language client
    let clientOptions = {
        // Register the server for hwml documents
        documentSelector: [{ scheme: 'file', language: 'hwml' }],
        synchronize: {
            // Notify the server about file changes to hwml.toml files in the workspace
            fileEvents: vscode_1.workspace.createFileSystemWatcher('**/hwml.toml')
        },
        outputChannel: outputChannel,
        revealOutputChannelOn: node_1.RevealOutputChannelOn.Info,
    };
    // Create the language client and start the client.
    client = new node_1.LanguageClient('hwml', 'HWML Language Server', serverOptions, clientOptions);
    // Register restart command
    let restartCommand = vscode.commands.registerCommand('hwml.restart', async () => {
        if (client) {
            outputChannel.appendLine('Restarting HWML Language Server...');
            await client.stop();
            await client.start();
            vscode.window.showInformationMessage('HWML Language Server restarted');
        }
    });
    context.subscriptions.push(restartCommand);
    // Start the client. This will also launch the server
    client.start();
}
exports.activate = activate;
function deactivate() {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
exports.deactivate = deactivate;
//# sourceMappingURL=extension.js.map