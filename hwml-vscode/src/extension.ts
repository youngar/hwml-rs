import * as path from 'path';
import { workspace, ExtensionContext } from 'vscode';
import * as vscode from 'vscode';

import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    TransportKind, RevealOutputChannelOn

} from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: ExtensionContext) {
    const outputChannel = vscode.window.createOutputChannel('HWML Language Server');
    context.subscriptions.push(outputChannel);

    // Get server path from configuration
    const config = workspace.getConfiguration('hwml');
    let serverPath = config.get<string>('server_path', 'hwml_lsp_server');

    // If server_path is just a binary name (no path separators),
    // try to find it relative to the extension or in PATH
    if (!serverPath.includes('/') && !serverPath.includes('\\')) {
        // Try to find in workspace first (for development)
        const workspaceFolders = workspace.workspaceFolders;
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
    let serverOptions: ServerOptions = {
        command: serverPath
    };

    // Options to control the language client
    let clientOptions: LanguageClientOptions = {
        // Register the server for hwml documents
        documentSelector: [{ scheme: 'file', language: 'hwml' }],
        synchronize: {
            // Notify the server about file changes to hwml.toml files in the workspace
            fileEvents: workspace.createFileSystemWatcher('**/hwml.toml')
        },
        outputChannel: outputChannel,
        revealOutputChannelOn: RevealOutputChannelOn.Info,
    };

    // Create the language client and start the client.
    client = new LanguageClient(
        'hwml',
        'HWML Language Server',
        serverOptions,
        clientOptions
    );

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

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
