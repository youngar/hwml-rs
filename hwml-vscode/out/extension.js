"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.deactivate = exports.activate = void 0;
const vscode_1 = require("vscode");
const vscode = require("vscode");
const node_1 = require("vscode-languageclient/node");
let client;
function activate(context) {
    const outputChannel = vscode.window.createOutputChannel('hwml-vscode');
    context.subscriptions.push(outputChannel);
    // Get the path to the language server.
    let serverOptions = {
        command: '/Users/andrewyoung/wsp/hwml-rust/target/debug/hwml_lsp_server'
    };
    // Options to control the language client
    let clientOptions = {
        // Register the server for plain text documents
        documentSelector: [{ scheme: 'file', language: 'hwml' }],
        synchronize: {
            // Notify the server about file changes to '.clientrc files contained in the workspace
            fileEvents: vscode_1.workspace.createFileSystemWatcher('**/.hwml')
        },
        outputChannel: outputChannel,
        revealOutputChannelOn: node_1.RevealOutputChannelOn.Info,
    };
    // Create the language client and start the client.
    client = new node_1.LanguageClient('hwml', 'hwml Language Server', serverOptions, clientOptions);
    // The command has been defined in the package.json file
    // Now provide the implementation of the command with registerCommand
    // The commandId parameter must match the command field in package.json
    let disposable = vscode.commands.registerCommand('hwml.helloworld', () => {
        // The code you place here will be executed every time your command is executed
        // Display a message box to the user
        vscode.window.showInformationMessage('Hello World!');
    });
    context.subscriptions.push(disposable);
    let restartCommand = vscode.commands.registerCommand('hwml.restart', () => {
        // The code you place here will be executed every time your command is executed
        // Display a message box to the user
        vscode.window.showInformationMessage('Restart!');
    });
    context.subscriptions.push(restartCommand);
    outputChannel.show();
    outputChannel.appendLine("qwertyuiop");
    vscode.window.showInformationMessage("hello from the client!", "yes", "no");
    vscode.window.showErrorMessage("hello");
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