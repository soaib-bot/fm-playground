import * as vscode from 'vscode';

export class PlaygroundPanel {
    public static currentPanel: PlaygroundPanel | undefined;
    private readonly _panel: vscode.WebviewPanel;
    private readonly _extensionUri: vscode.Uri;
    private _disposables: vscode.Disposable[] = [];

    public static createOrShow(extensionUri: vscode.Uri) {
        const column = vscode.window.activeTextEditor
            ? vscode.window.activeTextEditor.viewColumn
            : undefined;

        // If we already have a panel, show it.
        if (PlaygroundPanel.currentPanel) {
            PlaygroundPanel.currentPanel._panel.reveal(column);
            return;
        }

        // Otherwise, create a new panel.
        const panel = vscode.window.createWebviewPanel(
            'fmPlayground',
            'FM Playground',
            column || vscode.ViewColumn.One,
            {
                enableScripts: true,
                retainContextWhenHidden: true,
                localResourceRoots: [extensionUri]
            }
        );

        PlaygroundPanel.currentPanel = new PlaygroundPanel(panel, extensionUri);
    }

    private constructor(panel: vscode.WebviewPanel, extensionUri: vscode.Uri) {
        this._panel = panel;
        this._extensionUri = extensionUri;

        // Set the webview's initial html content
        this._update();

        // Listen for when the panel is disposed
        this._panel.onDidDispose(() => this.dispose(), null, this._disposables);

        // Handle messages from the webview
        this._panel.webview.onDidReceiveMessage(
            (message) => {
                switch (message.command) {
                    case 'alert':
                        vscode.window.showInformationMessage(message.text);
                        return;
                    case 'error':
                        vscode.window.showErrorMessage(message.text);
                        return;
                }
            },
            null,
            this._disposables
        );
    }

    public dispose() {
        PlaygroundPanel.currentPanel = undefined;

        // Clean up our resources
        this._panel.dispose();

        while (this._disposables.length) {
            const x = this._disposables.pop();
            if (x) {
                x.dispose();
            }
        }
    }

    private _update() {
        const webview = this._panel.webview;
        this._panel.webview.html = this._getHtmlForWebview(webview);
    }

    private _getHtmlForWebview(webview: vscode.Webview) {
        return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FM Playground</title>
    <style>
        body {
            font-family: var(--vscode-font-family);
            color: var(--vscode-foreground);
            background-color: var(--vscode-editor-background);
            padding: 20px;
        }
        .container {
            max-width: 1200px;
            margin: 0 auto;
        }
        h1 {
            color: var(--vscode-foreground);
            border-bottom: 1px solid var(--vscode-panel-border);
            padding-bottom: 10px;
        }
        .tool-section {
            margin: 20px 0;
            padding: 15px;
            border: 1px solid var(--vscode-panel-border);
            border-radius: 5px;
        }
        .tool-section h2 {
            margin-top: 0;
        }
        button {
            background-color: var(--vscode-button-background);
            color: var(--vscode-button-foreground);
            border: none;
            padding: 8px 16px;
            margin: 5px 5px 5px 0;
            cursor: pointer;
            border-radius: 2px;
        }
        button:hover {
            background-color: var(--vscode-button-hoverBackground);
        }
        .info {
            color: var(--vscode-descriptionForeground);
            font-size: 0.9em;
            margin-top: 10px;
        }
    </style>
</head>
<body>
    <div class="container">
        <h1>🎮 FM Playground</h1>
        <p>Welcome to the Formal Methods Playground VSCode extension!</p>
        
        <div class="tool-section">
            <h2>🔧 Available Tools</h2>
            <p>Use the commands below to run formal verification tools on your code:</p>
            
            <div style="margin: 15px 0;">
                <h3>Limboole</h3>
                <p class="info">Boolean satisfiability solver</p>
                <button onclick="runCommand('fm-playground.runLimboole')">Run Limboole</button>
            </div>
            
            <div style="margin: 15px 0;">
                <h3>Z3 (SMT Solver)</h3>
                <p class="info">Satisfiability Modulo Theories solver</p>
                <button onclick="runCommand('fm-playground.runZ3')">Run Z3</button>
            </div>
            
            <div style="margin: 15px 0;">
                <h3>nuXmv</h3>
                <p class="info">Symbolic model checker</p>
                <button onclick="runCommand('fm-playground.runNuXmv')">Run nuXmv</button>
            </div>
            
            <div style="margin: 15px 0;">
                <h3>Spectra</h3>
                <p class="info">Reactive synthesis tool</p>
                <button onclick="runCommand('fm-playground.runSpectra')">Run Spectra</button>
            </div>
        </div>
        
        <div class="tool-section">
            <h2>📝 Quick Start</h2>
            <ol>
                <li>Create a new file with the appropriate extension (.limboole, .smt2, .smv, .spectra)</li>
                <li>Write your formal specification</li>
                <li>Run the corresponding command from the Command Palette (Ctrl+Shift+P / Cmd+Shift+P)</li>
                <li>View the results in the output panel</li>
            </ol>
        </div>
        
        <div class="tool-section">
            <h2>⚙️ Configuration</h2>
            <p>Configure API endpoints in VSCode settings (File > Preferences > Settings > Extensions > FM Playground)</p>
        </div>
    </div>
    
    <script>
        const vscode = acquireVsCodeApi();
        
        function runCommand(command) {
            vscode.postMessage({
                command: 'alert',
                text: 'Please use the Command Palette to run this command, or run it directly in a file with the correct extension.'
            });
        }
    </script>
</body>
</html>`;
    }
}
