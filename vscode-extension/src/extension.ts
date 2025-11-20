import * as vscode from 'vscode';
import { PlaygroundPanel } from './playgroundPanel';
import { LimbooleExecutor } from './executors/limbooleExecutor';
import { Z3Executor } from './executors/z3Executor';
import { NuXmvExecutor } from './executors/nuxmvExecutor';
import { SpectraExecutor } from './executors/spectraExecutor';

export function activate(context: vscode.ExtensionContext) {
    console.log('FM Playground extension is now active!');

    // Register command to open the playground webview
    const openPlaygroundCommand = vscode.commands.registerCommand(
        'fm-playground.openPlayground',
        () => {
            PlaygroundPanel.createOrShow(context.extensionUri);
        }
    );

    // Register command to run Limboole
    const runLimbooleCommand = vscode.commands.registerCommand(
        'fm-playground.runLimboole',
        async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor) {
                vscode.window.showErrorMessage('No active text editor');
                return;
            }
            const code = editor.document.getText();
            const executor = new LimbooleExecutor();
            await executor.execute(code);
        }
    );

    // Register command to run Z3
    const runZ3Command = vscode.commands.registerCommand(
        'fm-playground.runZ3',
        async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor) {
                vscode.window.showErrorMessage('No active text editor');
                return;
            }
            const code = editor.document.getText();
            const executor = new Z3Executor();
            await executor.execute(code);
        }
    );

    // Register command to run nuXmv
    const runNuXmvCommand = vscode.commands.registerCommand(
        'fm-playground.runNuXmv',
        async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor) {
                vscode.window.showErrorMessage('No active text editor');
                return;
            }
            const code = editor.document.getText();
            const executor = new NuXmvExecutor();
            await executor.execute(code);
        }
    );

    // Register command to run Spectra
    const runSpectraCommand = vscode.commands.registerCommand(
        'fm-playground.runSpectra',
        async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor) {
                vscode.window.showErrorMessage('No active text editor');
                return;
            }
            const code = editor.document.getText();
            const executor = new SpectraExecutor();
            await executor.execute(code);
        }
    );

    context.subscriptions.push(
        openPlaygroundCommand,
        runLimbooleCommand,
        runZ3Command,
        runNuXmvCommand,
        runSpectraCommand
    );

    // Register configuration change listener
    vscode.workspace.onDidChangeConfiguration((e) => {
        if (e.affectsConfiguration('fm-playground')) {
            vscode.window.showInformationMessage(
                'FM Playground configuration changed. Please reload the window for changes to take effect.'
            );
        }
    });
}

export function deactivate() {
    console.log('FM Playground extension is now deactivated');
}
