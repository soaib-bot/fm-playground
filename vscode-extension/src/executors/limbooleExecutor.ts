import * as vscode from 'vscode';
import axios from 'axios';

export class LimbooleExecutor {
    private outputChannel: vscode.OutputChannel;

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel('FM Playground - Limboole');
    }

    async execute(code: string): Promise<void> {
        const config = vscode.workspace.getConfiguration('fm-playground');
        const apiUrl = config.get<string>('limboole.apiUrl', 'http://localhost:8055');

        this.outputChannel.show(true);
        this.outputChannel.appendLine('Running Limboole...');
        this.outputChannel.appendLine('─'.repeat(50));

        try {
            const response = await axios.post(`${apiUrl}/diff-limboole`, {
                code,
            });

            this.outputChannel.appendLine('Result:');
            this.outputChannel.appendLine(JSON.stringify(response.data, null, 2));
            
            vscode.window.showInformationMessage('Limboole execution completed!');
        } catch (error: any) {
            const errorMessage = error.response?.data?.message || error.message || 'Unknown error';
            this.outputChannel.appendLine(`Error: ${errorMessage}`);
            vscode.window.showErrorMessage(`Limboole execution failed: ${errorMessage}`);
        }

        this.outputChannel.appendLine('─'.repeat(50));
    }
}
