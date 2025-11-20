import * as vscode from 'vscode';
import axios from 'axios';

export class SpectraExecutor {
    private outputChannel: vscode.OutputChannel;

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel('FM Playground - Spectra');
    }

    async execute(code: string): Promise<void> {
        const config = vscode.workspace.getConfiguration('fm-playground');
        const apiUrl = config.get<string>('spectra.apiUrl', 'http://localhost:8080');

        this.outputChannel.show(true);
        this.outputChannel.appendLine('Running Spectra...');
        this.outputChannel.appendLine('─'.repeat(50));

        try {
            const response = await axios.post(`${apiUrl}/spectra`, {
                code,
            });

            this.outputChannel.appendLine('Result:');
            this.outputChannel.appendLine(JSON.stringify(response.data, null, 2));
            
            vscode.window.showInformationMessage('Spectra execution completed!');
        } catch (error: any) {
            const errorMessage = error.response?.data?.message || error.message || 'Unknown error';
            this.outputChannel.appendLine(`Error: ${errorMessage}`);
            vscode.window.showErrorMessage(`Spectra execution failed: ${errorMessage}`);
        }

        this.outputChannel.appendLine('─'.repeat(50));
    }
}
