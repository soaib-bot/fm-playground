import * as vscode from 'vscode';
import axios from 'axios';

export class NuXmvExecutor {
    private outputChannel: vscode.OutputChannel;

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel('FM Playground - nuXmv');
    }

    async execute(code: string): Promise<void> {
        const config = vscode.workspace.getConfiguration('fm-playground');
        const apiUrl = config.get<string>('nuxmv.apiUrl', 'http://localhost:8080');

        this.outputChannel.show(true);
        this.outputChannel.appendLine('Running nuXmv...');
        this.outputChannel.appendLine('─'.repeat(50));

        try {
            const response = await axios.post(`${apiUrl}/nuxmv`, {
                code,
            });

            this.outputChannel.appendLine('Result:');
            this.outputChannel.appendLine(JSON.stringify(response.data, null, 2));
            
            vscode.window.showInformationMessage('nuXmv execution completed!');
        } catch (error: any) {
            const errorMessage = error.response?.data?.message || error.message || 'Unknown error';
            this.outputChannel.appendLine(`Error: ${errorMessage}`);
            vscode.window.showErrorMessage(`nuXmv execution failed: ${errorMessage}`);
        }

        this.outputChannel.appendLine('─'.repeat(50));
    }
}
