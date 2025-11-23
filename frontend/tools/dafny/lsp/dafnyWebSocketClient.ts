import { BrowserMessageReader, BrowserMessageWriter } from 'vscode-languageclient/browser.js';

export class WebSocketToMessagePortAdapter {
    private websocket: WebSocket;
    private messagePort1: MessagePort;
    private messagePort2: MessagePort;

    constructor(url: string) {
        // Create a MessageChannel to bridge WebSocket and MessagePort
        const channel = new MessageChannel();
        this.messagePort1 = channel.port1;
        this.messagePort2 = channel.port2;

        this.websocket = new WebSocket(url);
        this.setupBridge();
    }

    private setupBridge() {
        // Forward messages from WebSocket to MessagePort
        this.websocket.onmessage = (event) => {
            try {
                const message = JSON.parse(event.data);
                this.messagePort1.postMessage(message);
            } catch (error) {
                console.error('Failed to parse Dafny LSP WebSocket message:', error);
            }
        };

        // Forward messages from MessagePort to WebSocket
        this.messagePort2.onmessage = (event) => {
            if (this.websocket.readyState === WebSocket.OPEN) {
                this.websocket.send(JSON.stringify(event.data));
            }
        };

        this.websocket.onopen = () => {
            this.messagePort2.start();
        };

        this.websocket.onerror = (error) => {
            console.error('Dafny LSP WebSocket error:', error);
        };

        this.websocket.onclose = () => {
            this.messagePort1.close();
            this.messagePort2.close();
        };
    }

    getMessagePort(): MessagePort {
        return this.messagePort1;
    }

    close() {
        this.websocket.close();
        this.messagePort1.close();
        this.messagePort2.close();
    }
}

// Create a fake worker that encapsulates the WebSocket connection
export class DafnyWebSocketWorker {
    private websocket: WebSocket;
    private isConnected = false;
    private pendingMessages: any[] = [];
    private connectedPort: MessagePort | null = null;

    constructor(url: string = 'ws://localhost:5173/lsp-dafny/lsp') {
        this.websocket = new WebSocket(url);
        this.setupWebSocket();
    }

    private setupWebSocket() {
        this.websocket.onopen = () => {
            this.isConnected = true;

            // Send any pending messages
            if (this.connectedPort && this.pendingMessages.length > 0) {
                this.pendingMessages.forEach(msg => {
                    this.websocket.send(JSON.stringify(msg));
                });
                this.pendingMessages = [];
            }
        };

        this.websocket.onmessage = (event) => {
            try {
                const message = JSON.parse(event.data);

                if (this.connectedPort) {
                    this.connectedPort.postMessage(message);
                }
            } catch (error) {

            }
        };

        this.websocket.onerror = (error) => {
            console.error('Dafny LSP WebSocket error:', error);
        };

        this.websocket.onclose = () => {
            this.isConnected = false;
        };
    }

    postMessage(data: any, transfer?: Transferable[]) {
        // Simulate worker behavior - when a port is passed, start the connection
        if (data.port && transfer && transfer[0] === data.port) {
            this.connectedPort = data.port;

            // Listen for messages from the language client
            data.port.onmessage = (event: MessageEvent) => {

                if (this.isConnected) {
                    this.websocket.send(JSON.stringify(event.data));
                } else {
                    // Queue messages until connected
                    this.pendingMessages.push(event.data);
                }
            };

            data.port.start();
        }
    }

    terminate() {
        if (this.websocket) {
            this.websocket.close();
        }
        if (this.connectedPort) {
            this.connectedPort.close();
        }
    }
}

export function createDafnyMessageTransports(url: string = 'ws://localhost:5173/lsp-dafny/lsp') {
    const adapter = new WebSocketToMessagePortAdapter(url);
    const messagePort = adapter.getMessagePort();

    const reader = new BrowserMessageReader(messagePort);
    const writer = new BrowserMessageWriter(messagePort);

    return { reader, writer, adapter };
}

export function createDafnyWebSocketWorker(url: string = 'ws://localhost:5173/lsp-dafny/lsp') {
    return new DafnyWebSocketWorker(url);
}
