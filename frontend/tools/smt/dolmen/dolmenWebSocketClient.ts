// WebSocket Language Client for Dolmen LSP
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
                console.error('Failed to parse WebSocket message:', error);
            }
        };

        // Forward messages from MessagePort to WebSocket
        this.messagePort2.onmessage = (event) => {
            if (this.websocket.readyState === WebSocket.OPEN) {
                this.websocket.send(JSON.stringify(event.data));
            }
        };

        this.websocket.onopen = () => {
            console.log('Dolmen LSP WebSocket connected');
            this.messagePort2.start();
        };

        this.websocket.onerror = (error) => {
            console.error('Dolmen LSP WebSocket error:', error);
        };

        this.websocket.onclose = () => {
            console.log('Dolmen LSP WebSocket disconnected');
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
export class DolmenWebSocketWorker {
    private websocket: WebSocket;
    private isConnected = false;
    private pendingMessages: any[] = [];
    private connectedPort: MessagePort | null = null;

    constructor(url: string = 'ws://localhost:5173/dolmen-lsp') {
        console.log('Creating Dolmen WebSocket Worker with URL:', url);
        this.websocket = new WebSocket(url);
        this.setupWebSocket();
    }

    private setupWebSocket() {
        this.websocket.onopen = () => {
            console.log('Dolmen LSP WebSocket connected in worker');
            this.isConnected = true;

            // Send any pending messages
            if (this.connectedPort && this.pendingMessages.length > 0) {
                console.log(`Sending ${this.pendingMessages.length} pending messages`);
                this.pendingMessages.forEach(msg => {
                    console.log('Sending pending message:', msg);
                    this.websocket.send(JSON.stringify(msg));
                });
                this.pendingMessages = [];
            }
        };

        this.websocket.onmessage = (event) => {
            try {
                const message = JSON.parse(event.data);
                console.log('Received message from Dolmen LSP:', message);

                if (this.connectedPort) {
                    this.connectedPort.postMessage(message);
                } else {
                    console.warn('Received message but no connected port:', message);
                }
            } catch (error) {
                console.error('Failed to parse WebSocket message:', error, 'Raw data:', event.data);
            }
        };

        this.websocket.onerror = (error) => {
            console.error('Dolmen LSP WebSocket error:', error);
        };

        this.websocket.onclose = (event) => {
            console.log('Dolmen LSP WebSocket disconnected:', event.code, event.reason);
            this.isConnected = false;
        };
    }

    postMessage(data: any, transfer?: Transferable[]) {
        console.log('Worker postMessage called with:', data, transfer);

        // Simulate worker behavior - when a port is passed, start the connection
        if (data.port && transfer && transfer[0] === data.port) {
            console.log('Setting up port connection for Dolmen worker');
            this.connectedPort = data.port;

            // Listen for messages from the language client
            data.port.onmessage = (event: MessageEvent) => {
                console.log('Sending message to Dolmen LSP:', event.data);

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
        console.log('Terminating Dolmen WebSocket Worker');
        if (this.websocket) {
            this.websocket.close();
        }
        if (this.connectedPort) {
            this.connectedPort.close();
        }
    }
}

export function createDolmenMessageTransports(url: string = 'ws://localhost:5173/dolmen-lsp') {
    const adapter = new WebSocketToMessagePortAdapter(url);
    const messagePort = adapter.getMessagePort();

    const reader = new BrowserMessageReader(messagePort);
    const writer = new BrowserMessageWriter(messagePort);

    return { reader, writer, adapter };
}

export function createDolmenWebSocketWorker(url: string = 'ws://localhost:5173/dolmen-lsp') {
    return new DolmenWebSocketWorker(url);
}
