# Langium-based Language Server Implementation

This guide walks you through implementing a new language server using the [Langium framework](https://langium.org/) for FM Playground.

## Overview

Langium is a TypeScript-based framework for building domain-specific languages with full Language Server Protocol (LSP) support. It generates type-safe ASTs and provides extensive customization options for language features.

## Getting Started

Follow the steps from the [Langium documentation](https://langium.org/docs/learn/workflow/) to set up your development environment. Ensure you have Node.js and npm installed. Then create a new Langium project outside the FM Playground project directory.

[Scaffolding a Langium project](https://langium.org/docs/learn/workflow/scaffold/), offers an interactive CLI to create a new language project. Based on your selection, it can generate different parts you want to include in your language server, such as VS Code extension, CLI, Web worker, etc. For FM Playground, we will focus on the _Web worker_. You can include all of the options, later we will copy the relevant files to the FM Playground project.

### Generate artifacts

Following all the steps in the Langium documentation, you will have a new directory with the following structure:

```bash title="my-langium-project" linenums="1"  hl_lines="1"
my-langium-project/
├── ...                             # Other generated files
├── src/                            # Source files
│   ├── ...                         # Other language files
│   ├── language/                   # Language-specific files
│   │   ├── generated/              # Generated files
│   │   ├── my-language.langium     # Language grammar
│   │   ├── my-language-module.ts   # Dependency injection
│   │   ├── ...                     # Other language files e.g., validators,
├── syntaxes/                       # TextMate grammar files
│   └── my-language.tmLanguage.json # Syntax highlighting rules
├── langium-config.json             # Langium configuration
├── language-configuration.json     # Language features configuration
└── ...                             # Other files
```

## Integrating with FM Playground

Now that you have a basic Langium project, we will integrate it into FM Playground.

### Step 1: Copy Files to FM Playground

- Create a new directory in `frontend/tools/your-language/langium/` (replace `your-language` with your language name).
- Copy the `*config*.json` files (line 12,13) from your Langium project to `frontend/tools/your-language/langium/config/`.
- Copy the `language` (line 4) directory to `frontend/tools/your-language/langium/ls/`. (including generated files)
- Copy the `syntaxes` (line 10) directory to `frontend/tools/your-language/langium/syntaxes/`.

### Step 2: Create Worker

- Create a new directory `frontend/tools/your-language/langium/worker/`. This will contain the worker setup for your language server.
- Now, create three files in the `worker` directory:
  - `your-language-server.ts`: This will be the main worker file.
  - `your-language-server-port.ts`: This will handle the port-based worker setup.
  - `your-language-server-start.ts`: This will contain the startup logic for your language server.

Now, implement the worker files as follows:

```typescript title="your-language-server.ts" linenums="1"
/// <reference lib="WebWorker" />
import { start } from "./your-language-server-start.js";
declare const self: DedicatedWorkerGlobalScope;
start(self, "your-language-server");
```

This file initializes the worker and starts the language server.

```typescript title="your-language-server-port.ts" linenums="1"
/// <reference lib="WebWorker" />
import { start } from "./your-language-server-start.js";
declare const self: DedicatedWorkerGlobalScope;
self.onmessage = async (event: MessageEvent) => {
  const data = event.data;
  console.log(event.data);
  if (data.port !== undefined) {
    start(data.port, "your-language-server-port");
    setTimeout(() => {
      self.postMessage("started");
    }, 1000);
  }
};
```

This file listens for messages from the main thread and starts the language server with the provided port.

```typescript title="your-language-server-start.ts" linenums="1"
/// <reference lib="WebWorker" />

import { EmptyFileSystem } from "langium";
import { startLanguageServer } from "langium/lsp";
import {
  BrowserMessageReader,
  BrowserMessageWriter,
  createConnection,
} from "vscode-languageserver/browser.js";
import { createYourLanguageServices } from "../ls/your-language-module.js";
export const start = (
  port: MessagePort | DedicatedWorkerGlobalScope,
  name: string
) => {
  console.log(`Starting ${name}...`);
  /* browser specific setup code */
  const messageReader = new BrowserMessageReader(port);
  const messageWriter = new BrowserMessageWriter(port);
  const connection = createConnection(messageReader, messageWriter);
  // Inject the shared services and language-specific services
  const { shared } = createYourLanguageServices({
    connection,
    ...EmptyFileSystem,
  });
  // Start the language server with the shared services
  startLanguageServer(shared);
};
```

This file sets up the language server connection and starts the server with the shared services.

### Step 3: Configure Monaco Editor

Now, we need to configure the Monaco Editor to use the new language server. The common configuration file for Monaco Editor is `frontend/tools/common/lspWrapperConfig.ts`.

- Import the necessary files at the top of the file:

```typescript title="lspWrapperConfig.ts" linenums="1"
// Your tool specific imports
import workerPortUrlYourLanguage from "@/../tools/your-language/langium/worker/your-language-server-port?worker&url";
import yourLanguageLanguageConfig from "@/../tools/your-language/langium/config/language-configuration.json?raw";
import responseYourlanguageTm from "@/../tools/your-language/langium/syntaxes/your-language.tmLanguage.json?raw";
```

- Add the worker factory function to load your language worker:

```typescript title="lspWrapperConfig.ts" linenums="1"
const loadYourLanguageWorkerPort = () => {
  return new Worker(workerPortUrlYourLanguage, {
    type: "module",
    name: "YourLanguage Server Port",
  });
};
```

- In the `createLangiumGlobalConfig` function, add your language configuration:

```typescript title="lspWrapperConfig.ts" linenums="1"
...
// Load the worker ports for your language
const yourLanguageExtensionFilesOrContents = new Map<string, string | URL>();
yourLanguageExtensionFilesOrContents.set(
    `/your-language-configuration.json`,
    yourLanguageLanguageConfig
);
yourLanguageExtensionFilesOrContents.set(
    `/your-language-grammar.json`,
    responseYourLanguageTm
);

// Load worker
...
const yourLanguageWorkerPort = loadYourLanguageWorkerPort();

// Create message channel
const yourLanguageChannel = new MessageChannel();
yourLanguageWorkerPort.postMessage(
    { port: yourLanguageChannel.port2 },
    [yourLanguageChannel.port2]
);

// Create message readers and writers for each channel
const yourLanguageReader = new BrowserMessageReader(
    yourLanguageChannel.port1
);
const yourLanguageWriter = new BrowserMessageWriter(
    yourLanguageChannel.port1
);

return {
    id: 42,
    ... // existing config
    editorAppConfig: {
      extensions:[{
        config: {
          name: 'your-language-example',
          publisher: 'your-publisher',
          version: '1.0.0',
          engine: {
            vscode: '*',
          },
          contributes: {
            languages: [
              {
                id: 'your-language',
                extensions: ['.yourlang'],
                aliases: ['YourLanguage', 'your-language'],
                configuration: `./your-language-configuration.json`,
              },
            ],
            grammars: [
              {
                language: 'your-language',
                scopeName: 'source.yourlanguage',
                path: `./your-language-grammar.json`,
              },
            ],
          },
        },
        filesOrContents: yourLanguageExtensionFilesOrContents,
      },
        ... // existing extensions
      ],
    },
    languageClientConfigs: {
      yourLanguage: {
        languageId: 'your-language',
        connection: {
          options: {
            $type: 'WorkerDirect',
            worker: loadYourLanguageWorkerPort,
            messagePort: yourLanguageChannel.port1,
          },
          messageTransports: { 
            reader: yourLanguageReader, 
            writer: yourLanguageWriter
          },
      },
      ... // existing language clients
      },
  },
}
```

This configuration code demonstrates the complete integration of a Langium-based language server into FM Playground's Monaco Editor. Let's break down each section:

#### 1. Extension Files Mapping
```typescript
const yourLanguageExtensionFilesOrContents = new Map<string, string | URL>();
yourLanguageExtensionFilesOrContents.set(
    `/your-language-configuration.json`,
    yourLanguageLanguageConfig
);
yourLanguageExtensionFilesOrContents.set(
    `/your-language-grammar.json`,
    responseYourLanguageTm
);
```

This creates a virtual file system for Monaco Editor, mapping file paths to their content:
- **Language configuration**: Defines editor behaviors like bracket matching, auto-closing pairs, and comment styles
- **TextMate grammar**: Provides syntax highlighting rules that colorize your language's tokens

#### 2. Worker Initialization
```typescript
const yourLanguageWorkerPort = loadYourLanguageWorkerPort();
```

Creates a new Web Worker instance running your language server. Web Workers are crucial because they:
- Run language processing in a separate thread
- Prevent UI blocking during heavy parsing/validation
- Isolate language server crashes from the main application

#### 3. Inter-thread Communication Setup
```typescript
const yourLanguageChannel = new MessageChannel();
yourLanguageWorkerPort.postMessage(
    { port: yourLanguageChannel.port2 },
    [yourLanguageChannel.port2]
);
```

Establishes a bidirectional communication pipe:
- **MessageChannel**: Creates two connected ports for communication
- **Port transfer**: Sends one end to the worker, keeping the other in the main thread
- **Structured messaging**: Enables reliable, type-safe communication between threads

#### 4. Language Server Protocol Transport Layer
```typescript
const yourLanguageReader = new BrowserMessageReader(yourLanguageChannel.port1);
const yourLanguageWriter = new BrowserMessageWriter(yourLanguageChannel.port1);
```

Creates LSP-compliant message transports:
- **Reader**: Processes incoming LSP messages from the language server
- **Writer**: Sends LSP requests/notifications to the language server
- **Protocol compliance**: Ensures compatibility with standard LSP implementations

#### 5. VS Code Extension Simulation
```typescript
editorAppConfig: {
  extensions:[{
    config: {
      name: 'your-language-example',
      publisher: 'your-publisher',
      version: '1.0.0',
      engine: { vscode: '*' },
      contributes: {
        languages: [...],
        grammars: [...]
      }
    },
    filesOrContents: yourLanguageExtensionFilesOrContents,
  }]
}
```

Mimics a VS Code extension's `package.json` structure:
- **Metadata**: Extension identification and versioning
- **Language contribution**: Registers file extensions, aliases, and configuration
- **Grammar contribution**: Associates the language with its TextMate grammar
- **File mapping**: Links virtual files to their content

#### 6. Language Client Configuration
```typescript
languageClientConfigs: {
  yourLanguage: {
    languageId: 'your-language',
    connection: {
      options: {
        $type: 'WorkerDirect',
        worker: loadYourLanguageWorkerPort,
        messagePort: yourLanguageChannel.port1,
      },
      messageTransports: { 
        reader: yourLanguageReader, 
        writer: yourLanguageWriter
      },
    },
  },
}
```

Configures the LSP client for your language:
- **Language identification**: Maps to the language ID in the extension config
- **Connection type**: Specifies direct worker communication
- **Worker factory**: Function to create new worker instances when needed
- **Message handling**: Links the reader/writer pair for LSP communication


## Resources

- [Langium Documentation](https://langium.org/)

_← Back to [Language Server Integration](./language-servers.md)_
