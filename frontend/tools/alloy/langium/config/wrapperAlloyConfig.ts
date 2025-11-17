import getKeybindingsServiceOverride from '@codingame/monaco-vscode-keybindings-service-override';
import getLifecycleServiceOverride from '@codingame/monaco-vscode-lifecycle-service-override';
import getLocalizationServiceOverride from '@codingame/monaco-vscode-localization-service-override';
import { createDefaultLocaleConfiguration } from 'monaco-languageclient/vscode/services';
import { LogLevel } from 'vscode/services';
import { BrowserMessageReader, BrowserMessageWriter } from 'vscode-languageclient/browser.js';
import { WrapperConfig } from 'monaco-editor-wrapper';
import alloyLanguageConfig from './language-configuration.json?raw';
import responseAlloyTm from '../syntaxes/alloy.tmLanguage.json?raw';
import { configureMonacoWorkers } from '../utils';
import workerPortUrlAlloy from '../worker/alloy-server-port?worker&url';

const loadLangiumWorkerPort = () => {
    return new Worker(workerPortUrlAlloy, {
        type: 'module',
        name: 'Alloy Server Port',
    });
};

export const createLangiumAlloyConfig = async (): Promise<WrapperConfig> => {
    const extensionFilesOrContents = new Map<string, string | URL>();
    extensionFilesOrContents.set(`/alloy-configuration.json`, alloyLanguageConfig);
    extensionFilesOrContents.set(`/alloy-grammar.json`, responseAlloyTm);

    const alloyWorkerPort = loadLangiumWorkerPort();

    const channel = new MessageChannel();
    alloyWorkerPort.postMessage({ port: channel.port2 }, [channel.port2]);

    const reader = new BrowserMessageReader(channel.port1);
    const writer = new BrowserMessageWriter(channel.port1);

    return {
        logLevel: LogLevel.Error,
        serviceConfig: {
            userServices: {
                ...getKeybindingsServiceOverride(),
                ...getLifecycleServiceOverride(),
                ...getLocalizationServiceOverride(createDefaultLocaleConfiguration()),
            },
        },
        editorAppConfig: {
            $type: 'extended',
            editorOptions: {
                minimap: {
                    enabled: false,
                },
                automaticLayout: true,
                mouseWheelZoom: true,
                bracketPairColorization: {
                    enabled: true,
                    independentColorPoolPerBracketType: true,
                },
                glyphMargin: false,
            },
            codeResources: {
                main: {
                    text: '',
                    fileExt: 'als',
                },
            },
            useDiffEditor: false,
            extensions: [
                {
                    config: {
                        name: 'alloy',
                        publisher: 'soaibuzzaman',
                        version: '1.0.0',
                        engine: {
                            vscode: '*',
                        },
                        contributes: {
                            languages: [
                                {
                                    id: 'alloy',
                                    extensions: ['.als'],
                                    aliases: ['alloy', 'Alloy'],
                                    configuration: `./alloy-configuration.json`,
                                },
                            ],
                            grammars: [
                                {
                                    language: 'alloy',
                                    scopeName: 'source.alloy',
                                    path: `./alloy-grammar.json`,
                                },
                            ],
                        },
                    },
                    filesOrContents: extensionFilesOrContents,
                },
            ],
            userConfiguration: {
                json: JSON.stringify({
                    'workbench.colorTheme': 'Default Light Modern',
                    'editor.guides.bracketPairsHorizontal': 'active',
                    'editor.wordBasedSuggestions': 'off',
                    'editor.experimental.asyncTokenization': true,
                    'editor.semanticHighlighting.enabled': true,
                }),
            },
            monacoWorkerFactory: configureMonacoWorkers,
        },
        languageClientConfigs: {
            alloy: {
                languageId: 'alloy',
                connection: {
                    options: {
                        $type: 'WorkerDirect',
                        worker: alloyWorkerPort,
                        messagePort: channel.port1,
                    },
                    messageTransports: { reader, writer },
                },
            },
        },
    };
};
