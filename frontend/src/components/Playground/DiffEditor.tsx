import { useState, useRef, useEffect } from 'react';
import * as monacoEditor from 'monaco-editor';
import { DiffEditor } from '@monaco-editor/react';
import { useAtom } from 'jotai';
import { editorValueAtom, languageAtom, lineToHighlightAtom } from '@/atoms';
import { fmpConfig, languageConfigMap } from '@/ToolMaps';
import '@/assets/style/Playground.css';

interface DiffCodeEditorProps {
    height: string;
    editorTheme: string;
    originalValue?: string;
    modifiedValue?: string;
    readOnly?: boolean;
}

const CodeDiffEditor: React.FC<DiffCodeEditorProps> = (props: DiffCodeEditorProps) => {
    const [editorValue, setEditorValue] = useAtom(editorValueAtom);
    const diffEditorRef = useRef<monacoEditor.editor.IStandaloneDiffEditor | null>(null);
    const [language, setLanguage] = useAtom(languageAtom);
    const [lineToHighlight, setLineToHighlight] = useAtom(lineToHighlightAtom);
    const [decorationIds, setDecorationIds] = useState<string[]>([]);

    /**
     * Sets the editor value when the editorValue prop changes.
     */
    useEffect(() => {
        setEditorValue(editorValue);
    }, [editorValue]);

    /**
     * Sets the language when the language prop changes.
     */
    useEffect(() => {
        setLanguage(language);
    }, [language.id]);

    useEffect(() => {
        if (diffEditorRef.current) {
            const modifiedEditor = diffEditorRef.current.getModifiedEditor();
            if (lineToHighlight !== null && lineToHighlight.length > 0 && modifiedEditor) {
                const decorations = lineToHighlight.map((line) => {
                    return {
                        range: new window.monaco.Range(line, 1, line, 1),
                        options: {
                            isWholeLine: true,
                            className: 'lineHighlight',
                            glyphMarginClassName: 'lineHighlightGlyph',
                        },
                    };
                });
                const newDecorationIds = modifiedEditor.deltaDecorations(decorationIds, decorations);
                setDecorationIds(newDecorationIds);
            } else if (modifiedEditor) {
                // Remove all decorations
                const newDecorationIds = modifiedEditor.deltaDecorations(decorationIds, []);
                setDecorationIds(newDecorationIds);
            }
        }
    }, [lineToHighlight]);

    // Register the language configuration for each tool
    function handleDiffEditorDidMount(editor: monacoEditor.editor.IStandaloneDiffEditor, monaco: typeof monacoEditor) {
        diffEditorRef.current = editor;
        const modifiedEditor = editor.getModifiedEditor();
        modifiedEditor?.focus();

        // Listen for changes on the modified editor
        if (modifiedEditor) {
            modifiedEditor.onDidChangeModelContent(() => {
                const newCode = modifiedEditor.getValue();
                handleCodeChange(newCode);
            });
        }

        const tools: { [key: string]: { name: string; extension: string; shortName: string } } = fmpConfig.tools;
        for (const toolKey in tools) {
            const tool = tools[toolKey as keyof typeof tools];
            const languageId = tool.extension.replace(/^\./, '');
            const resource = languageConfigMap[languageId];
            if (!resource) {
                console.warn(`Language configuration for ${languageId} not found.`);
                continue;
            }
            const { tokenProvider, configuration } = resource;
            monaco.languages.register({ id: languageId });
            monaco.languages.setMonarchTokensProvider(languageId, tokenProvider);
            monaco.languages.setLanguageConfiguration(languageId, configuration);
        }

        monaco.editor.defineTheme('spectraTheme', {
            base: props.editorTheme === 'vs-dark' ? 'vs-dark' : 'vs', // 'vs-dark' or 'vs'
            inherit: true, // inherit the base theme
            rules: [
                { token: 'system', foreground: '189BCC', fontStyle: 'bold' },
                { token: 'environment', foreground: '0CD806', fontStyle: 'bold' },
                { token: 'reg', foreground: 'FF00FF' },
            ],
            colors: {},
        });

        monaco.editor.setTheme('spectraTheme');
    }

    useEffect(() => {
        if (diffEditorRef.current) {
            handleDiffEditorDidMount(diffEditorRef.current, window.monaco);
        }
    }, [props.editorTheme]);

    const handleCodeChange = (newCode: string | undefined) => {
        if (newCode !== undefined) {
            setEditorValue(newCode);
            setLineToHighlight([]);
        }
    };

    return (
        <div className='custom-diff-editor'>
            <DiffEditor
                height={props.height}
                width='100%'
                language={language.id}
                original={props.originalValue || ''}
                modified={props.modifiedValue || editorValue}
                theme={props.editorTheme}
                options={{
                    minimap: {
                        enabled: false,
                    },
                    automaticLayout: true,
                    mouseWheelZoom: true,
                    bracketPairColorization: {
                        enabled: true,
                        independentColorPoolPerBracketType: true,
                    },
                    readOnly:false,
                    renderSideBySide: true,
                    enableSplitViewResizing: true,
                    renderOverviewRuler: true,
                    ignoreTrimWhitespace: false,
                }}
                onMount={handleDiffEditorDidMount}
            />
        </div>
    );
};

export default CodeDiffEditor;