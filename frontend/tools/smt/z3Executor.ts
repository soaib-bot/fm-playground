import runZ3WASM from '@/../tools/smt/runZ3WASM';
import { getLineToHighlight } from '@/../tools/common/lineHighlightingUtil';
import { saveCodeAndRefreshHistory } from '@/utils/codeExecutionUtils';
import { fmpConfig } from '@/ToolMaps';
import {
    editorValueAtom,
    jotaiStore,
    languageAtom,
    permalinkAtom,
    isExecutingAtom,
    lineToHighlightAtom,
    outputAtom,
    enableLspAtom,
} from '@/atoms';
import axios from 'axios';
import { updateMetadataByPermalink } from '@/api/playgroundApi';
import { Permalink } from '@/types';


// Cache of redundant lines to remove, set when the server returns res[1]
let __redundantLinesToRemove: any[] | null = null;

// Helper to parse line data and return a set of line numbers
const parseLinesToSet = (linesData: any[], maxLines: number): Set<number> => {
    const lineSet = new Set<number>();
    const addRange = (start: number, end?: number) => {
        if (!Number.isFinite(start)) return;
        const s = Math.max(1, Math.min(Math.trunc(start), maxLines));
        const e = Number.isFinite(end as number)
            ? Math.max(1, Math.min(Math.trunc(end as number), maxLines))
            : s;
        const from = Math.min(s, e);
        const to = Math.max(s, e);
        for (let i = from; i <= to; i++) lineSet.add(i);
    };

    if (Array.isArray(linesData)) {
        for (const item of linesData) {
            if (typeof item === 'number') {
                addRange(item);
            } else if (Array.isArray(item) && item.length >= 2) {
                addRange(Number(item[0]), Number(item[1]));
            } else if (item && typeof item === 'object') {
                if (typeof (item as any).line === 'number') {
                    addRange((item as any).line);
                } else if (
                    typeof (item as any).start === 'number' &&
                    typeof (item as any).end === 'number'
                ) {
                    addRange((item as any).start, (item as any).end);
                } else if (
                    (item as any).startLine !== undefined &&
                    (item as any).endLine !== undefined
                ) {
                    addRange(Number((item as any).startLine), Number((item as any).endLine));
                }
            }
        }
    }
    return lineSet;
};

// Expose global click handlers for the inline buttons rendered in outputAtom
if (typeof window !== 'undefined') {
    // Comment out redundant assertions
    (window as any).__commentRedundantAssertions = () => {
        try {
            const linesData = __redundantLinesToRemove;
            if (!linesData) return;

            const editorValue = (jotaiStore.get(editorValueAtom) as string) || '';
            const lines = editorValue.split(/\r?\n/);
            const max = lines.length;

            const toComment = parseLinesToSet(linesData, max);

            // Comment out lines; no need for descending order since we don't change indices
            const sorted = Array.from(toComment).sort((a, b) => a - b);
            for (const ln of sorted) {
                const idx = ln - 1; // convert 1-based to 0-based
                if (idx >= 0 && idx < lines.length) {
                    const original = lines[idx];
                    // Skip if already commented
                    if (/^\s*;/.test(original)) continue;
                    // Preserve leading indentation when inserting '; '
                    const m = original.match(/^(\s*)(.*)$/);
                    const indent = m ? m[1] : '';
                    const rest = m ? m[2] : original;
                    lines[idx] = `${indent}; ${rest}`;
                }
            }

            const updated = lines.join('\n');
            jotaiStore.set(editorValueAtom, updated);
            jotaiStore.set(lineToHighlightAtom, []);
            jotaiStore.set(outputAtom, '; Commented out redundant assertions');
        } catch (err) {
            jotaiStore.set(outputAtom, '; Failed to comment out lines');
        }
    };

    // Remove redundant assertions
    (window as any).__removeRedundantAssertions = () => {
        try {
            const linesData = __redundantLinesToRemove;
            if (!linesData) return;

            const editorValue = (jotaiStore.get(editorValueAtom) as string) || '';
            const lines = editorValue.split(/\r?\n/);
            const max = lines.length;

            const toRemove = parseLinesToSet(linesData, max);

            // Remove lines in descending order to avoid index shifting
            const sorted = Array.from(toRemove).sort((a, b) => b - a);
            for (const ln of sorted) {
                const idx = ln - 1; // convert 1-based to 0-based
                if (idx >= 0 && idx < lines.length) {
                    lines.splice(idx, 1);
                }
            }

            const updated = lines.join('\n');
            jotaiStore.set(editorValueAtom, updated);
            jotaiStore.set(lineToHighlightAtom, []);
            jotaiStore.set(outputAtom, '; Removed redundant assertions');
        } catch (err) {
            jotaiStore.set(outputAtom, '; Failed to remove lines');
        }
    };
}

async function executeZ3(permalink: Permalink) {
    let url = `/smt/smt/run/?check=${permalink.check}&p=${permalink.permalink}`;
    try {
        const response = await axios.get(url);
        return response.data;
    } catch (error) {
        throw error;
    }
}

/**
 * Execute Z3 on the server.
 * Handles redundant assertions if returned by the server.
 */
export const executeZ3Server = async () => {
    const editorValue = jotaiStore.get(editorValueAtom);
    const language = jotaiStore.get(languageAtom);
    const permalink = jotaiStore.get(permalinkAtom);
    const enableLsp = jotaiStore.get(enableLspAtom);
    let response: any = null;
    const metadata = { ls: enableLsp };
    try {
        response = await saveCodeAndRefreshHistory(editorValue, language.short, permalink.permalink || null, metadata);
        if (response) {
            jotaiStore.set(permalinkAtom, response.data);
        }
    } catch (error: any) {
        jotaiStore.set(
            outputAtom,
            `Something went wrong. If the problem persists, open an <a href="${fmpConfig.issues}" target="_blank">issue</a>`
        );
    }

    // Removed unused runWithTimeout helper (was used only by commented-out WASM path)

    try {
        const res = await executeZ3(response?.data);
        if (res[0].includes('(error')) {
            jotaiStore.set(outputAtom, res[0]);
            jotaiStore.set(lineToHighlightAtom, getLineToHighlight(res[0], language.id) || []);
            jotaiStore.set(isExecutingAtom, false);
            return;
        }
        if (res[1] && res[1].length > 0) {
            __redundantLinesToRemove = res[1];
            jotaiStore.set(lineToHighlightAtom, res[1]);

            // Update metadata in backend with redundant lines found
            try {
                const currentPermalink = jotaiStore.get(permalinkAtom);
                if (currentPermalink?.permalink) {
                    await updateMetadataByPermalink(currentPermalink.permalink, { redFound: res[1] });
                }
            } catch (error) {
                console.error('Failed to update metadata:', error);
            }

            const msg =
                res[0] +
                `\n; Your script contains redundant assertions (see highlighted lines).\n; Do you want to remove them?` +
                `\n<button onclick="__commentRedundantAssertions()">Comment out</button> ` +
                `<button onclick="__removeRedundantAssertions()">Remove</button>`;
            jotaiStore.set(outputAtom, msg);
            jotaiStore.set(isExecutingAtom, false);
            return;
        }

        jotaiStore.set(outputAtom, res[0]);
    } catch (error) {
        jotaiStore.set(outputAtom, (error as any).message);
        jotaiStore.set(isExecutingAtom, false);
        return;
    }
    jotaiStore.set(isExecutingAtom, false);
};


/**
 * Execute Z3 using a hybrid approach: try WASM first, then fall back to server.
 */
export const executeZ3Hybrid = async () => {
    const editorValue = jotaiStore.get(editorValueAtom);
    const language = jotaiStore.get(languageAtom);
    const permalink = jotaiStore.get(permalinkAtom);
    const enableLsp = jotaiStore.get(enableLspAtom);
    let response: any = null;
    const metadata = { ls: enableLsp };
    try {
        response = await saveCodeAndRefreshHistory(editorValue, language.short, permalink.permalink || null, metadata);
        if (response) {
            jotaiStore.set(permalinkAtom, response.data);
        }
    } catch (error: any) {
        jotaiStore.set(
            outputAtom,
            `Something went wrong. If the problem persists, open an <a href="${fmpConfig.issues}" target="_blank">issue</a>`
        );
    }

    const runWithTimeout = <T>(promise: Promise<T>, timeoutMs: number): Promise<T> => {
        return Promise.race([
            promise,
            new Promise<T>((_, reject) => setTimeout(() => reject(new Error('WASM load timeout')), timeoutMs)),
        ]);
    };

    try {
        const res = await runWithTimeout(runZ3WASM(editorValue), 10000);
        if (res.error) {
            jotaiStore.set(outputAtom, res.error);
        } else {
            jotaiStore.set(lineToHighlightAtom, getLineToHighlight(res.output, language.id) || []);
            jotaiStore.set(outputAtom, res.output);
        }
    } catch (err: any) {
        jotaiStore.set(outputAtom, "Could't load WASM module. Trying to execute on the server...");
        try {
            const res = await executeZ3(response?.data);
            jotaiStore.set(lineToHighlightAtom, getLineToHighlight(res, language.id) || []);
            jotaiStore.set(outputAtom, res);
        } catch (error: any) {
            jotaiStore.set(outputAtom, error.message);
        }
    }
    jotaiStore.set(isExecutingAtom, false);
};