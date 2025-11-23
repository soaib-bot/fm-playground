import { saveCodeAndRefreshHistory } from '@/utils/codeExecutionUtils';
import { fmpConfig } from '@/ToolMaps';
import {
    editorValueAtom,
    jotaiStore,
    languageAtom,
    permalinkAtom,
    isExecutingAtom,
    outputAtom,
} from '@/atoms';
import { Permalink } from '@/types';
import axios from 'axios';

async function executeDafny(permalink: Permalink) {
    let url = `/dafny/dfy/run/?check=${permalink.check}&p=${permalink.permalink}`;
    try {
        const response = await axios.get(url);
        return response.data;
    } catch (error) {
        throw error;
    }
}

export const executeDafnyTool = async () => {
    const editorValue = jotaiStore.get(editorValueAtom);
    const language = jotaiStore.get(languageAtom);
    const permalink = jotaiStore.get(permalinkAtom);
    const response = await saveCodeAndRefreshHistory(editorValue, language.short, permalink.permalink || null, null);
    if (response) {
        jotaiStore.set(permalinkAtom, response.data);
    } else {
        jotaiStore.set(
            outputAtom,
            `Something went wrong. If the problem persists, open an <a href="${fmpConfig.issues}" target="_blank">issue</a>`
        );
        jotaiStore.set(isExecutingAtom, false);
    }

    try {
        const res = await executeDafny(response?.data);
        jotaiStore.set(outputAtom, res);
    } catch (err: any) {
        jotaiStore.set(
            outputAtom,
            `${err.message}. If the problem persists, open an <a href="${fmpConfig.issues}" target="_blank">issue</a>`
        );
    }
    jotaiStore.set(isExecutingAtom, false);
};
