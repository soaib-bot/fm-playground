import { saveCodeAndRefreshHistory } from '@/utils/codeExecutionUtils';
import { fmpConfig } from '@/ToolMaps';
import {
    editorValueAtom,
    jotaiStore,
    languageAtom,
    permalinkAtom,
    isExecutingAtom,
    outputAtom,
    limbooleDiffOptionsAtom,
    diffComparisonHistoryIdAtom,
    limbooleDiffWitnessAtom,
} from '@/atoms';
import { Permalink } from '@/types';
import axios from 'axios';

async function getLimbooleDiffWitness(permalink: Permalink, analysis: string) {
    let url = `/diff-limboole/run/?check=${permalink.check}&p=${permalink.permalink}&analysis=${analysis}`;
    try {
        const response = await axios.get(url);
        return response.data;
    } catch (error) {
        throw error;
    }
}

export const executeLimbooleDiffTool = async () => {
    const editorValue = jotaiStore.get(editorValueAtom);
    const language = jotaiStore.get(languageAtom);
    const permalink = jotaiStore.get(permalinkAtom);
    const limbooleDiffOption = jotaiStore.get(limbooleDiffOptionsAtom);
    const diffComparisonHistoryId = jotaiStore.get(diffComparisonHistoryIdAtom);

    // Create metadata with leftSideCodeId
    const metadata = {
        leftSideCodeId: diffComparisonHistoryId,
        diff_option: limbooleDiffOption,
    };

    // Save the code with SemDiff check type
    const response = await saveCodeAndRefreshHistory(
        editorValue,
        language.short + 'SemDiff',
        permalink.permalink || null,
        metadata
    );

    if (response) {
        jotaiStore.set(permalinkAtom, response.data);
    } else {
        jotaiStore.set(
            outputAtom,
            `Unable to generate permalink. If the problem persists, open an <a href="${fmpConfig.issues}" target="_blank">issue</a>`
        );
        jotaiStore.set(isExecutingAtom, false);
        return;
    }

    try {
        // Call the backend to get the first witness
        const res = await getLimbooleDiffWitness(response.data, limbooleDiffOption);
        jotaiStore.set(limbooleDiffWitnessAtom, res);
    } catch (err: any) {
        if (err.response?.status === 404) {
            console.error('No witnesses found');
            jotaiStore.set(limbooleDiffWitnessAtom, {
                error: 'No witnesses found',
            });
        } else {
            jotaiStore.set(limbooleDiffWitnessAtom, {
                error: `${err.message}. If the problem persists, open an <a href="${fmpConfig.issues}" target="_blank">issue</a>`,
            });
        }
    }
    jotaiStore.set(isExecutingAtom, false);
};
