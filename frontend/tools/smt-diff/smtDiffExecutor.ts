import { saveCodeAndRefreshHistory } from '@/utils/codeExecutionUtils';
import { fmpConfig } from '@/ToolMaps';
import {
    editorValueAtom,
    jotaiStore,
    languageAtom,
    permalinkAtom,
    isExecutingAtom,
    outputAtom,
    smtDiffOptionsAtom,
    diffComparisonHistoryIdAtom,
    smtDiffWitnessAtom,
    smtDiffFilterAtom
} from '@/atoms';
import { Permalink } from '@/types';
import axios from 'axios';

async function getSmtDiffWitness(permalink: Permalink, analysis: string, filter?: string) {
    let url = `/diff-smt/run/?check=${permalink.check}&p=${permalink.permalink}&analysis=${analysis}`;
    if (filter && filter.trim()) {
        url += `&filter=${encodeURIComponent(filter)}`;
    }
    try {
        const response = await axios.get(url);
        return response.data;
    } catch (error) {
        throw error;
    }
}

export async function getNextSmtDiffWitness(specId: string, p: string) {
    let url = `/diff-smt/next/${specId}?p=${p}`;
    try {
        const response = await axios.get(url);
        return response.data;
    } catch (error) {
        throw error;
    }
}

export const executeSmtDiffTool = async () => {
    const editorValue = jotaiStore.get(editorValueAtom);
    const language = jotaiStore.get(languageAtom);
    const permalink = jotaiStore.get(permalinkAtom);
    const smtDiffOption = jotaiStore.get(smtDiffOptionsAtom);
    const diffComparisonHistoryId = jotaiStore.get(diffComparisonHistoryIdAtom);
    const filterExpression = jotaiStore.get(smtDiffFilterAtom);

    // Create metadata with leftSideCodeId
    const metadata = {
        leftSideCodeId: diffComparisonHistoryId,
        diff_option: smtDiffOption,
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
        const res = await getSmtDiffWitness(response.data, smtDiffOption, filterExpression);
        jotaiStore.set(smtDiffWitnessAtom, res);
    } catch (err: any) {
        if (err.response?.status === 404) {
            jotaiStore.set(smtDiffWitnessAtom, {
                error: 'No witnesses found',
            });
        } else {
            jotaiStore.set(smtDiffWitnessAtom, {
                error: `${err.message}. If the problem persists, open an <a href="${fmpConfig.issues}" target="_blank">issue</a>`,
            });
        }
    }
    jotaiStore.set(isExecutingAtom, false);
};
