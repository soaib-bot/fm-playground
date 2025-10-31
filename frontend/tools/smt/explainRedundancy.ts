import axios from 'axios';

export interface ExplainRedundancyResponse {
    lineRanges: number[][];
    targetAssertionRange: number[] | null;
}

/**
 * Call the backend API to explain redundancy at a specific assertion line.
 * @param check - The check type (e.g., 'SMT')
 * @param permalink - The permalink identifier
 * @param assertionLine - The line number where the cursor is positioned (1-based). Optional if assertion_text is provided.
 * @param assertion_text - The assertion text to explain. Optional if assertionLine is provided.
 * @returns Promise containing the API response with line ranges to highlight
 */
export async function explainRedundancy(
    check: string,
    permalink: string,
    assertionLine?: number,
    assertion_text?: string
): Promise<ExplainRedundancyResponse> {
    try {
        const url = `/smt/smt/explain-redundancy/`;

        const requestBody: any = {
            check,
            p: permalink,
        };

        if (assertionLine === 1) {
            throw new Error('<span style="color: red">; Assertion line is selected as 1, which might not be correct.<br>Select place cursor on the actual assertion line or select the complete assertion text.</span>');
        }

        if (assertion_text) {
            requestBody.assertion_text = assertion_text;
        } else if (assertionLine !== undefined) {
            requestBody.assertion_line = assertionLine;
        } else {
            throw new Error('<span style="color: red ">; Either assertionLine or assertion_text must be provided</span>');
        }

        const response = await axios.post(url, requestBody);

        const data = response.data;
        if (data && typeof data === 'object') {
            return {
                lineRanges: data.minimal_line_ranges,
                targetAssertionRange: data.target_assertion_range,
            };
        }

        throw new Error('<span style="color: red">; Invalid response format from explain-redundancy API</span>');
    } catch (error) {
        if (axios.isAxiosError(error)) {
            throw new Error(`${error.response?.data?.detail || error.message}\n; Check you have selected a valid assertion line.`);
        }
        throw error;
    }
}

/**
 * Parse line ranges from the API response to get individual line numbers to highlight.
 * For example, [[4, 6, 1, 15]] returns [4, 5, 6]
 * @param lineRanges - Array of [start_line, end_line, start_col, end_col] ranges
 * @returns Array of individual line numbers to highlight
 */
export function parseLineRanges(lineRanges: number[][]): number[] {
    const lines: number[] = [];

    for (const range of lineRanges) {
        if (Array.isArray(range) && range.length >= 2) {
            const start = range[0];
            const end = range[1];

            // Add all lines from start to end (inclusive)
            for (let line = start; line <= end; line++) {
                lines.push(line);
            }
        } else if (typeof range === 'number') {
            // If it's just a single number, add it
            lines.push(range);
        }
    }

    return lines;
}

/**
 * Convert API ranges to Monaco editor range objects for precise highlighting.
 * @param ranges - Array of [start_line, end_line, start_col, end_col] ranges
 * @returns Array of objects with startLine, startColumn, endLine, endColumn
 */
export function parseRangesToMonaco(ranges: number[][]): Array<{
    startLine: number;
    startColumn: number;
    endLine: number;
    endColumn: number;
}> {
    const monacoRanges: Array<{
        startLine: number;
        startColumn: number;
        endLine: number;
        endColumn: number;
    }> = [];

    for (const range of ranges) {
        if (Array.isArray(range) && range.length >= 4) {
            monacoRanges.push({
                startLine: range[0],
                startColumn: range[2],
                endLine: range[1],
                endColumn: range[3],
            });
        } else if (Array.isArray(range) && range.length >= 2) {
            // Fallback: whole line if no column info
            monacoRanges.push({
                startLine: range[0],
                startColumn: 1,
                endLine: range[1],
                endColumn: Number.MAX_SAFE_INTEGER,
            });
        }
    }

    return monacoRanges;
}
