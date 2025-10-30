import axios from 'axios';

export interface ExplainRedundancyResponse {
  executionTime: number;
  weakerAssertions: string[];
  targetAssertion: string;
  lineRanges: number[][];
}

/**
 * Call the backend API to explain redundancy at a specific assertion line.
 * @param check - The check type (e.g., 'SMT')
 * @param permalink - The permalink identifier
 * @param assertionLine - The line number where the cursor is positioned (1-based)
 * @returns Promise containing the API response with line ranges to highlight
 */
export async function explainRedundancy(
  check: string,
  permalink: string,
  assertionLine: number
): Promise<ExplainRedundancyResponse> {
  try {
    const url = `/smt/smt/explain-redundancy/?check=${check}&p=${permalink}&assertion_line=${assertionLine}`;
    const response = await axios.get(url);

    // The backend now returns a JSON object: 
    // { time_taken: 0.002, minimal_set: ["x > 2"], given_assert: "x > 1", minimal_line_ranges: [[4, 6]] }
    const data = response.data;

    // Handle new JSON format
    if (data && typeof data === 'object' && 'time_taken' in data) {
      return {
        executionTime: data.time_taken,
        weakerAssertions: data.minimal_set,
        targetAssertion: data.given_assert,
        lineRanges: data.minimal_line_ranges,
      };
    }

    // Fallback: handle old array format for backward compatibility
    if (Array.isArray(data) && data.length >= 4) {
      return {
        executionTime: data[0],
        weakerAssertions: data[1],
        targetAssertion: data[2],
        lineRanges: data[3],
      };
    }

    throw new Error('Invalid response format from explain-redundancy API');
  } catch (error) {
    if (axios.isAxiosError(error)) {
      throw new Error(`Failed to explain redundancy: ${error.response?.data?.detail || error.message}\n; Check you have selected a valid assertion line.`);
    }
    throw error;
  }
}

/**
 * Parse line ranges from the API response to get individual line numbers to highlight.
 * For example, [[4, 6]] returns [4, 5, 6]
 * @param lineRanges - Array of [start, end] line ranges
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
