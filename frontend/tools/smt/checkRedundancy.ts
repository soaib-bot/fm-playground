import axios from 'axios';

export interface CheckRedundancyResponse {
    output: string;
    redundantLines: any[] | null;
}

/**
 * Call the backend API to check for redundant assertions.
 * @param check - The check type (e.g., 'SMT')
 * @param permalink - The permalink identifier
 * @returns Promise containing the API response with output and redundant lines
 */
export async function checkRedundancy(check: string, permalink: string): Promise<CheckRedundancyResponse> {
    try {
        const url = `/smt/smt/check-redundancy/?check=${check}&p=${permalink}`;
        const response = await axios.get(url);

        // The backend now returns a JSON object: { result: string, redundant_lines: array | null }
        const data = response.data;

        // Handle new JSON format
        if (data && typeof data === 'object' && 'result' in data) {
            return {
                output: data.result || '',
                redundantLines: data.redundant_lines || null,
            };
        }

        // Fallback: handle old array format for backward compatibility
        if (Array.isArray(data)) {
            return {
                output: data[0] || '',
                redundantLines: data[1] || null,
            };
        }

        // If it's just a string, treat it as output with no redundant lines
        if (typeof data === 'string') {
            return {
                output: data,
                redundantLines: null,
            };
        }

        throw new Error('Invalid response format from check-redundancy API');
    } catch (error) {
        if (axios.isAxiosError(error)) {
            throw new Error(`Failed to check redundancy: ${error.response?.data?.detail || error.message}`);
        }
        throw error;
    }
}
