import axios from 'axios';

export interface NextSmtModelResponse {
    specId: string;
    next_model: string;
    error?: string;
}

/**
 * Fetch the next SMT model from the backend API
 * @param specId - The specification ID
 * @param permalink - The permalink identifier
 * @returns Promise containing the next model
 */
export async function getNextSmtModel(
    specId: string,
    permalink: string
): Promise<NextSmtModelResponse> {
    try {
        const url = `/smt/smt/next/?specId=${specId}&p=${permalink}`;
        const response = await axios.get(url);
        return response.data;
    } catch (error) {
        if (axios.isAxiosError(error)) {
            if (error.response?.status === 404) {
                throw new Error('No more models available');
            }
            throw new Error(`Failed to fetch next model: ${error.response?.data?.detail || error.message}`);
        }
        throw error;
    }
}
