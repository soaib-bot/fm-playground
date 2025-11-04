import axios from 'axios';

export interface SmtModelIterationResponse {
    specId: string;
    result: string;
    error?: string;
}

export interface NextSmtModelResponse {
    specId: string;
    next_model: string;
    error?: string;
}

export async function initiateModelIteration(check: string, permalink: string): Promise<SmtModelIterationResponse> {
    try {
        const url = `/smt/smt/model-iteration/?check=${check}&p=${permalink}`;
        const response = await axios.get(url);

        if (!response.data.specId) {
            throw new Error('No specId returned from model iteration');
        }

        return response.data;
    } catch (error) {
        if (axios.isAxiosError(error)) {
            throw new Error(`Failed to initiate model iteration: ${error.response?.data?.detail || error.message}`);
        }
        throw error;
    }
}

export async function getNextSmtModel(specId: string, permalink: string): Promise<NextSmtModelResponse> {
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
