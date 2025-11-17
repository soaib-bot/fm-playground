import { WrapperConfig } from 'monaco-editor-wrapper';
import { createLangiumLimbooleConfig as createLimbooleConfig } from '../limboole/langium/config/wrapperLimbooleConfig';
import { createLangiumSmtConfig as createSmtConfig } from '../smt/langium/config/wrapperSmtConfig';
import { createLangiumSpectraConfig as createSpectraConfig } from '../spectra/langium/config/wrapperSpectraConfig';
import { createLangiumAlloyConfig as createAlloyConfig } from '../alloy/langium/config/wrapperAlloyConfig';
// import { createLangiumNuxmvConfig as createNuxmvConfig } from '../nuxmv/config/wrapperXmvConfig';

// Type for language configuration
interface LanguageConfig {
    configCreator: (params?: any) => Promise<WrapperConfig>;
    languageId: string;
}

// Map of language short names to their respective configurations
const languageConfigMap: Record<string, LanguageConfig | null> = {
    SAT: {
        configCreator: createLimbooleConfig,
        languageId: 'limboole',
    },
    SMT: {
        configCreator: createSmtConfig,
        languageId: 'smt',
    },
    SPECTRA: {
        configCreator: createSpectraConfig,
        languageId: 'spectra',
    },
    XMV: null, // XMV is not supported
    ALS: {
        configCreator: createAlloyConfig,
        languageId: 'alloy',
    }
};

export const createDynamicLspConfig = async (languageShort: string): Promise<WrapperConfig | null> => {
    const languageConfig = languageConfigMap[languageShort as keyof typeof languageConfigMap];

    if (!languageConfig) {
        console.warn(`No LSP configuration available for language: ${languageShort}`);
        return null;
    }

    try {
        return await languageConfig.configCreator();
    } catch (error) {
        console.error(`Error creating LSP config for ${languageShort}:`, error);
        return null;
    }
};

// Helper function to check if LSP is supported for a language
export const isLspSupported = (languageShort: string): boolean => {
    return languageConfigMap[languageShort as keyof typeof languageConfigMap] !== null;
};
