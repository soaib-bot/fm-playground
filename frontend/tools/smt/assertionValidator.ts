/**
 * Validates if a given text represents a complete SMT-LIB assertion.
 * Uses regex pattern matching and parenthesis counting similar to the backend.
 *
 * @param text - The selected text to validate
 * @returns Object with isValid flag and optional error message
 */
export function validateAssertion(text: string): {
    isValid: boolean;
    error?: string;
    normalizedText?: string;
} {
    if (!text || text.trim().length === 0) {
        return {
            isValid: false,
            error: 'No text selected. Select a complete assertion or place cursor on an assertion line.',
        };
    }

    const trimmedText = text.trim();

    // Check if it contains (assert pattern (case-insensitive)
    const assertPattern = /\(\s*assert\s+/i;
    const hasAssert = assertPattern.test(trimmedText);

    // If it doesn't start with (assert, check if it's just an expression
    let textToValidate = trimmedText;
    let isExpression = false;

    if (!hasAssert) {
        // Check if it looks like an expression (starts with '(')
        if (trimmedText.startsWith('(')) {
            // It might be just the expression without (assert ...)
            isExpression = true;
            textToValidate = trimmedText;
        } else {
            return {
                isValid: false,
                error: 'Selected text is not a valid assertion. Select a complete assertion or place cursor on an assertion line.',
            };
        }
    }

    // Validate parenthesis matching
    const parenCount = countParentheses(textToValidate);

    if (parenCount !== 0) {
        return {
            isValid: false,
            error: 'Incomplete assertion selected. Parentheses are not balanced. Select a complete assertion or place cursor on an assertion line.',
        };
    }

    // If it's an expression without (assert ...), we'll let the backend handle normalization
    // If it has (assert ...), verify it's at the beginning
    if (hasAssert) {
        const match = assertPattern.exec(trimmedText);
        if (match && match.index !== 0) {
            return {
                isValid: false,
                error: 'Assertion must start with "(assert". Select a complete assertion or place cursor on an assertion line.',
            };
        }
    }

    return {
        isValid: true,
        normalizedText: trimmedText,
    };
}

/**
 * Counts parentheses in a string to check if they are balanced.
 * @param text - The text to check
 * @returns The difference between opening and closing parentheses (0 means balanced)
 */
function countParentheses(text: string): number {
    let count = 0;
    let inString = false;
    let escapeNext = false;

    for (let i = 0; i < text.length; i++) {
        const char = text[i];

        // Handle string literals to avoid counting parentheses inside strings
        if (escapeNext) {
            escapeNext = false;
            continue;
        }

        if (char === '\\') {
            escapeNext = true;
            continue;
        }

        if (char === '"') {
            inString = !inString;
            continue;
        }

        if (inString) {
            continue;
        }

        // Count parentheses outside of strings
        if (char === '(') {
            count++;
        } else if (char === ')') {
            count--;
        }

        // If count goes negative, parentheses are unbalanced
        if (count < 0) {
            return count;
        }
    }

    return count;
}
