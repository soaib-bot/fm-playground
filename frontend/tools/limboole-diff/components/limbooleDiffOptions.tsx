import { useState } from 'react';
import Select, { SingleValue } from 'react-select';
import { useAtom } from 'jotai';
import { limbooleDiffOptionsAtom, limbooleDiffWitnessAtom } from '@/atoms';
import { MDBInput } from 'mdb-react-ui-kit';
import axios from 'axios';

const LimbooleDiffOptions = () => {
    // current-vs-left (Not Previous But Current), left-vs-current (Not Current But Previous)
    const options = [
        { value: 'common-witness', label: 'Common Witness' },
        { value: 'not-current-but-previous', label: 'Not Current But Previous' },
        { value: 'not-previous-but-current', label: 'Not Previous But Current' },
        { value: 'semantic-relation', label: 'Semantic Relation' },
    ];
    const [selectedOption, setSelectedOption] = useState(options[0].value);
    const [, setLimbooleDiffOption] = useAtom(limbooleDiffOptionsAtom);
    const [limbooleDiffWitness, setLimbooleDiffWitness] = useAtom(limbooleDiffWitnessAtom);

    const [isEvaluating, setIsEvaluating] = useState(false);

    const handleOptionChange = (selectedOption: SingleValue<{ value: string; label: string }>) => {
        if (selectedOption) {
            setLimbooleDiffOption(selectedOption.value);
            setSelectedOption(selectedOption.value);
        }
    };

    const handleEvaluate = async (expr: string) => {
        if (!expr.trim()) {
            // Show error in the witness output area
            setLimbooleDiffWitness({
                ...limbooleDiffWitness,
                witness: 'Please enter a formula to evaluate',
                error: 'Please enter a formula to evaluate',
            });
            return;
        }

        const specId = limbooleDiffWitness?.specId;
        if (!specId || specId === 'semantic-relation') {
            setLimbooleDiffWitness({
                ...limbooleDiffWitness,
                witness: 'Evaluation not available for this analysis type',
                error: 'Evaluation not available for this analysis type',
            });
            return;
        }

        setIsEvaluating(true);

        try {
            const url = `/diff-limboole/eval/${specId}?formula=${encodeURIComponent(expr)}`;
            const response = await axios.get(url);
            // Update witness with evaluation result - replace the witness content
            setLimbooleDiffWitness({
                ...limbooleDiffWitness,
                witness: response.data.evaluation,
            });
        } catch (error: any) {
            let errorMsg = 'Error evaluating formula. Please check the syntax.';
            if (error.response?.status === 404) {
                errorMsg = 'Cache expired or formula evaluation failed';
            }
            setLimbooleDiffWitness({
                ...limbooleDiffWitness,
                witness: errorMsg,
                error: errorMsg,
            });
            console.error('Error evaluating formula:', error);
        } finally {
            setIsEvaluating(false);
        }
    };

    // Show evaluator only if:
    // 1. Analysis type is not semantic-relation
    // 2. We have a witness (analysis has been run at least once)
    // 3. The witness is not UNSATISFIABLE
    const isUnsatisfiable = limbooleDiffWitness?.witness?.startsWith('% UNSATISFIABLE formula');
    const showEvaluator = selectedOption !== 'semantic-relation' && limbooleDiffWitness?.specId && !isUnsatisfiable;

    return (
        <div>
            <div style={{ display: 'flex', justifyContent: 'center', marginTop: '5px' }}>
                <p style={{ marginRight: '10px', marginTop: '5px' }}>Analysis:</p>
                <div style={{ width: '70%' }}>
                    <Select
                        className='basic-single react-select-container'
                        classNamePrefix='select'
                        defaultValue={options[0] || null}
                        isDisabled={false}
                        isLoading={false}
                        isClearable={false}
                        isRtl={false}
                        isSearchable={true}
                        options={options}
                        onChange={handleOptionChange}
                        menuPortalTarget={document.body}
                        styles={{
                            menuPortal: (base) => ({ ...base, zIndex: 9999 }),
                        }}
                    />
                </div>
            </div>

            {showEvaluator && (
                <div style={{ marginTop: '15px', paddingLeft: '15px', paddingRight: '15px' }}>
                    <MDBInput
                        label='Witness Filter (Limboole Expression)'
                        id='limbooleExpressionForm'
                        type='text'
                        disabled={isEvaluating}
                        onKeyDown={(e) => {
                            if (e.key === 'Enter') {
                                handleEvaluate(e.currentTarget.value);
                            }
                        }}
                    />
                </div>
            )}
        </div>
    );
};

export default LimbooleDiffOptions;
