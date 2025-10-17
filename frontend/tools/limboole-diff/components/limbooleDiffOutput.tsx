import { useState, useEffect } from 'react';
import { useAtom } from 'jotai';
import { isFullScreenAtom, limbooleDiffWitnessAtom } from '@/atoms';

const LimbooleDiffOutput = () => {
    const [isFullScreen] = useAtom(isFullScreenAtom);
    const [limbooleDiffWitness] = useAtom(limbooleDiffWitnessAtom);

    const [witnessMessage, setWitnessMessage] = useState('');
    const [hasWitness, setHasWitness] = useState(false);
    const [witnessContent, setWitnessContent] = useState('');

    /**
     * Update the witness in the state when the API response is received
     */
    useEffect(() => {
        if (limbooleDiffWitness) {
            if (limbooleDiffWitness.witness) {
                setHasWitness(true);
                setWitnessContent(limbooleDiffWitness.witness);
                setWitnessMessage('');
            } else if (limbooleDiffWitness.error) {
                setHasWitness(false);
                setWitnessMessage(limbooleDiffWitness.error);
                setWitnessContent('');
            }
        }
    }, [limbooleDiffWitness]);

    return (
        <div>
            {hasWitness ? (
                <pre
                    className='plain-output-box'
                    contentEditable={false}
                    style={{
                        borderRadius: '8px',
                        height: isFullScreen ? '80vh' : '45vh',
                        whiteSpace: 'pre-wrap',
                        overflowY: 'auto',
                    }}
                >
                    {witnessContent}
                </pre>
            ) : (
                <div
                    className='plain-output-box'
                    style={{
                        borderRadius: '8px',
                        height: isFullScreen ? '80vh' : '45vh',
                        whiteSpace: 'pre-wrap',
                        padding: '15px',
                        overflowY: 'auto',
                    }}
                    dangerouslySetInnerHTML={{ __html: witnessMessage }}
                />
            )}
        </div>
    );
};

export default LimbooleDiffOutput;