import { useState, useEffect } from 'react';
import { useAtom } from 'jotai';
import { MDBBtn } from 'mdb-react-ui-kit';
import { VscArrowLeft, VscArrowRight } from "react-icons/vsc";
import { isFullScreenAtom, smtDiffWitnessAtom } from '@/atoms';
import { getNextSmtDiffWitness } from '../smtDiffExecutor';
import SMTDiffEvaluator from './smtDiffEvaluator';

const SmtDiffOutput = () => {
    const [isFullScreen] = useAtom(isFullScreenAtom);
    const [smtDiffWitness, setSmtDiffWitness] = useAtom(smtDiffWitnessAtom);
    
    const [witnesses, setWitnesses] = useState<any[]>([]);
    const [currentWitnessIndex, setCurrentWitnessIndex] = useState(0);
    const [specId, setSpecId] = useState<string | null>(null);
    const [isNextWitnessExecuting, setIsNextWitnessExecuting] = useState(false);
    const [isLastWitness, setIsLastWitness] = useState(false);
    const [witnessMessage, setWitnessMessage] = useState('');
    const [hasWitness, setHasWitness] = useState(false);

    /**
     * Update the witness in the state when the API response is received
     */
    useEffect(() => {
        if (smtDiffWitness) {
            // Reset witnesses array when we get a completely new witness (e.g., new specification run)
            const isNavigationUpdate = witnesses.some((witness) => witness === smtDiffWitness);
            if (!isNavigationUpdate) {
                setWitnesses([smtDiffWitness]);
                setCurrentWitnessIndex(0);
            }
            
            if (smtDiffWitness.specId) {
                setSpecId(smtDiffWitness.specId);
                setHasWitness(true);
                setWitnessMessage('');
            } else if (smtDiffWitness.error) {
                setHasWitness(false);
                setWitnessMessage(smtDiffWitness.error);
            }
        }
    }, [smtDiffWitness]);

    const handleNextWitness = () => {
        // Check if we already have a next witness cached
        if (currentWitnessIndex < witnesses.length - 1) {
            // Move to next cached witness
            const nextIndex = currentWitnessIndex + 1;
            setCurrentWitnessIndex(nextIndex);
            setSmtDiffWitness(witnesses[nextIndex]);
            return;
        }

        // Fetch new witness from API
        if (!specId) return;
        
        setIsNextWitnessExecuting(true);
        getNextSmtDiffWitness(specId)
            .then((data) => {
                if (data.error) {
                    setIsLastWitness(true);
                    setWitnessMessage('No more witnesses');
                    setIsNextWitnessExecuting(false);
                    return;
                }
                
                // Add new witness to the array
                const updatedWitnesses = [...witnesses, data];
                const newIndex = updatedWitnesses.length - 1;
                setWitnesses(updatedWitnesses);
                setCurrentWitnessIndex(newIndex);
                setSmtDiffWitness(data);
                setIsNextWitnessExecuting(false);
            })
            .catch((error) => {
                console.error('Error fetching next witness:', error);
                if (error.response?.status === 404) {
                    setIsLastWitness(true);
                    setWitnessMessage('No more witnesses');
                }
                setIsNextWitnessExecuting(false);
            });
    };

    const handlePreviousWitness = () => {
        if (currentWitnessIndex > 0) {
            const prevIndex = currentWitnessIndex - 1;
            setCurrentWitnessIndex(prevIndex);
            setSmtDiffWitness(witnesses[prevIndex]);
            setIsLastWitness(false);
        }
    };

    const getCurrentWitness = () => {
        if (witnesses.length > 0 && witnesses[currentWitnessIndex]) {
            return witnesses[currentWitnessIndex].witness || '';
        }
        return '';
    };

    return (
        <div>
            {hasWitness ? (
                <div>
                    <SMTDiffEvaluator specId={specId} />
                    <pre
                        className='plain-output-box'
                        contentEditable={false}
                        style={{
                            borderRadius: '8px',
                            height: isFullScreen ? '70vh' : '45vh',
                            whiteSpace: 'pre-wrap',
                            marginBottom: '10px',
                        }}
                    >
                        {getCurrentWitness()}
                    </pre>
                    
                    {witnessMessage && (
                        <div style={{ textAlign: 'center', color: '#666', marginBottom: '10px' }}>
                            {witnessMessage}
                        </div>
                    )}

                    <div style={{ display: 'flex', justifyContent: 'center', gap: '10px', marginTop: '10px' }}>
                        <MDBBtn
                            color='secondary'
                            rounded
                            onClick={handlePreviousWitness}
                            disabled={currentWitnessIndex === 0}
                            size='sm'
                        >
                            <VscArrowLeft size={20} />
                        </MDBBtn>
                        
                        <span style={{ alignSelf: 'center', padding: '0 10px' }}>
                            Witness {currentWitnessIndex + 1} of {witnesses.length}
                        </span>
                        
                        <MDBBtn
                            color='secondary'
                            rounded
                            onClick={handleNextWitness}
                            disabled={isNextWitnessExecuting || isLastWitness}
                            size='sm'
                        >
                            {isNextWitnessExecuting ? 'Loading...' : <VscArrowRight size={20} />}
                        </MDBBtn>
                    </div>
                </div>
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

export default SmtDiffOutput;