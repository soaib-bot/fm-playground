import { useState, useEffect } from 'react';
import { useAtom } from 'jotai';
import { MDBBtn } from 'mdb-react-ui-kit';
import { smtModelAtom, outputPreviewHeightAtom, outputAtom } from '@/atoms';
import { getNextSmtModel } from '../smtExecutor';
import { jotaiStore, permalinkAtom } from '@/atoms';
import { logToDb } from '@/api/playgroundApi';

const SmtOutput = () => {
    const [smtModel, setSmtModel] = useAtom(smtModelAtom);
    const [outputPreviewHeight] = useAtom(outputPreviewHeightAtom);
    const [output] = useAtom(outputAtom);
    const permalink = jotaiStore.get(permalinkAtom);
    const [models, setModels] = useState<any[]>([]);
    const [currentModelIndex, setCurrentModelIndex] = useState(0);
    const [specId, setSpecId] = useState<string | null>(null);
    const [isNextModelExecuting, setIsNextModelExecuting] = useState(false);
    const [isLastModel, setIsLastModel] = useState(false);
    const [modelMessage, setModelMessage] = useState('');
    const [hasModel, setHasModel] = useState(false);
    const [isSatScenario, setIsSatScenario] = useState(false); // Track if this is a SAT scenario

    /**
     * Update the model in the state when the API response is received
     */
    useEffect(() => {
        if (smtModel) {
            // Reset models array when we get a completely new model (e.g., new execution)
            const isNavigationUpdate = models.some((model) => model === smtModel);
            if (!isNavigationUpdate) {
                setModels([smtModel]);
                setCurrentModelIndex(0);
                setIsLastModel(false); // Reset the last model flag for new execution
                
                // Check if the initial result is SAT (only on first execution)
                const initialResult = smtModel.result || '';
                const isSat = initialResult.toLowerCase().includes('sat') && !initialResult.toLowerCase().includes('unsat');
                setIsSatScenario(isSat);
            }

            // Check if we have any displayable content (result or next_model)
            const hasContent = smtModel.result || smtModel.next_model;
            
            if (smtModel.specId && hasContent) {
                setSpecId(smtModel.specId);
                setHasModel(true);
                setModelMessage('');
            } else if (smtModel.error) {
                setHasModel(false);
                setModelMessage(smtModel.result || smtModel.error || output);
                setIsSatScenario(false);
            } else if (hasContent) {
                // If there's a result/next_model but no specId, just display it
                setHasModel(true);
                setModelMessage('');
            }
        } else {
            // Clear all state when model is set to null
            setModels([]);
            setCurrentModelIndex(0);
            setSpecId(null);
            setIsNextModelExecuting(false);
            setIsLastModel(false);
            setModelMessage('');
            setHasModel(false);
            setIsSatScenario(false);
        }
    }, [smtModel, output]);

    const handleNextModel = () => {
        // Check if we already have a next model cached
        if (currentModelIndex < models.length - 1) {
            // Move to next cached model
            const nextIndex = currentModelIndex + 1;
            setCurrentModelIndex(nextIndex);
            setSmtModel(models[nextIndex]);
            return;
        }

        // Fetch new model from API
        if (!specId) return;

        setIsNextModelExecuting(true);
        getNextSmtModel(specId, permalink.permalink || '')
            .then((data: any) => {
                // Check if there's an error or no next_model
                if (data.error || !data.next_model || data.next_model.trim() === '') {
                    setIsLastModel(true);
                    setModelMessage('No more models');
                    setIsNextModelExecuting(false);
                    return;
                }

                // The backend returns { specId, next_model }
                // Normalize it to have the same structure as initial response
                const normalizedData = {
                    specId: data.specId || specId, // Preserve specId
                    result: data.next_model || data.result,
                    next_model: data.next_model
                };

                // Add new model to the array
                const updatedModels = [...models, normalizedData];
                const newIndex = updatedModels.length - 1;
                setModels(updatedModels);
                setCurrentModelIndex(newIndex);
                setSmtModel(normalizedData);
                setIsNextModelExecuting(false);
                
                // Log the next model event
                logToDb(permalink.permalink || '', { tool: 'SMT-Next', model: normalizedData, specId: specId });
            })
            .catch((error: any) => {
                console.error('Error fetching next model:', error);
                // 404 means no more models, any other error also means we can't fetch more
                setIsLastModel(true);
                setModelMessage('No more models');
                setIsNextModelExecuting(false);
            });
    };

    const handlePreviousModel = () => {
        if (currentModelIndex > 0) {
            const prevIndex = currentModelIndex - 1;
            setCurrentModelIndex(prevIndex);
            setSmtModel(models[prevIndex]);
            setIsLastModel(false);
            logToDb(permalink.permalink || '', { tool: 'SMT-Previous', model: models[prevIndex], specId: specId });
        }
    };

    const getCurrentModel = () => {
        if (models.length > 0 && models[currentModelIndex]) {
            return models[currentModelIndex].result || models[currentModelIndex].next_model || '';
        }
        return '';
    };

    // Check if the current model contains HTML
    const containsHTML = (text: string) => /<[^>]*>/.test(text);
    
    // Get the text to display - prefer smtModel output, fallback to outputAtom
    const getDisplayText = () => {
        if (hasModel) {
            return getCurrentModel();
        }
        return modelMessage || output;
    };
    
    const displayText = getDisplayText();
    const hasHTML = containsHTML(displayText);

    // Show buttons if we have a specId and this is a SAT scenario (determined from initial result)
    const shouldShowButtons = () => {
        return isSatScenario && specId !== null;
    };

    return (
        <div>
            {hasModel ? (
                <div>
                    <pre
                        className='plain-output-box'
                        contentEditable={false}
                        style={{
                            borderRadius: '8px',
                            height: outputPreviewHeight,
                            whiteSpace: 'pre-wrap',
                            marginBottom: '10px',
                        }}
                        {...(hasHTML ? { dangerouslySetInnerHTML: { __html: displayText } } : { children: displayText })}
                    />

                    {shouldShowButtons() && (
                        <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
                            <div style={{ display: 'flex', gap: '8px' }}>
                                <MDBBtn
                                    color='warning'
                                    onClick={handlePreviousModel}
                                    disabled={currentModelIndex === 0}
                                >
                                    Previous
                                </MDBBtn>

                                <MDBBtn
                                    color='success'
                                    onClick={handleNextModel}
                                    disabled={isNextModelExecuting || isLastModel}
                                >
                                    {isNextModelExecuting ? 'Computing...' : 'Next'}
                                </MDBBtn>
                            </div>
                        </div>
                    )}
                    {modelMessage && isLastModel && (
                        <div style={{ textAlign: 'center', color: '#ff0000ff' }}>{modelMessage}</div>
                    )}
                </div>
            ) : (
                <div
                    className='plain-output-box'
                    style={{
                        borderRadius: '8px',
                        height: outputPreviewHeight,
                        whiteSpace: 'pre-wrap',
                        padding: '15px',
                        overflowY: 'auto',
                    }}
                    {...(hasHTML ? { dangerouslySetInnerHTML: { __html: displayText } } : { children: displayText })}
                />
            )}
        </div>
    );
};

export default SmtOutput;
