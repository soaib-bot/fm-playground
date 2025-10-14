import React from 'react'
import { useAtom } from 'jotai';
import { isFullScreenAtom } from '@/atoms';
const smtDiffOutput = () => {
    const [isFullScreen] = useAtom(isFullScreenAtom);
    return (
        <div>
            <pre
                className='plain-output-box'
                contentEditable={false}
                style={{
                    borderRadius: '8px',
                    height: isFullScreen ? '80vh' : '55vh',
                    whiteSpace: 'pre-wrap',
                }}
                // dangerouslySetInnerHTML={{ __html: alloyErrorMessage }}
            />
        </div>
    )
}

export default smtDiffOutput