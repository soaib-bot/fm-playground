import React from 'react'
import { MDBInput } from 'mdb-react-ui-kit';
import './SMTDiff.css';
interface SMTDiffEvaluatorProps {
    specId: string | null;
}

const SMTDiffEvaluator = ({ specId }: SMTDiffEvaluatorProps) => {
    const handleEvaluate = (expr: string) => {
        console.log("Evaluating smt-diff expression: ", expr, " for specId: ", specId);
    }
    return (
        <MDBInput
            label='SMT-LIB Assertion'
            id='smtLibAssertionForm'
            type='text'
            className='smt-lib-assertion-input'
            onKeyDown={(e) => {
                if (e.key === 'Enter') {
                    handleEvaluate(e.currentTarget.value);
                }
            }}
        />
    )
}

export default SMTDiffEvaluator