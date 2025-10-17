import Select, { SingleValue } from 'react-select';
import { useAtom } from 'jotai';
import { limbooleDiffOptionsAtom } from '@/atoms';

const LimbooleDiffOptions = () => {
    // current-vs-left (Not Previous But Current), left-vs-current (Not Current But Previous)
    const options = [
        { value: 'common-witness', label: 'Common Witness' },
        { value: 'not-current-but-previous', label: 'Not Current But Previous' },
        { value: 'not-previous-but-current', label: 'Not Previous But Current' },
        { value: 'semantic-relation', label: 'Semantic Relation' },
    ];
    const [, setLimbooleDiffOption] = useAtom(limbooleDiffOptionsAtom);

    const handleOptionChange = (selectedOption: SingleValue<{ value: string; label: string }>) => {
        if (selectedOption) {
            setLimbooleDiffOption(selectedOption.value);
        }
    };

    return (
        <div style={{ display: 'flex', justifyContent: 'center', marginTop: '5px' }}>
            <p style={{ marginRight: '10px', marginTop: '5px' }}>Analysis:</p>
            <div style={{ width: '80%' }}>
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
    );
};

export default LimbooleDiffOptions;
