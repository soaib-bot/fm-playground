import Select, { SingleValue } from 'react-select';
import { useAtom } from 'jotai';
import { smtDiffOptionsAtom } from '@/atoms';

const SmtDiffOptions = () => {
    const options = [
        { value: 'common', label: 'Common' },
        { value: 'left-vs-current', label: 'Left vs Current' },
        { value: 'current-vs-left', label: 'Current vs Left' },
    ];
    const [, setSmtDiffOption] = useAtom(smtDiffOptionsAtom);

    const handleOptionChange = (selectedOption: SingleValue<{ value: string; label: string }>) => {
        if (selectedOption) {
            setSmtDiffOption(selectedOption.value);
        }
    };

    return (
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
    );
};

export default SmtDiffOptions;
