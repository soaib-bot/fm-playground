import Select from 'react-select';
import { useAtom } from 'jotai';
import { spectraCliOptionsAtom, isDarkThemeAtom } from '@/atoms';

const SpectraCliOptions = () => {
    const [, setSpectraCliOption] = useAtom(spectraCliOptionsAtom);
    const [isDarkTheme] = useAtom(isDarkThemeAtom);
    const options = [
        { value: 'check-realizability', label: 'Check Realizability' },
        { value: 'concrete-controller', label: 'Synthesize Controller' },
        { value: 'concrete-counter-strategy', label: 'Counter-strategy' },
        { value: 'unrealizable-core', label: 'Unrealizable core' },
        { value: 'check-well-sep', label: 'Check well-separation' },
        { value: 'non-well-sep-core', label: 'Non-well-separated core' },
    ];

    const handleOptionChange = (selectedOption: { value: string; label: string } | null) => {
        if (selectedOption) {
            setSpectraCliOption(selectedOption.value);
        }
    };

    return (
        <div style={{ display: 'flex', justifyContent: 'center', marginTop: '15px' }}>
            <p style={{ marginRight: '10px', marginTop: '5px' }}>Command:</p>
            <div style={{ width: '70%' }}>
                <Select
                    className='basic-single react-select-container'
                    classNamePrefix='select'
                    defaultValue={options[0]}
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
                        control: (base, state) => ({
                            ...base,
                            backgroundColor: isDarkTheme ? '#1e1e1e' : base.backgroundColor,
                            borderColor: isDarkTheme ? '#464647' : base.borderColor,
                            color: isDarkTheme ? '#d4d4d4' : base.color,
                            '&:hover': {
                                borderColor: isDarkTheme ? '#0d6efd' : base.borderColor,
                            },
                            boxShadow: state.isFocused
                                ? isDarkTheme
                                    ? '0 0 0 1px #0d6efd'
                                    : base.boxShadow
                                : base.boxShadow,
                        }),
                        menu: (base) => ({
                            ...base,
                            backgroundColor: isDarkTheme ? '#1e1e1e' : base.backgroundColor,
                            border: isDarkTheme ? '1px solid #464647' : base.border,
                        }),
                        option: (base, state) => ({
                            ...base,
                            backgroundColor: state.isSelected
                                ? isDarkTheme
                                    ? '#0d6efd'
                                    : base.backgroundColor
                                : state.isFocused
                                    ? isDarkTheme
                                        ? '#2d2d30'
                                        : base.backgroundColor
                                    : isDarkTheme
                                        ? '#1e1e1e'
                                        : base.backgroundColor,
                            color: isDarkTheme ? '#d4d4d4' : base.color,
                            '&:hover': {
                                backgroundColor: isDarkTheme ? '#2d2d30' : base.backgroundColor,
                            },
                        }),
                        singleValue: (base) => ({
                            ...base,
                            color: isDarkTheme ? '#d4d4d4' : base.color,
                        }),
                        input: (base) => ({
                            ...base,
                            color: isDarkTheme ? '#d4d4d4' : base.color,
                        }),
                        placeholder: (base) => ({
                            ...base,
                            color: isDarkTheme ? '#6c757d' : base.color,
                        }),
                    }}
                />
            </div>
        </div>
    );
};

export default SpectraCliOptions;
