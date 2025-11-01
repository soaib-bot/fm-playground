import { useEffect } from 'react';
import Select, { SingleValue } from 'react-select';
import { useAtom } from 'jotai';
import { editorValueAtom, alloySelectedCmdAtom, alloyCmdOptionsAtom, isDarkThemeAtom } from '@/atoms';

const AlloyCmdOptions = () => {
    const [editorValue] = useAtom(editorValueAtom);
    const [, setAlloySelectedCmd] = useAtom(alloySelectedCmdAtom);
    const [alloyCmdOption, setAlloyCmdOption] = useAtom(alloyCmdOptionsAtom);
    const [isDarkTheme] = useAtom(isDarkThemeAtom);

    const findIndexByValue = (cmdOptionValue: number) => {
        return alloyCmdOption.findIndex((option) => option.value === cmdOptionValue);
    };

    useEffect(() => {
        if (editorValue) {
            const lines = editorValue.split('\n');
            const options = [];
            const labelRegex = /^(\w+):\s*(run|check)\s+(\w+)/;

            for (let i = 0; i < lines.length; i++) {
                const line = lines[i].trim();
                if (line.startsWith('run') || line.startsWith('check')) {
                    const option = line;
                    options.push({ value: i, label: option });
                }
                // If there is a label, we need to add the label to the command
                else if (labelRegex.test(line)) {
                    const match = line.match(labelRegex);

                    if (match) {
                        const option = `${match[2]} ${match[1]} ${line.slice(match[0].length)}`;
                        options.push({ value: i, label: option });
                    }
                }
            }

            setAlloyCmdOption(options);
        }
    }, [editorValue]);

    const handleOptionChange = (selectedOption: SingleValue<{ value: number; label: string }>) => {
        if (selectedOption) {
            setAlloySelectedCmd(findIndexByValue(selectedOption.value));
        }
    };

    return (
        <div
            style={{
                display: 'flex',
                justifyContent: 'center',
                marginTop: '15px',
            }}
        >
            <p style={{ marginRight: '10px', marginTop: '5px' }}>Command:</p>
            <div style={{ width: '70%' }}>
                <Select
                    className='basic-single react-select-container'
                    classNamePrefix='select'
                    isDisabled={false}
                    isLoading={false}
                    isClearable={false}
                    isRtl={false}
                    isSearchable={true}
                    options={alloyCmdOption}
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

export default AlloyCmdOptions;
