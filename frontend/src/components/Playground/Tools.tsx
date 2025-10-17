import React, { useEffect, useState } from 'react';
import Select from 'react-select';
import { fmpConfig } from '@/ToolMaps';
import '@/assets/style/Playground.css';

export type LanguageProps = {
    id: string;
    value: string;
    label: string;
    short: string;
};
interface ToolsProps {
    onChange: (selectedOption: any) => void;
    selected: LanguageProps;
    editorTheme: string;
    isDisabled?: boolean;
}

const Tools: React.FC<ToolsProps> = (props: ToolsProps) => {
    const [options, setOptions] = useState<{ id: string; value: string; label: string; short: string }[]>([]);
    const isDarkTheme = props.editorTheme === 'vs-dark';

    useEffect(() => {
        const generatedOptions = Object.entries(fmpConfig.tools).map(([key, tool]) => ({
            id: key,
            value: tool.extension,
            label: tool.name,
            short: tool.shortName,
        }));
        setOptions(generatedOptions);
    }, []);

    return (
        <div className='tools'>
            <Select
                className='basic-single react-select-container'
                classNamePrefix='select'
                defaultValue={options[0]}
                isDisabled={props.isDisabled || false}
                isLoading={false}
                isClearable={false}
                isRtl={false}
                isSearchable={true}
                name='color'
                options={options}
                onChange={props.onChange}
                value={props.selected}
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
    );
};

export default Tools;
