import React, { useMemo, useState } from 'react';
import { Chip, IconButton, InputBase, ListItem, Stack, Tooltip as MUITooltip } from '@mui/material';
import { MdEdit as EditIcon, MdSave as SaveIcon, MdClose as CloseIcon, MdLabel as LabelIcon, MdAdd as AddIcon, MdPushPin as PinFilledIcon, MdOutlinePushPin as PinOutlineIcon } from 'react-icons/md';
import { HistoryItemDTO } from './types';

function parseTags(raw: HistoryItemDTO['tags']): string[] {
    if (!raw) return [];
    if (Array.isArray(raw)) return raw;
    try {
        const arr = JSON.parse(raw);
        return Array.isArray(arr) ? arr : [];
    } catch {
        return [];
    }
}

interface HistoryItemProps {
    item: HistoryItemDTO;
    isSelected: boolean;
    onSelect: (item: HistoryItemDTO) => void;
    onHover: (id: number) => void;
    onTitleChange: (id: number, title: string) => Promise<void>;
    onTagsChange: (id: number, tags: string[]) => Promise<void>;
    onPinToggle: (id: number, pinned: boolean) => Promise<void>;
    fullCode?: string; // Full code for tooltip
    isDarkTheme: boolean;
}

const HistoryItem: React.FC<HistoryItemProps> = ({ item, isSelected, onSelect, onHover, onTitleChange, onTagsChange, onPinToggle, fullCode, isDarkTheme }) => {
    const [isEditingTitle, setIsEditingTitle] = useState(false);
    const [titleDraft, setTitleDraft] = useState(item.title || 'Untitled');
    const tags = useMemo(() => parseTags(item.tags), [item.tags]);
    const [localTags, setLocalTags] = useState<string[]>(tags);
    const [newTag, setNewTag] = useState('');
    const [isPinned, setIsPinned] = useState(item.pinned || false);

    React.useEffect(() => {
        setIsPinned(item.pinned || false);
    }, [item.pinned]);

    const handleSaveTitle = async () => {
        const t = titleDraft.trim() || 'Untitled';
        await onTitleChange(item.id, t);
        setIsEditingTitle(false);
    };

    const handleAddTag = async () => {
        const t = newTag.trim();
        if (!t) return;
        const next = Array.from(new Set([...localTags, t]));
        setLocalTags(next); // optimistic
        setNewTag('');
        await onTagsChange(item.id, next);
    };

    const handleRemoveTag = async (tag: string) => {
        const next = localTags.filter((x) => x !== tag);
        setLocalTags(next);
        await onTagsChange(item.id, next);
    };

    const handleEditClick = (e: React.MouseEvent) => {
        e.stopPropagation();
        setIsEditingTitle(true);
    };

    const handlePinClick = async (e: React.MouseEvent) => {
        e.stopPropagation();
        const newPinned = !isPinned;
        setIsPinned(newPinned); // optimistic update
        await onPinToggle(item.id, newPinned);
    };

    return (
        <MUITooltip
            title={
                <pre
                    style={{
                        margin: 0,
                        padding: '8px',
                        maxWidth: '400px',
                        maxHeight: '300px',
                        overflow: 'auto',
                        fontSize: '0.85rem',
                        fontFamily: 'monospace',
                        whiteSpace: 'pre-wrap',
                        wordBreak: 'break-word',
                    }}
                >
                    {fullCode || 'Loading...'}
                </pre>
            }
            placement='left'
            arrow
            enterDelay={500}
        >
            <ListItem
                divider
                selected={isSelected}
                onMouseEnter={() => onHover(item.id)}
                sx={{
                    cursor: 'pointer',
                    alignItems: 'flex-start',
                    padding: '8px 12px',
                    backgroundColor: isDarkTheme ? (isSelected ? 'rgba(144, 202, 249, 0.16)' : 'transparent') : undefined,
                    '&:hover': {
                        backgroundColor: isDarkTheme ? 'rgba(255, 255, 255, 0.08)' : undefined
                    },
                    borderColor: isDarkTheme ? 'rgba(255, 255, 255, 0.1)' : undefined
                }}
                onClick={() => !isEditingTitle && onSelect(item)}
            >
                <Stack direction="column" spacing={0.5} sx={{ width: '100%', alignItems: 'flex-start' }}>
                    {/* Title row with edit button */}
                    <Stack direction="row" justifyContent="space-between" alignItems="flex-start" sx={{ width: '100%' }}>
                        {isEditingTitle ? (
                            <>
                                <InputBase
                                    autoFocus
                                    value={titleDraft}
                                    onChange={(e) => setTitleDraft(e.target.value)}
                                    onKeyDown={(e) => {
                                        if (e.key === 'Enter') handleSaveTitle();
                                        if (e.key === 'Escape') setIsEditingTitle(false);
                                    }}
                                    onClick={(e) => e.stopPropagation()}
                                    placeholder="Untitled"
                                    sx={{
                                        fontWeight: 600,
                                        flex: 1,
                                        color: isDarkTheme ? '#fff' : '#000',
                                        '& input::placeholder': {
                                            color: isDarkTheme ? '#aaa' : '#666',
                                            opacity: 1
                                        }
                                    }}
                                />
                                <Stack direction="row" spacing={0.5}>
                                    <IconButton
                                        size="small"
                                        onClick={(e) => { e.stopPropagation(); handleSaveTitle(); }}
                                        aria-label="save title"
                                        sx={{ color: isDarkTheme ? '#fff' : undefined }}
                                    >
                                        <SaveIcon size={16} />
                                    </IconButton>
                                    <IconButton
                                        size="small"
                                        onClick={(e) => { e.stopPropagation(); setIsEditingTitle(false); }}
                                        aria-label="cancel"
                                        sx={{ color: isDarkTheme ? '#fff' : undefined }}
                                    >
                                        <CloseIcon size={16} />
                                    </IconButton>
                                </Stack>
                            </>
                        ) : (
                            <>
                                <span style={{ fontWeight: 600, flex: 1, color: isDarkTheme ? '#fff' : '#000' }}>{item.title || 'Untitled'}</span>
                                <Stack direction="row" spacing={0.5}>
                                    <IconButton
                                        size="small"
                                        onClick={handlePinClick}
                                        aria-label={isPinned ? "unpin item" : "pin item"}
                                        sx={{ padding: '4px', color: isDarkTheme ? '#fff' : undefined }}
                                    >
                                        {isPinned ? <PinFilledIcon size={16} /> : <PinOutlineIcon size={16} />}
                                    </IconButton>
                                    <IconButton
                                        size="small"
                                        onClick={handleEditClick}
                                        aria-label="edit title"
                                        sx={{ padding: '4px', color: isDarkTheme ? '#fff' : undefined }}
                                    >
                                        <EditIcon size={16} />
                                    </IconButton>
                                </Stack>
                            </>
                        )}
                    </Stack>

                    {/* Code snippet */}
                    <code style={{ fontSize: '0.75rem', color: isDarkTheme ? '#aaa' : '#666', display: 'block', textAlign: 'left', width: '100%' }}>
                        {item.code}
                    </code>

                    {/* Tool badge and tags */}
                    <Stack direction="row" spacing={1} alignItems="center" useFlexGap flexWrap="wrap" sx={{ justifyContent: 'flex-start', width: '100%' }}>
                        <MUITooltip title={`Tool: ${item.check}`}>
                            <Chip
                                size="small"
                                label={item.check}
                                variant="outlined"
                                sx={{
                                    color: isDarkTheme ? '#fff' : undefined,
                                    borderColor: isDarkTheme ? 'rgba(255, 255, 255, 0.23)' : undefined
                                }}
                            />
                        </MUITooltip>
                        {localTags.map((t) => (
                            <Chip
                                key={t}
                                size="small"
                                label={t}
                                onDelete={(e) => { e.stopPropagation(); handleRemoveTag(t); }}
                                sx={{
                                    color: isDarkTheme ? '#fff' : undefined,
                                    backgroundColor: isDarkTheme ? 'rgba(255, 255, 255, 0.08)' : undefined,
                                    '& .MuiChip-deleteIcon': {
                                        color: isDarkTheme ? 'rgba(255, 255, 255, 0.7)' : undefined,
                                        '&:hover': {
                                            color: isDarkTheme ? 'rgba(255, 255, 255, 0.9)' : undefined
                                        }
                                    }
                                }}
                            />
                        ))}
                        <Stack direction="row" spacing={0.5} alignItems="center">
                            <LabelIcon size={14} color={isDarkTheme ? '#aaa' : '#999'} />
                            <InputBase
                                placeholder="Add tag"
                                value={newTag}
                                onClick={(e) => e.stopPropagation()}
                                onChange={(e) => setNewTag(e.target.value)}
                                onKeyDown={(e) => {
                                    if (e.key === 'Enter') {
                                        e.stopPropagation();
                                        handleAddTag();
                                    }
                                }}
                                sx={{
                                    width: 80,
                                    fontSize: 12,
                                    color: isDarkTheme ? '#fff' : '#000',
                                    '& input::placeholder': {
                                        color: isDarkTheme ? '#aaa' : '#999',
                                        opacity: 1
                                    }
                                }}
                            />
                            <IconButton
                                size="small"
                                onClick={(e) => { e.stopPropagation(); handleAddTag(); }}
                                aria-label="add tag"
                                sx={{
                                    color: isDarkTheme ? '#fff' : undefined
                                }}
                            >
                                <AddIcon size={16} />
                            </IconButton>
                        </Stack>
                    </Stack>
                </Stack>
            </ListItem>
        </MUITooltip>
    );
};

export default HistoryItem;
