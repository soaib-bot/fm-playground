import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import { Drawer, List, ListSubheader, InputBase, IconButton, CircularProgress, Chip } from '@mui/material';
import { MdRefresh, MdPushPin, MdOutlinePushPin, MdSearch, MdClose } from 'react-icons/md';
import { useAtom } from 'jotai';
import { historyRefreshTriggerAtom } from '@/atoms';
import { getHistoryByPage, searchUserHistory, getCodeById, updateHistoryTitle, updateHistoryTags, updateHistoryPinned } from '@/api/playgroundApi';
import HistoryItem from './HistoryItem';
import type { DrawerComponentProps, HistoryItemDTO } from './types';

function groupByDate(items: HistoryItemDTO[]) {
    const groups: Record<string, HistoryItemDTO[]> = { Today: [], Yesterday: [], Earlier: [] };
    const now = new Date();
    const todayStr = now.toDateString();
    const yesterday = new Date(now); yesterday.setDate(now.getDate() - 1);
    const yesterdayStr = yesterday.toDateString();
    for (const it of items) {
        const d = it.time_iso ? new Date(it.time_iso) : null;
        const key = d ? (d.toDateString() === todayStr ? 'Today' : d.toDateString() === yesterdayStr ? 'Yesterday' : 'Earlier') : 'Earlier';
        groups[key].push(it);
    }
    return groups;
}

const HistoryDrawer: React.FC<DrawerComponentProps> = ({ isOpen, onClose, onItemSelect, isDarkTheme = false, isLoggedIn, selectedTool }) => {
    const [historyRefreshTrigger] = useAtom(historyRefreshTriggerAtom);
    const [shouldRefreshOnOpen, setShouldRefreshOnOpen] = useState(false);
    const [data, setData] = useState<HistoryItemDTO[]>([]);
    const [searchData, setSearchData] = useState<HistoryItemDTO[]>([]);
    const [page, setPage] = useState(1);
    const [loading, setLoading] = useState(false);
    const [hasMoreData, setHasMoreData] = useState(true);
    const [isDrawerPinned, setIsDrawerPinned] = useState(false);
    const [showPinnedOnly, setShowPinnedOnly] = useState(false);
    const [searchIn, setSearchIn] = useState<'all' | 'code' | 'title' | 'tags'>('all');
    const [selectedItemId, setSelectedItemId] = useState<number | null>(null);
    const [fullCodeCache, setFullCodeCache] = useState<Record<number, string>>({});
    const [debouncedSearchQuery, setDebouncedSearchQuery] = useState('');
    const drawerRef = useRef<HTMLDivElement | null>(null);

    const uniqueData = useMemo(() => {
        const ids = new Set<number>();
        const list: HistoryItemDTO[] = [];
        (data || []).forEach((it) => { if (!ids.has(it.id)) { ids.add(it.id); list.push(it); } });
        return list;
    }, [data]);

    const uniqueSearchData = useMemo(() => {
        const ids = new Set<number>();
        const list: HistoryItemDTO[] = [];
        (searchData || []).forEach((it) => { if (!ids.has(it.id)) { ids.add(it.id); list.push(it); } });
        return list;
    }, [searchData]);

    const handleScroll = () => {
        const el = drawerRef.current;
        if (el) {
            const { scrollTop, scrollHeight, clientHeight } = el;
            const fromBottom = scrollHeight - (scrollTop + clientHeight);
            if (fromBottom < 50 && !loading && hasMoreData && !debouncedSearchQuery) {
                void fetchData(page);
            }
        }
    };

    const fetchData = async (pageNumber: number) => {
        if (loading || !hasMoreData) return;
        try {
            setLoading(true);
            const res = await getHistoryByPage(pageNumber, selectedTool);
            const hist = res?.history || [];
            if (pageNumber === 1) setData(hist);
            else setData((prev) => [...prev, ...hist]);
            setHasMoreData(!!res?.has_more_data);
            setPage((p) => p + 1);
        } catch (e) {
            console.error('Error fetching history', e);
        } finally { setLoading(false); }
    };

    // Debounced search
    useEffect(() => {
        const id = setTimeout(async () => {
            if (!debouncedSearchQuery) { setSearchData([]); return; }
            try {
                setLoading(true);
                const res = await searchUserHistory(debouncedSearchQuery, selectedTool, searchIn);
                setSearchData(res?.history || []);
            } catch (e) { console.error(e); } finally { setLoading(false); }
        }, 400);
        return () => clearTimeout(id);
    }, [debouncedSearchQuery, selectedTool, searchIn]);

    const handleItemClick = async (item: HistoryItemDTO) => {
        try {
            const cached = fullCodeCache[item.id];
            if (cached) {
                onItemSelect(item.check, item.permalink, cached, item.id);
            } else {
                const res = await getCodeById(item.id);
                if (res?.code) {
                    onItemSelect(res.check, res.permalink, res.code, item.id);
                    setFullCodeCache((prev) => ({ ...prev, [item.id]: res.code }));
                }
            }
            onClose();
            setSelectedItemId(item.id);
        } catch (e) { console.error(e); }
    };

    const handleItemHover = async (id: number) => {
        if (fullCodeCache[id]) return;
        try {
            const res = await getCodeById(id);
            if (res?.code) setFullCodeCache((prev) => ({ ...prev, [id]: res.code }));
        } catch (e) { console.error(e); }
    };

    const handleRefresh = useCallback(async (isAutoRefresh: boolean = false) => {
        try {
            const res = await getHistoryByPage(1, selectedTool);
            const hist = res?.history || [];
            if (isAutoRefresh) { setData(hist); setPage(1); }
            else {
                const newIds = new Set(hist.map((h: HistoryItemDTO) => h.id));
                setData((prev) => [...hist, ...prev.filter((p) => !newIds.has(p.id))]);
            }
        } catch (e) { console.error(e); }
    }, [selectedTool]);

    useEffect(() => {
        if (!debouncedSearchQuery) {
            if (isOpen) handleRefresh(true);
            else setShouldRefreshOnOpen(true);
        }
    }, [historyRefreshTrigger, isOpen, debouncedSearchQuery, handleRefresh]);

    useEffect(() => {
        if (isOpen && shouldRefreshOnOpen && !debouncedSearchQuery) {
            void handleRefresh(true);
            setShouldRefreshOnOpen(false);
        }
    }, [isOpen, shouldRefreshOnOpen, debouncedSearchQuery, handleRefresh]);

    useEffect(() => {
        const el = drawerRef.current;
        el?.addEventListener('scroll', handleScroll);
        return () => el?.removeEventListener('scroll', handleScroll);
    }, [handleScroll]);

    useEffect(() => {
        setData([]); setSearchData([]); setPage(1); setHasMoreData(true);
        if (isOpen) void fetchData(1);
    }, [selectedTool]);

    useEffect(() => { if (isOpen && page === 1) void fetchData(1); }, [isOpen]);

    const groups = useMemo(() => {
        const base = debouncedSearchQuery ? uniqueSearchData : uniqueData;
        const filtered = showPinnedOnly ? base.filter((it) => !!it.pinned) : base;
        return groupByDate(filtered);
    }, [debouncedSearchQuery, uniqueSearchData, uniqueData, showPinnedOnly]);

    const handleTitleChange = async (id: number, title: string) => {
        // optimistic update
        setData((prev) => prev.map((it) => (it.id === id ? { ...it, title } : it)));
        setSearchData((prev) => prev.map((it) => (it.id === id ? { ...it, title } : it)));
        await updateHistoryTitle(id, title);
    };

    const handleTagsChange = async (id: number, tags: string[]) => {
        // optimistic update
        const encoded = JSON.stringify(tags);
        setData((prev) => prev.map((it) => (it.id === id ? { ...it, tags: encoded } : it)));
        setSearchData((prev) => prev.map((it) => (it.id === id ? { ...it, tags: encoded } : it)));
        await updateHistoryTags(id, tags);
    };

    const handlePinToggle = async (id: number, pinned: boolean) => {
        // optimistic update
        setData((prev) => prev.map((it) => (it.id === id ? { ...it, pinned } : it)));
        setSearchData((prev) => prev.map((it) => (it.id === id ? { ...it, pinned } : it)));
        await updateHistoryPinned(id, pinned);
    };

    return (
        <Drawer
            ref={drawerRef as any}
            variant={isDrawerPinned ? 'permanent' : 'temporary'}
            anchor='right'
            open={isOpen}
            onClose={onClose}
            ModalProps={{ disableScrollLock: true }}
            sx={{
                flexShrink: 0,
                '& .MuiDrawer-paper': {
                    width: 320,
                    boxSizing: 'border-box',
                    overflowX: 'hidden',
                    backgroundColor: isDarkTheme ? '#1e1e1e' : '#fff',
                    color: isDarkTheme ? '#fff' : '#000'
                }
            }}
        >
            <div style={{ overflow: 'auto' }}>
                <List
                    subheader={
                        <>
                            <div style={{
                                display: 'flex',
                                gap: 8,
                                alignItems: 'center',
                                padding: '8px 12px',
                                backgroundColor: isDarkTheme ? '#1e1e1e' : '#fff',
                                borderBottom: `1px solid ${isDarkTheme ? 'rgba(255, 255, 255, 0.1)' : 'rgba(0, 0, 0, 0.1)'}`
                            }}>
                                <div style={{ flex: 1, display: 'flex', alignItems: 'center', gap: 8, background: isDarkTheme ? '#2d2d2d' : '#f2f2f2', borderRadius: 6, padding: '4px 8px' }}>
                                    <MdSearch style={{ color: isDarkTheme ? '#aaa' : '#666' }} />
                                    <InputBase
                                        placeholder='Search'
                                        value={debouncedSearchQuery}
                                        onChange={(e) => { setDebouncedSearchQuery(e.target.value); setPage(1); }}
                                        fullWidth
                                        sx={{
                                            color: isDarkTheme ? '#fff' : '#000',
                                            '& ::placeholder': {
                                                color: isDarkTheme ? '#aaa' : '#666',
                                                opacity: 1
                                            }
                                        }}
                                    />
                                    {debouncedSearchQuery && (
                                        <IconButton
                                            size='small'
                                            onClick={() => { setDebouncedSearchQuery(''); setPage(1); }}
                                            aria-label='clear search'
                                            sx={{
                                                padding: '2px',
                                                color: isDarkTheme ? '#aaa' : '#666',
                                                '&:hover': {
                                                    color: isDarkTheme ? '#fff' : '#000'
                                                }
                                            }}
                                        >
                                            <MdClose size={18} />
                                        </IconButton>
                                    )}
                                </div>
                                <IconButton
                                    size='small'
                                    onClick={() => setIsDrawerPinned((p) => !p)}
                                    aria-label='pin drawer'
                                    title={isDrawerPinned ? 'Unpin drawer' : 'Pin drawer open'}
                                    sx={{ color: isDarkTheme ? '#fff' : undefined }}
                                >
                                    {isDrawerPinned ? <MdPushPin /> : <MdOutlinePushPin />}
                                </IconButton>
                                <IconButton
                                    size='small'
                                    onClick={() => handleRefresh(false)}
                                    aria-label='refresh'
                                    sx={{ color: isDarkTheme ? '#fff' : undefined }}
                                >
                                    <MdRefresh />
                                </IconButton>
                            </div>
                            <div style={{
                                display: 'flex',
                                gap: 4,
                                alignItems: 'center',
                                padding: '4px 12px',
                                borderBottom: `1px solid ${isDarkTheme ? 'rgba(255, 255, 255, 0.1)' : 'rgba(0, 0, 0, 0.1)'}`,
                                backgroundColor: isDarkTheme ? '#1e1e1e' : '#fff'
                            }}>
                                <Chip
                                    label="All"
                                    size="small"
                                    onClick={() => setShowPinnedOnly(false)}
                                    color={!showPinnedOnly ? 'primary' : 'default'}
                                    variant={!showPinnedOnly ? 'filled' : 'outlined'}
                                    sx={{
                                        ...(showPinnedOnly && isDarkTheme && {
                                            color: '#fff',
                                            borderColor: 'rgba(255, 255, 255, 0.23)'
                                        })
                                    }}
                                />
                                <Chip
                                    label="Pinned"
                                    size="small"
                                    onClick={() => setShowPinnedOnly(true)}
                                    color={showPinnedOnly ? 'primary' : 'default'}
                                    variant={showPinnedOnly ? 'filled' : 'outlined'}
                                    icon={<MdPushPin size={14} />}
                                    sx={{
                                        ...(!showPinnedOnly && isDarkTheme && {
                                            color: '#fff',
                                            borderColor: 'rgba(255, 255, 255, 0.23)',
                                            '& .MuiChip-icon': {
                                                color: '#fff'
                                            }
                                        })
                                    }}
                                />
                            </div>
                            {debouncedSearchQuery && (
                                <div style={{ display: 'flex', gap: 4, alignItems: 'center', padding: '4px 12px', borderBottom: `1px solid ${isDarkTheme ? 'rgba(255, 255, 255, 0.1)' : 'rgba(0, 0, 0, 0.1)'}`, fontSize: '0.75rem', backgroundColor: isDarkTheme ? '#1e1e1e' : '#fff' }}>
                                    <span style={{ opacity: 0.7, minWidth: 'fit-content', color: isDarkTheme ? '#fff' : '#000' }}>Search in:</span>
                                    <Chip
                                        label="All"
                                        size="small"
                                        onClick={() => setSearchIn('all')}
                                        color={searchIn === 'all' ? 'primary' : 'default'}
                                        variant={searchIn === 'all' ? 'filled' : 'outlined'}
                                        sx={{
                                            ...(searchIn !== 'all' && isDarkTheme && {
                                                color: '#fff',
                                                borderColor: 'rgba(255, 255, 255, 0.23)'
                                            })
                                        }}
                                    />
                                    <Chip
                                        label="Title"
                                        size="small"
                                        onClick={() => setSearchIn('title')}
                                        color={searchIn === 'title' ? 'primary' : 'default'}
                                        variant={searchIn === 'title' ? 'filled' : 'outlined'}
                                        sx={{
                                            ...(searchIn !== 'title' && isDarkTheme && {
                                                color: '#fff',
                                                borderColor: 'rgba(255, 255, 255, 0.23)'
                                            })
                                        }}
                                    />
                                    <Chip
                                        label="Tags"
                                        size="small"
                                        onClick={() => setSearchIn('tags')}
                                        color={searchIn === 'tags' ? 'primary' : 'default'}
                                        variant={searchIn === 'tags' ? 'filled' : 'outlined'}
                                        sx={{
                                            ...(searchIn !== 'tags' && isDarkTheme && {
                                                color: '#fff',
                                                borderColor: 'rgba(255, 255, 255, 0.23)'
                                            })
                                        }}
                                    />
                                    <Chip
                                        label="Specification"
                                        size="small"
                                        onClick={() => setSearchIn('code')}
                                        color={searchIn === 'code' ? 'primary' : 'default'}
                                        variant={searchIn === 'code' ? 'filled' : 'outlined'}
                                        sx={{
                                            ...(searchIn !== 'code' && isDarkTheme && {
                                                color: '#fff',
                                                borderColor: 'rgba(255, 255, 255, 0.23)'
                                            })
                                        }}
                                    />
                                </div>
                            )}
                        </>
                    }
                    sx={{ maxHeight: '100%', overflowY: 'auto' }}
                    onScroll={handleScroll}
                >
                    {Object.entries(groups).map(([label, items]) => (
                        items.length > 0 ? (
                            <li key={label} style={{ listStyle: 'none' }}>
                                <ul style={{ padding: 0, margin: 0 }}>
                                    <ListSubheader
                                        sx={{
                                            bgcolor: isDarkTheme ? 'rgba(255, 255, 255, 0.05)' : 'rgba(0, 0, 0, 0.05)',
                                            color: isDarkTheme ? '#fff' : 'rgba(0, 0, 0, 0.87)',
                                            fontWeight: 700,
                                            fontSize: '0.85rem',
                                            lineHeight: '32px',
                                            paddingLeft: '16px',
                                            paddingRight: '16px',
                                            borderBottom: `1px solid ${isDarkTheme ? 'rgba(255, 255, 255, 0.1)' : 'rgba(0, 0, 0, 0.1)'}`,
                                            position: 'sticky',
                                            top: 0,
                                            zIndex: 1
                                        }}
                                    >
                                        {label}
                                    </ListSubheader>
                                    {items.map((it) => (
                                        <HistoryItem
                                            key={it.id}
                                            item={it}
                                            isSelected={selectedItemId === it.id}
                                            onSelect={handleItemClick}
                                            onHover={handleItemHover}
                                            onTitleChange={handleTitleChange}
                                            onTagsChange={handleTagsChange}
                                            onPinToggle={handlePinToggle}
                                            fullCode={fullCodeCache[it.id]}
                                            isDarkTheme={isDarkTheme}
                                        />
                                    ))}
                                </ul>
                            </li>
                        ) : null
                    ))}
                    {loading && (
                        <div style={{ display: 'flex', justifyContent: 'center', padding: 16 }}>
                            <CircularProgress size={20} />
                        </div>
                    )}
                </List>
                {!isLoggedIn && (
                    <div style={{
                        padding: '8px 12px',
                        backgroundColor: isDarkTheme ? '#5d3a1a' : '#fff3e0',
                        borderTop: `1px solid ${isDarkTheme ? '#ff9800' : '#ffb74d'}`,
                        fontSize: '0.75rem',
                        color: isDarkTheme ? '#ffb74d' : '#e65100',
                        textAlign: 'center',
                        position: 'sticky',
                        bottom: 0,
                        zIndex: 1
                    }}>
                        ⚠️ Session-based history will be lost when you close the browser. Login to save your history permanently.
                    </div>
                )}
            </div>
        </Drawer>
    );
};

export default HistoryDrawer;
