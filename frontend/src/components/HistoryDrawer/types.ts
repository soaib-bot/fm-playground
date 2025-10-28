export interface HistoryItemDTO {
    id: number;
    time?: string;
    time_iso?: string | null;
    check: string;
    code: string;
    permalink: string;
    title?: string;
    tags?: string | string[] | null;
    pinned?: boolean;
}

export type OnItemSelect = (check: string, permalink: string, code: string, itemId?: number) => void;

export interface DrawerComponentProps {
    isOpen: boolean;
    onClose: () => void;
    onItemSelect: OnItemSelect;
    isDarkTheme?: boolean;
    isLoggedIn: boolean;
    selectedTool?: string;
}
