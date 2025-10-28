import React from 'react';
import HistoryDrawer from '@/components/HistoryDrawer/HistoryDrawer';
import type { DrawerComponentProps } from '@/components/HistoryDrawer/types';

const DrawerComponent: React.FC<DrawerComponentProps> = (props) => {
    return <HistoryDrawer {...props} />;
};

export default DrawerComponent;
