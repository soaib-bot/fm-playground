import { useState, useEffect, useContext } from 'react';
import { BrowserRouter as Router, Route, Routes } from 'react-router-dom';
import { AuthProvider, AuthContext } from '@/contexts/AuthContext';
import { Provider as JotaiProvider, useAtom } from 'jotai';
import Nav from '@/components/Utils/Nav';
import Footer from '@/components/Utils/Footer';
import Tour from '@/components/Utils/Tour';
import { loggedInTourSteps, loggedOutTourSteps } from '@/components/Utils/tourSteps';
import { CallBackProps } from 'react-joyride';
import Playground from '@/components/Playground/Playground';
import Login from '@/components/Authentication/Login';
import ProtectedRoutes from '@/components/Authentication/ProtectedRoutes';
import Missing from '@/components/Utils/Missing';
import { isDarkThemeAtom } from '@/atoms';

import { jotaiStore } from '@/atoms';
import '@/assets/style/index.css';
import '@/assets/style/App.css';

const App = () => {
    const [isDarkTheme, setIsDarkTheme] = useAtom(isDarkThemeAtom);
    const [editorTheme, setEditorTheme] = useState(() => {
        const storedTheme = localStorage.getItem('editorTheme');
        return storedTheme || 'vs';
    });
    const [runTour, setRunTour] = useState(false);
    const authContext = useContext(AuthContext);
    const isLoggedIn = authContext?.isLoggedIn ?? false;

    const handleStartTour = () => {
        setRunTour(true);
    };

    const handleTourEnd = (data: CallBackProps) => {
        const { status } = data;
        const finishedStatuses: string[] = ['finished', 'skipped'];

        if (finishedStatuses.includes(status)) {
            setRunTour(false);
        }
    };

    useEffect(() => {
        const tourViewed = localStorage.getItem('tourViewed');
        if (!tourViewed) {
            setRunTour(true);
            localStorage.setItem('tourViewed', 'true');
        }
    }, []);

    // const handleToggleTheme = () => {
    //   setIsDarkTheme((prevIsDarkTheme) => {
    //     const newTheme = !prevIsDarkTheme;
    //     localStorage.setItem('isDarkTheme', newTheme.toString());
    //     return newTheme;
    //   });
    // };

    useEffect(() => {
        const theme = isDarkTheme ? 'dark' : 'light';
        if (theme === 'dark') {
            setEditorTheme('vs-dark');
            localStorage.setItem('editorTheme', 'vs-dark');
        } else {
            setEditorTheme('vs');
            localStorage.setItem('editorTheme', 'vs');
        }
        document.documentElement.setAttribute('data-theme', theme);
    }, [isDarkTheme]);

    return (
        <AuthProvider>
            <JotaiProvider store={jotaiStore}>
                <div className='App' data-theme={isDarkTheme ? 'dark' : 'light'}>
                    <Tour
                        run={runTour}
                        steps={isLoggedIn ? loggedInTourSteps : loggedOutTourSteps}
                        onTourEnd={handleTourEnd}
                    />
                    <Nav isDarkTheme={isDarkTheme} setIsDarkTheme={setIsDarkTheme} onStartTour={handleStartTour} />
                    <Router>
                        <Routes>
                            <Route element={<ProtectedRoutes />}></Route>
                            <Route path='/' element={<Playground editorTheme={editorTheme} />} />
                            <Route path='/login' element={<Login />} />
                            <Route path='*' element={<Missing />} />
                        </Routes>
                    </Router>
                    <Footer />
                </div>
            </JotaiProvider>
        </AuthProvider>
    );
};

export default App;
