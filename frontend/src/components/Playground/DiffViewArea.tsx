import React, { useState, useEffect } from 'react';
import { useLocation } from 'react-router-dom';
import { useAtom } from 'jotai';
import { Stack } from '@mui/material';
import { MDBBtn, MDBIcon } from 'mdb-react-ui-kit';
import { VscNewFile } from "react-icons/vsc";
import { IoLogoYoutube } from "react-icons/io5";
import { AiOutlineFullscreen, AiOutlineFullscreenExit } from 'react-icons/ai';
import {
  editorValueAtom,
  outputAtom,
  permalinkAtom,
  languageAtom,
  isFullScreenAtom,
  diffComparisonCodeAtom,
} from '@/atoms';
import ConfirmModal from '@/components/Utils/Modals/ConfirmModal';
import FileUploadButton from '@/components/Utils/FileUpload';
import FileDownload from '@/components/Utils/FileDownload';
import CopyToClipboardBtn from '@/components/Utils/CopyToClipboardBtn';
import CodeDiffEditor from './DiffEditor';
import { getCodeByParmalink } from '@/api/playgroundApi';

interface DiffViewAreaProps {
  editorTheme: string;
  onBackToEditingClick: () => void;
  onFullScreenButtonClick: () => void;
  originalValue?: string;
}

const DiffViewArea: React.FC<DiffViewAreaProps> = ({
  editorTheme,
  onBackToEditingClick,
  onFullScreenButtonClick,
  originalValue
}) => {
  const location = useLocation();
  const [editorValue, setEditorValue] = useAtom(editorValueAtom);
  const [, setOutput] = useAtom(outputAtom);
  const [permalink, setPermalink] = useAtom(permalinkAtom);
  const [language] = useAtom(languageAtom);
  const [isFullScreen] = useAtom(isFullScreenAtom);
  const [diffComparisonCode, setDiffComparisonCode] = useAtom(diffComparisonCodeAtom);


  const [isNewSpecModalOpen, setIsNewSpecModalOpen] = useState(false);
  const [isMobile, setIsMobile] = useState(false);
  const [permalinkInput, setPermalinkInput] = useState('');
  const [isLoadingFromPermalink, setIsLoadingFromPermalink] = useState(false);
  const [permalinkError, setPermalinkError] = useState('');
  const [loadedPermalinkCode, setLoadedPermalinkCode] = useState('');

  // Check screen size on mount and resize for mobile detection
  useEffect(() => {
    const checkScreenSize = () => {
      setIsMobile(window.innerWidth < 768);
    };

    checkScreenSize();
    window.addEventListener('resize', checkScreenSize);

    return () => {
      window.removeEventListener('resize', checkScreenSize);
    };
  }, []);

  // Calculate editor height based on screen size and fullscreen state
  const getEditorHeight = () => {
    if (isFullScreen) {
      return isMobile ? '70vh' : '80vh';
    }
    return isMobile ? '50vh' : '70vh'; // Slightly taller since no output area
  };

  const openModal = () => setIsNewSpecModalOpen(true);
  const closeModal = () => setIsNewSpecModalOpen(false);

  const handleReset = () => {
    setEditorValue('');
    setOutput('');
    const infoElement = document.getElementById('info');
    if (infoElement) {
      infoElement.innerHTML = '';
    }
    setPermalink({ check: null, permalink: null });
    closeModal();
  };

  const handleFileUpload = (file: File) => {
    const reader = new FileReader();
    reader.onload = (e) => {
      if (e.target) {
        const content = e.target.result as string;
        setEditorValue(content);
        setPermalink((prev) => ({ ...prev, permalink: null }));
      }
    };
    reader.readAsText(file);
  };

  const handleDownload = () => {
    const content = editorValue;
    const queryParams = new URLSearchParams(location.search);
    const p = queryParams.get('p');
    const fileName = p ? p : 'code';
    const fileExtension = language.id ?? 'txt';
    return <FileDownload content={content} fileName={fileName} fileExtension={fileExtension} />;
  };

  const extractPermalinkParams = (url: string) => {
    try {
      const urlObj = new URL(url);
      const check = urlObj.searchParams.get('check');
      const permalink = urlObj.searchParams.get('p');
      return { check, permalink };
    } catch {
      // If URL parsing fails, try to extract from a simple permalink format
      const match = url.match(/[?&]check=([^&]+).*[?&]p=([^&]+)/);
      if (match) {
        return { check: match[1], permalink: match[2] };
      }
      return { check: null, permalink: null };
    }
  };

  const handleLoadFromPermalink = async () => {
    if (!permalinkInput.trim()) return;

    setIsLoadingFromPermalink(true);
    setPermalinkError('');

    try {
      const { check, permalink } = extractPermalinkParams(permalinkInput);

      if (!check || !permalink) {
        throw new Error('Invalid permalink format. Please provide a valid URL with check and p parameters.');
      }

      const response = await getCodeByParmalink(check, permalink);
      setLoadedPermalinkCode(response.code);
      setPermalinkError('');
      setPermalinkInput(''); // Clear the input after successful load
    } catch (error: any) {
      if (error.response && error.response.status === 404) {
        setPermalinkError('Code not found. Please check the permalink and try again.');
      } else {
        setPermalinkError(error.message || 'Failed to load code from permalink. Please check the URL and try again.');
      }
      setLoadedPermalinkCode('');
    } finally {
      setIsLoadingFromPermalink(false);
    }
  };

  const handlePermalinkKeyDown = (e: React.KeyboardEvent<HTMLInputElement>) => {
    if (e.key === 'Enter') {
      handleLoadFromPermalink();
    }
  };



  return (
    <div className='row'>
      <div className='col-md-12 mx-auto mb-2'>
        <div className='d-flex justify-content-between align-items-center'>
          <div className='col-md-4'>
            <h2>Compare Specifications</h2>
          </div>
          <div>
            <Stack direction='row' spacing={1}>
              <MDBIcon
                size='lg'
                className='playground-icon'
                onClick={openModal}
                data-tooltip-id='playground-tooltip'
                data-tooltip-content='New Spec'
              >
                <VscNewFile className='playground-icon' role='button' />
              </MDBIcon>
              <ConfirmModal
                isOpen={isNewSpecModalOpen}
                onClose={closeModal}
                title='New Spec'
                message={`Are you sure?
                              This will reset the editor and the output areas`}
                onConfirm={handleReset}
              />
              <MDBIcon
                size='lg'
                className='playground-icon'
                data-tooltip-id='playground-tooltip'
                data-tooltip-content='Upload file'
              >
                <FileUploadButton onFileSelect={handleFileUpload} />
              </MDBIcon>
              <>{handleDownload()}</>
              {permalink.check && permalink.permalink && (
                <MDBIcon
                  size='lg'
                  className='playground-icon'
                  data-tooltip-id='playground-tooltip'
                  data-tooltip-content='Copy Permalink'
                >
                  <CopyToClipboardBtn />
                </MDBIcon>
              )}
              <MDBIcon size='lg' className='playground-icon' onClick={() => onFullScreenButtonClick()}>
                {isFullScreen ? (
                  <AiOutlineFullscreenExit
                    className='playground-icon'
                    data-tooltip-id='playground-tooltip'
                    data-tooltip-content='Exit'
                  />
                ) : (
                  <AiOutlineFullscreen
                    className='playground-icon'
                    data-tooltip-id='playground-tooltip'
                    data-tooltip-content='Fullscreen'
                  />
                )}
              </MDBIcon>
            </Stack>
          </div>
        </div>
      </div>

      {/* Permalink input */}
      <div className='col-12 mb-2'>
        <div className='row align-items-center g-2'>
          <div className='col-md-8'>
            {/* <label htmlFor='permalink-input' className='form-label mb-1'>
                  <small><strong>Load code from permalink (for comparison):</strong></small>
                </label> */}
            <input
              id='permalink-input'
              type='text'
              className={`form-control form-control-md ${editorTheme === 'vs-dark' ? 'bg-dark text-light border-secondary' : ''}`}
              placeholder='Paste permalink here to load code into right side for comparison'
              value={permalinkInput}
              onChange={(e) => setPermalinkInput(e.target.value)}
              onKeyDown={handlePermalinkKeyDown}
              style={editorTheme === 'vs-dark' ? { 
                backgroundColor: '#1e1e1e', 
                color: '#d4d4d4',
                borderColor: '#464647'
              } : {}}
              {...(editorTheme === 'vs-dark' && {
                'data-bs-theme': 'dark'
              })}
            />
          </div>
          <div className='col-md-4'>
            <div className='d-flex gap-2'>
              <MDBBtn
                size='sm'
                color='primary'
                onClick={handleLoadFromPermalink}
                disabled={!permalinkInput.trim() || isLoadingFromPermalink}
              >
                {isLoadingFromPermalink ? 'Loading...' : 'Load Code'}
              </MDBBtn>
              {(loadedPermalinkCode || diffComparisonCode) && (
                <MDBBtn
                  size='sm'
                  color='secondary'
                  onClick={() => {
                    setLoadedPermalinkCode('');
                    setDiffComparisonCode('');
                  }}
                >
                  Clear
                </MDBBtn>
              )}
              <MDBBtn
                // className={`mx-auto my-3 ${isMobile ? 'mobile-run-button' : ''}`}
                color='secondary'
                onClick={onBackToEditingClick}
              >
                {/* <VscEdit style={{ marginRight: '2px' }} /> */}
                Back
              </MDBBtn>
            </div>
          </div>
        </div>
        {permalinkError && (
          <div role='alert' style={{marginTop: '8px', color: 'red'}}>
            <small>{permalinkError}</small>
          </div>
        )}
        {(loadedPermalinkCode || diffComparisonCode) && !permalinkError && (
          <div role='alert' style={{marginTop: '8px', color: 'green'}}>
            <small>✓ Code loaded successfully for comparison {diffComparisonCode ? '(from history)' : '(from permalink)'}</small>
          </div>
        )}
      </div>

      {/* Help text */}
      <div className='col-12 mb-2'>
        <div className='alert alert-info' role='alert'>
          <small>
            The left side shows code for comparison (read-only), the right side shows your current editable code.
            You can edit the right side and see the differences highlighted. Load any saved specification using
            the permalink field above or from history. For detailed instructions, please watch the &nbsp;
            <a
              href='https://www.loom.com/share/1f3f3b1e8f004b6c8a1f3f3b1e8f004b6c8a1'
              target='_blank'
              rel='noopener noreferrer'
            >
              <IoLogoYoutube /> video tutorial on YouTube
            </a>.
          </small>
        </div>
      </div>

      <CodeDiffEditor
        height={getEditorHeight()}
        editorTheme={editorTheme}
        originalValue={diffComparisonCode || loadedPermalinkCode || originalValue || "Use the permalink input above to load code for comparison\n Or click on any history item to load it here\n Click 'Back to Editing Mode' to return to normal editing"}
        modifiedValue={editorValue}
        readOnly={false}
      />

      {/* <MDBBtn
        className={`mx-auto my-3 ${isMobile ? 'mobile-run-button' : ''}`}
        style={{ width: '95%' }}
        color='secondary'
        onClick={onBackToEditingClick}
      >
        <VscEdit style={{ marginRight: '8px' }} />
        Back to Editing Mode
      </MDBBtn> */}
    </div>
  );
};

export default DiffViewArea;