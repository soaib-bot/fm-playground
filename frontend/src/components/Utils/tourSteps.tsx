import { Step } from 'react-joyride';

export const tourSteps: Step[] = [
  {
    target: '#tool-selector',
    content: 'This is the tool selector. You can choose from a variety of formal methods tools here.',
    disableBeacon: true,
    title: 'Tool Selector',
  },
  {
    target: '#input-area',
    content: 'This is the input area. You can write your code here.',
    title: 'Input Area',
  },
  {
    target: '#input-actions',
    content: 'Here you can find a set of actions to manage your code, such as creating a new file, uploading, downloading, and sharing a permalink.',
    title: 'Code Actions',
  },
  {
    target: '#diff-view-button',
    content: 'You can also compare two different specifications using the diff view.',
    title: 'Diff View',
  },
  {
    target: '#run-button',
    content: 'Click this button to run the selected tool and see the output.',
    title: 'Run Button',
  },
  {
    target: '#output-area',
    content: 'The output of the tool will be displayed here.',
    title: 'Output Area',
  },
  {
    target: '#history-button',
    content: 'You can view your past executions in the history drawer.',
    title: 'History Drawer',
  },
  {
    target: '#search-history-input',
    content: 'You can search your history by keyword.',
    title: 'Search History',
  },
  {
    target: '#pin-history-button',
    content: 'You can pin the history drawer to keep it open.',
    title: 'Pin History',
  },
];

export const loggedOutTourSteps: Step[] = [
  ...tourSteps,
  {
    target: '#login-button',
    content: 'You can log in to save your history permanently.',
    title: 'Login',
  },
];

export const loggedInTourSteps: Step[] = [
  ...tourSteps,
  {
    target: '#login-button',
    content: 'You are logged in, so your history will be saved permanently.',
    title: 'Logged In',
  },
];
