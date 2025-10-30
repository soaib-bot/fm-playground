import Joyride, { Step, CallBackProps } from 'react-joyride';

interface TourProps {
  run: boolean;
  steps: Step[];
  onTourEnd: (data: CallBackProps) => void;
}

const Tour: React.FC<TourProps> = ({ run, steps, onTourEnd }) => {
  return (
    <Joyride
      run={run}
      steps={steps}
      callback={onTourEnd}
      continuous
      showProgress
      showSkipButton
      styles={{
        options: {
          primaryColor: '#0d6efd',
          zIndex: 10000,
        },
      }}
    />
  );
};

export default Tour;
