import { Button, ButtonGroup, ThemeProvider } from '@mui/material';
import { useState } from 'react';
import theme from './theme';
import CalendarGrid from './CalendarGrid';

function App() {
  const [events, setEvents] = useState([
    { id: 1, day: 1, start: 1, end: 2 },
    { id: 2, day: 1, start: 3, end: 4 },
    { id: 3, day: 2, start: 12, end: 17 },
  ]);
  const [daySpan, setDaySpan] = useState({ start: 0, numDays: 7 });

  const shiftDaySpan = (shift: number) => {
    setDaySpan(prevDaySpan => ({ ...prevDaySpan, start: prevDaySpan.start + shift }));
  };

  return (
    <ThemeProvider theme={theme}>
      <div style={{ height: "80vh", overflow: "auto" }}>
        <CalendarGrid events={events} daySpan={daySpan} pixPerHour={30} />
      </div>
      <ButtonGroup>
        <Button onClick={() => shiftDaySpan(-1)}>Left</Button>
        <Button onClick={() => shiftDaySpan(1)}>Right</Button>
      </ButtonGroup>
    </ThemeProvider>
  );
}

export default App;
