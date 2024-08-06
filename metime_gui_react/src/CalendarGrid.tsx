import { Box } from "@mui/material";
import "./CalendarGrid.css";

interface Event {
  id: number,
  day: number,
  start: number,
  end: number
}

/// Converts a time, in hours, into which percent of the column day area's
/// height corresponds to that time.
function timeToPercent(time: number): number {
  return time / 24;
}

interface CalendarGridProps {
  events: Event[];
  daySpan: { start: number, numDays: number };
  pixPerHour: number;
}
function CalendarGrid({ events, daySpan, pixPerHour }: CalendarGridProps) {
  const days: { day: number, events: Event[] }[] = Array.from({ length: daySpan.numDays }, (_, i) => ({
    day: i + daySpan.start,
    events: [],
  }));

  events.forEach(event => {
    if (event.day >= daySpan.start && event.day < daySpan.start + daySpan.numDays) {
      days[event.day - daySpan.start].events.push(event);
    }
  });

  return (
    <div className="calendar-grid__container" style={{ height: `${pixPerHour * 24}px` }}>
      {Array.from({ length: daySpan.numDays }, (_, i) => i + daySpan.start).map(day => (
        <div key={day} className="calendar-grid__column">
          <div className="calendar-grid__column__header">
            day {day}
          </div>
          <div className="calendar-grid__column__day-area">
            {days[day - daySpan.start].events.map(event => (
              <Box
                key={event.id}
                typography="body2"
                className="calendar-grid__column__day-area__event"
                style={{
                  top: `${timeToPercent(event.start) * 100}%`,
                  height: `max(${timeToPercent(event.end - event.start) * 100}%, 50px)`,
                }}
              >
                Event {event.id}
                {event.day}: {event.start} - {event.end}
              </Box>
            ))}
          </div>
        </div>
      ))}
    </div>
  )
}

export default CalendarGrid;
