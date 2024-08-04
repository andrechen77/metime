use leptos::*;
use leptonic::prelude::*;

fn main() {
    println!("Hello, world!");

    mount_to_body(|| view! { <App/> });
}

#[component]
fn App() -> impl IntoView {
    let events = create_rw_signal(vec![
        create_rw_signal(Event { id: 0, day: 0, start: 0, end: 2 }),
        create_rw_signal(Event { id: 1, day: 1, start: 1, end: 2 }),
        create_rw_signal(Event { id: 2, day: 2, start: 2, end: 3 }),
        create_rw_signal(Event { id: 3, day: 3, start: 3, end: 7 }),
    ]);
    let day_span = create_rw_signal((0, 7));

    let go_left = move |_| day_span.update(|(start, _)| *start -= 1);
    let go_right = move |_| day_span.update(|(start, _)| *start += 1);

    view! {
        <Root default_theme=LeptonicTheme::default()>
            <Stack spacing=Size::Zero>
                <ColumnGrid events day_span=day_span.read_only()/>
                <Stack spacing=Size::Em(1.0) orientation=StackOrientation::Horizontal>
                    <Button on_click=go_left>{"Left"}</Button>
                    <Button on_click=go_right>{"Right"}</Button>
                </Stack>
            </Stack>
        </Root>
    }
}

#[component]
fn ColumnGrid(
    events: RwSignal<Vec<RwSignal<Event>>>,
    day_span: ReadSignal<(i32, usize)>,
) -> impl IntoView {
    let event_buckets = move || {
        logging::log!("Recomputing event buckets");
        let (start, span) = day_span.get();
        let mut event_buckets: Vec<_> = (0..span).map(|i| (start + i as i32, Vec::new())).collect();
        events.with(|events| {
            for event in events {
                let index = event.with(|e| e.day - start) as usize;
                if index < event_buckets.len() {
                    event_buckets[index].1.push(*event);
                }
            }
        });
        event_buckets
    };

    view! {
        <div class="column-grid__container" style:height="80vh" style:width="100%">
            <For
                each=event_buckets
                key=|(day, _)| *day
                children=|(day, events)| view! {
                    <div class="column-grid__column">
                        <p>{format!("Day {}", day)}</p>
                        <div class="column-grid__column-area">
                            <For
                                each=move || events.clone()
                                key=|event| event.with(|event| event.id)
                                let:event
                            >
                                <EventBox event/>
                            </For>
                        </div>
                    </div>
                }
            />
        </div>
    }
}

#[component]
fn EventBox(
    event: RwSignal<Event>,
) -> impl IntoView {
    let text = move || event.with(|event| format!("{} - {}", event.start, event.end));
    let vertical_position = move || event.with(|event| format!("{}%", event.start * 10));
    let height = move || event.with(|event| format!("{}%", (event.end - event.start) * 10));

    view! {
        <div
            class="event-box"
            style:top=vertical_position
            style:height=height
            style:width="100%"
        >{text}</div>
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
struct Event {
    id: u32,
    day: i32,
    start: u32,
    end: u32,
}
