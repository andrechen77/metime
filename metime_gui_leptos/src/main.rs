use leptos::*;

fn main() {
    println!("Hello, world!");

    mount_to_body(|| view! { <App/> });
}

#[component]
fn App() -> impl IntoView {
    let (events, set_events) = create_signal(vec![
        Event { day: 0, start: 0, end: 1 },
        Event { day: 1, start: 1, end: 2 },
        Event { day: 2, start: 2, end: 3 },
        Event { day: 3, start: 3, end: 4 },
    ]);
    let (day_span, set_day_span) = create_signal((0, 7));

    let go_left = move |_| set_day_span.update(|(start, _)| *start -= 1);
    let go_right = move |_| set_day_span.update(|(start, _)| *start += 1);

    view! {
        <div class="app-container">
            <ColumnGrid events day_span/>
        </div>
        <button on:click=go_left>{"Left"}</button>
        <button on:click=go_right>{"Right"}</button>

    }
}

#[component]
fn ColumnGrid(
    events: ReadSignal<Vec<Event>>,
    day_span: ReadSignal<(i32, usize)>,
) -> impl IntoView {
    let event_buckets = create_memo(move |_| {
        logging::log!("rerunning memo");
        let (start, span) = day_span.get();
        let mut event_buckets: Vec<_> = (0..span).map(|i| (start + i as i32, Vec::new())).collect();
        events.with(|events| {
            for event in events {
                let index = (event.day - start) as usize;
                if index < event_buckets.len() {
                    event_buckets[index].1.push(*event);
                }
            }
        });
        event_buckets
    });

    view! {
        <div class="column-grid__container">
            <For
                each=move || event_buckets.get()
                key=|(day, _)| *day
                children=|(day, events)| {
                    view! {
                        <div>
                            <p>{format!("Day {}", day)}</p>
                            <For
                                each=move || events.clone()
                                key=|event| *event
                                let:event
                            >
                                <div>{format!("{} - {}", event.start, event.end)}</div>
                            </For>
                        </div>
                    }
                }
            />
        </div>
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
struct Event {
    day: i32,
    start: u32,
    end: u32,
}
