use leptos::*;

fn main() {
    println!("Hello, world!");

    mount_to_body(|| view! { <App/> });
}

#[component]
fn App() -> impl IntoView {
    let (count, set_count) = create_signal(0);

    view! {
        <button
            on:click = move |_| { set_count.update(|count| *count += 1) }
        >
            "Click me: "
            {move || count.get()}
        </button>
    }
}
