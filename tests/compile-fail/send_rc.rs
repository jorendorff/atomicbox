extern crate atomicbox;

use atomicbox::AtomicBox;
use std::rc::Rc;

fn main() {
    let rc_main = Rc::new("Hello, world!");
    let rc_other = Rc::clone(&rc_main);

    let abox = AtomicBox::new(Box::new(rc_other));
    let handle = std::thread::spawn(move || {
        //~^ ERROR `Rc<&str>` cannot be sent between threads safely
        let value = *abox.into_inner();
        println!("Other thread: {:?}", value);
    });
    handle.join().unwrap();
    println!("Main Thread: {:?}", rc_main);
}
