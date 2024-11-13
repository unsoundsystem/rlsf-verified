mod singly_linked_list_trivial;
use singly_linked_list_trivial::llist;

fn main() {
    let mut ls = llist::LList::new();
    ls.push_front(1);
    ls.push_front(2);
    ls.push_front(3);

    let x = ls.pop_front();
    let y = ls.pop_front();
    let z = ls.pop_front();
    assert!(x == Some(3usize));
    assert!(y == Some(2usize));
    assert!(z == Some(1usize));
}
