//! ML's lists (`pure/list.ts`): each shares its tail, so that adding to the front takes constant
//! time and keeps the rest of the list alive only through the new cell.

use std::rc::Rc;

pub struct ListCell<T> {
    pub head: T,
    pub tail: List<T>,
}

/// A list, `None` when empty.
pub type List<T> = Option<Rc<ListCell<T>>>;

pub fn cons<T>(head: T, tail: List<T>) -> List<T> {
    Some(Rc::new(ListCell { head, tail }))
}

/// The items from the head on.
pub fn list_iter<T>(list: &List<T>) -> impl Iterator<Item = &T> {
    std::iter::successors(list.as_deref(), |cell| cell.tail.as_deref()).map(|cell| &cell.head)
}

impl<T> Drop for ListCell<T> {
    // Drops a long list in a loop rather than by recursion.
    fn drop(&mut self) {
        let mut tail = self.tail.take();
        while let Some(cell) = tail {
            tail = match Rc::try_unwrap(cell) {
                Ok(mut cell) => cell.tail.take(),
                Err(_) => None,
            };
        }
    }
}
