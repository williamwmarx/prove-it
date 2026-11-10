// Ported from Z3 (src/util/trail.h, src/util/union_find.h), MIT license, see z3-license.txt. A
// scoped undo trail, and the union-find over it whose merges a pop undoes, which nla's variable
// equivalences and monomial congruence classes use.
//
// The TS trail holds undo closures. Here it holds an undo value of its owner's type `U`; the owner
// pops it with `pop_scope` and `pop_above` and applies each entry, in the same LIFO order. The TS
// union-find calls the handler closures its owner installs; here the owner passes the handler to
// `merge` and `undo`, which call it at the same points.

pub struct TrailStack<U> {
    trail: Vec<U>,
    scopes: Vec<usize>,
}

impl<U> Default for TrailStack<U> {
    fn default() -> TrailStack<U> {
        TrailStack::new()
    }
}

impl<U> TrailStack<U> {
    pub fn new() -> TrailStack<U> {
        TrailStack {
            trail: Vec::new(),
            scopes: Vec::new(),
        }
    }

    pub fn push(&mut self, undo: U) {
        self.trail.push(undo);
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(self.trail.len());
    }

    // pop_scope: drops `count` scopes and returns the trail size to undo down to, which the owner
    // does with `pop_above` until it returns `None`, applying each entry. The entries an undo pushes
    // are popped in the same loop, as in TS.
    pub fn pop_scope(&mut self, count: usize) -> usize {
        if count == 0 {
            return self.trail.len();
        }
        let size = self.scopes[self.scopes.len() - count];
        self.scopes.truncate(self.scopes.len() - count);
        size
    }

    pub fn pop_above(&mut self, size: usize) -> Option<U> {
        if self.trail.len() > size {
            self.trail.pop()
        } else {
            None
        }
    }
}

// The handlers of union_find's context: r2 becomes the root of r1's class. Each receives the
// union-find, which is borrowed for the merge or the undo that calls it.
pub trait UnionFindHandler {
    fn merge_eh(
        &mut self,
        _union_find: &UnionFind,
        _r2: usize,
        _r1: usize,
        _v2: usize,
        _v1: usize,
    ) {
    }

    fn after_merge_eh(
        &mut self,
        _union_find: &UnionFind,
        _r2: usize,
        _r1: usize,
        _v2: usize,
        _v1: usize,
    ) {
    }

    fn unmerge_eh(&mut self, _union_find: &UnionFind, _r2: usize, _r1: usize) {}
}

// No handlers.
impl UnionFindHandler for () {}

// What the union-find's trail closures captured.
pub enum UnionFindUndo {
    MkVar,
    Merge { r1: usize, r2: usize },
}

#[derive(Default)]
pub struct UnionFind {
    finds: Vec<usize>,
    sizes: Vec<usize>,
    nexts: Vec<usize>,
}

impl UnionFind {
    pub fn new() -> UnionFind {
        UnionFind::default()
    }

    pub fn num_vars(&self) -> usize {
        self.finds.len()
    }

    pub fn mk_var<U: From<UnionFindUndo>>(&mut self, trail: &mut TrailStack<U>) -> usize {
        let value = self.finds.len();
        self.finds.push(value);
        self.sizes.push(1);
        self.nexts.push(value);
        trail.push(U::from(UnionFindUndo::MkVar));
        value
    }

    pub fn find(&self, input: usize) -> usize {
        let mut value = input;
        while self.finds[value] != value {
            value = self.finds[value];
        }
        value
    }

    pub fn next(&self, value: usize) -> usize {
        self.nexts[value]
    }

    pub fn merge<U: From<UnionFindUndo>>(
        &mut self,
        trail: &mut TrailStack<U>,
        handler: &mut impl UnionFindHandler,
        input_v1: usize,
        input_v2: usize,
    ) {
        let root1 = self.find(input_v1);
        let root2 = self.find(input_v2);
        if root1 == root2 {
            return;
        }
        let is_swapped = self.sizes[root1] > self.sizes[root2];
        let r1 = if is_swapped { root2 } else { root1 };
        let r2 = if is_swapped { root1 } else { root2 };
        let v1 = if is_swapped { input_v2 } else { input_v1 };
        let v2 = if is_swapped { input_v1 } else { input_v2 };
        handler.merge_eh(self, r2, r1, v2, v1);
        self.finds[r1] = r2;
        self.sizes[r2] += self.sizes[r1];
        self.nexts.swap(r1, r2);
        trail.push(U::from(UnionFindUndo::Merge { r1, r2 }));
        handler.after_merge_eh(self, r2, r1, v2, v1);
    }

    // Applies an entry of the trail, as its TS closure does.
    pub fn undo(&mut self, undo: UnionFindUndo, handler: &mut impl UnionFindHandler) {
        match undo {
            UnionFindUndo::MkVar => {
                self.finds.pop();
                self.sizes.pop();
                self.nexts.pop();
            }
            UnionFindUndo::Merge { r1, r2 } => {
                self.sizes[r2] -= self.sizes[r1];
                self.finds[r1] = r1;
                self.nexts.swap(r1, r2);
                handler.unmerge_eh(self, r2, r1);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct Recorder {
        events: Vec<String>,
    }

    impl UnionFindHandler for Recorder {
        fn merge_eh(
            &mut self,
            _union_find: &UnionFind,
            r2: usize,
            r1: usize,
            v2: usize,
            v1: usize,
        ) {
            self.events.push(format!("m{r2},{r1},{v2},{v1}"));
        }

        fn after_merge_eh(
            &mut self,
            _union_find: &UnionFind,
            r2: usize,
            r1: usize,
            v2: usize,
            v1: usize,
        ) {
            self.events.push(format!("a{r2},{r1},{v2},{v1}"));
        }

        fn unmerge_eh(&mut self, _union_find: &UnionFind, r2: usize, r1: usize) {
            self.events.push(format!("u{r2},{r1}"));
        }
    }

    // Expected values from running union-find.ts on the same steps.
    #[test]
    fn merges_and_undoes_merges_with_handlers() {
        let mut trail = TrailStack::<UnionFindUndo>::new();
        let mut union_find = UnionFind::new();
        let mut recorder = Recorder::default();
        for _ in 0..5 {
            union_find.mk_var(&mut trail);
        }
        union_find.merge(&mut trail, &mut recorder, 0, 1);
        trail.push_scope();
        union_find.merge(&mut trail, &mut recorder, 2, 3);
        union_find.merge(&mut trail, &mut recorder, 3, 1);
        union_find.mk_var(&mut trail);
        union_find.merge(&mut trail, &mut recorder, 5, 4);
        let finds: Vec<usize> = (0..6).map(|value| union_find.find(value)).collect();
        let nexts: Vec<usize> = (0..6).map(|value| union_find.next(value)).collect();
        assert_eq!(finds, [1, 1, 1, 1, 4, 4]);
        assert_eq!(nexts, [1, 2, 3, 0, 5, 4]);
        let size = trail.pop_scope(1);
        while let Some(undo) = trail.pop_above(size) {
            union_find.undo(undo, &mut recorder);
        }
        assert_eq!(union_find.num_vars(), 5);
        let finds: Vec<usize> = (0..5).map(|value| union_find.find(value)).collect();
        let nexts: Vec<usize> = (0..5).map(|value| union_find.next(value)).collect();
        assert_eq!(finds, [1, 1, 2, 3, 4]);
        assert_eq!(nexts, [1, 0, 2, 3, 4]);
        assert_eq!(
            recorder.events.join(" "),
            "m1,0,1,0 a1,0,1,0 m3,2,3,2 a3,2,3,2 m1,3,1,3 a1,3,1,3 m4,5,4,5 a4,5,4,5 u4,5 u1,3 u3,2"
        );
    }
}
