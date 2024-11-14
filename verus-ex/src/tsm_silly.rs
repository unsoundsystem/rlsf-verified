use vstd::prelude::*;

verus! {
use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::atomic_ghost::*;

tokenized_state_machine! {
    CountOne {
        fields {
            #[sharding(variable)]
            pub count: int
        }

        #[invariant]
        pub fn count_one_inv(&self) -> bool {
            self.count == 1 || self.count == 0
        }

        init!{
            initialize() {
                init count = 0;
            }
        }

        transition!{
            inc_one() {
                require(pre.count == 0);
                update count = pre.count + 1;
            }
        }

        property!{
            increment_will_not_overflow_u32() {
                assert 0 <= pre.count < 0xffff_ffff;
            }
        }

        property!{
            finalize() {
                assert pre.count == 1;
            }
        }

        #[inductive(inc_one)]
        fn inc_one_preserve(pre: Self, post: Self) {}

        #[inductive(initialize)]
        fn initialize_establish(post: Self) {}
    }
}

struct C {
    pub count: usize,
    pub count_tok: Tracked<CountOne::count>,
    pub instance: Tracked<CountOne::Instance>,
}

fn main() {
    let tracked (Tracked(instance), Tracked(count_token)) =
        CountOne::Instance::initialize();
    let mut c = C { count: 0, instance: Tracked(instance), count_tok: Tracked(count_token) };
    assert(c.count == c.count_tok@@.value);
    c.count = c.count + 1;
    proof {
        c.instance.borrow_mut().inc_one(c.count_tok.borrow_mut());
        assert(c.count == c.count_tok@@.value);
        assert(c.count == 1);
        c.instance.borrow().finalize(c.count_tok.borrow());
    }
}
}
