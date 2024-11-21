use vstd::prelude::*;

verus! {
use state_machines_macros::tokenized_state_machine;
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

struct_with_invariants!{
    struct C {
        pub count: AtomicU32<_, CountOne::count, _>,
        pub instance: Tracked<CountOne::Instance>,
    }

    spec fn wf(&self) -> bool {
        invariant on count with (instance) is (v: u32, g: CountOne::count) {
            g@.instance == instance@
            && g@.value == v as int
        }
    }
}

fn main() {
    let tracked (Tracked(instance), Tracked(count_token)) = CountOne::Instance::initialize();
    let c = C {
        count: AtomicU32::new(Ghost(Tracked(instance.clone())), 0, Tracked(count_token)),
        instance: Tracked(instance.clone())
    };
    let x = atomic_with_ghost!(&c.count => fetch_add(1);
        ghost cnt => {
            assert(cnt@.instance === c.instance@);
            c.instance.borrow().increment_will_not_overflow_u32(&cnt);
            //assert(cnt@.value == 0);
            c.instance.borrow().inc_one(&mut cnt)
        }
    );
    assert(x == 0);
    let y =
        atomic_with_ghost!(&c.count => load();
        ghost cnt => {
            assert(cnt@.instance === c.instance@);
            instance.finalize(&cnt);
        }
    );
    assert(y == 1);
}

}
