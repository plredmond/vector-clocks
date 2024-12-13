use vstd::prelude::*;

verus! {

    mod vc {
        use vstd::prelude::*;

        #[derive(PartialEq, Eq)]
        struct VC(Vec<u64>);

        fn max_u64(a:u64, b:u64) -> (c:u64)
            ensures
                a <= c,
                b <= c,
                a == c || b == c,
        {
            if a < b { b } else { a }
        }

        impl VC {

            // Specs

            pub closed spec fn spec_len(self) -> usize {
                self.0.len()
            }

            /// Called when you do `x[i]` in a spec for some vc `x`.
            pub closed spec fn spec_index(self, i:int) -> u64 {
                self.0[i]
            }

            // Facade for internal field

            pub fn len(&self) -> (r:usize)
                ensures self.spec_len() == r,
            {
                self.0.len()
            }

            pub fn index(&self, i:usize) -> (r:u64)
                requires i < self.spec_len(),
                ensures self[i as int] == r,
            {
                self.0[i]
            }

            // Interface

            pub fn new(n:usize) -> (vc:VC)
                ensures n == vc.spec_len(),
            {
                //let xs = vec![0; n]; // not yet supported by verus
                let mut xs = Vec::with_capacity(n);
                while xs.len() < n
                    invariant xs.len() <= n,
                {
                    xs.push(0);
                }
                VC(xs)
            }

            pub fn step(&mut self, i:usize)
                requires
                    i < old(self).spec_len(),
                    forall |j:int| old(self)[j] < u64::MAX,
                ensures
                    old(self).spec_len() == self.spec_len(),
                    forall |j:int| 0 <= j < old(self).spec_len() ==>
                        if i == j { old(self)[j] + 1 == self[j] }
                        else      { old(self)[j]     == self[j] }
            {
                let c = 1 + self.index(i);
                //self.0[i] = c; // not yet supported by verus
                self.0.set(i, c);
            }

            pub fn merge(&mut self, other:VC)
                requires
                    old(self).spec_len() == other.spec_len(),
                ensures
                    forall |i:int| 0 <= i < self.spec_len() ==>     other[i] <= self[i],
                    forall |i:int| 0 <= i < self.spec_len() ==> old(self)[i] <= self[i],
            {
                for i in iter: 0..self.len()
                    invariant
                        self.spec_len() == other.spec_len(),
                        iter.end == self.spec_len(),
                        forall |j:int| 0 <= j < i ==> other[j] <= self[j],
                        forall |j:int| 0 <= j < self.spec_len() ==> old(self)[j] <= self[j],
                {
                    let c = max_u64(self.index(i), other.index(i));
                    self.0.set(i, c);
                }
            }

            pub fn lessEqual(self, other: VC) -> (r:bool)
                requires
                    self.spec_len() == other.spec_len(),
                ensures
                    r == forall |i:int| 0 <= i < self.spec_len() ==> self[i] <= other[i],
            {
                let mut ok = true;
                for i in iter: 0..self.len()
                    invariant
                        self.spec_len() == other.spec_len(),
                        iter.end == self.spec_len(),
                         ok ==> forall |j:int| 0 <= j < i ==> self[j] <= other[j],
                        !ok ==> exists |j:int| 0 <= j < i &&  self[j] > other[j],
                        //0 <= i <= self.spec_len(), // why not < the upper bound?
                {
                    //assert(0 <= i < self.spec_len());
                    ok = ok && self.index(i) <= other.index(i);
                }
                ok
            }

        } // impl VC

    } // mod vc

    fn main() {
    }

}