use vstd::prelude::*;

verus! {

    mod vc {
        use vstd::prelude::*;
        //use vstd::math::*;
        use std::ops::Index;

        #[derive(PartialEq, Eq)]
        struct VC(Vec<u64>);

        impl Index<usize> for VC {
            type Output = u64;
            fn index(&self, i:usize) -> &Self::Output
                requires i < self.spec_len(),
            {
                &self.0[i]
            }
        }

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
                // TODO: supremum postcondition
            {
                let mut i = 0;
                while i < self.len()
                    invariant self.spec_len() == other.spec_len(),
                {
                    let c = max_u64(self.index(i), other.index(i));
                    self.0.set(i, c);
                    i += 1;
                }
                //for i in 0..self.len()
                //    invariant self.spec_len() == other.spec_len(),
                //{
                //    let c = max_u64(self.index(i), other.index(i));
                //    self.0.set(i, c);
                //}
            }

            pub fn lessEqual(self, other: VC) -> (r:bool)
                requires
                    self.spec_len() == other.spec_len(),
                //ensures
                //    r <==> forall |i:int| self[i] <= other[i],
            {
                let mut ok = true;
                let mut i = 0;
                while i < self.len()
                    invariant self.spec_len() == other.spec_len(),
                {
                    ok = ok && self.index(i) <= other.index(i);
                }
                ok
            }

        } // impl VC

    } // mod vc

    fn main() {
    }

//  fn inc_ofs(xs:&mut Vec<i8>, i:usize)
//      requires
//          i < old(xs).len(),
//          forall |j:int| old(xs)[j] < 127,
//  {
//      let x = xs[i];
//      let y = x + 1;
//      xs[i] = y;
//  }

//  fn inc_ofs(xs:&mut Vec<i8>, i:usize)
//      requires
//          i < old(xs).len(),
//  {
//      let x = xs.index_mut(i);
//      *x = *x + 1;
//  }

    fn inc_ofs(xs:&mut Vec<i8>, i:usize)
        requires
            i < old(xs).len(), // necessary to index the vector
            forall |j:int| old(xs)[j] < i8::MAX, // necessary to increment any value in the vector
        ensures
            forall |j:int| 0 <= j < old(xs).len() ==>
                if i == j { old(xs)[j] + 1 == xs[j] }
                else      { old(xs)[j]     == xs[j] },
    {
        let x = xs[i];
        xs.set(i, x + 1);
    }
}
