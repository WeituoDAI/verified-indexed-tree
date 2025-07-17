use vstd::prelude::*;

verus!{


pub proof fn lemma_fold_reverse<A, B>(s:Seq<A>, acc:B,  f:spec_fn(B, A) -> B, g:spec_fn(A, B) -> B)
    requires
        forall |a:A, b:B| #[trigger]f(b, a) == g(a, b)
    ensures
        s.fold_left(acc, f) == s.reverse().fold_right(g, acc),
    decreases s.len()
{
    if s.len() == 0 {}
    else {
        let last = s.last();
        let s0 = s.drop_last();
        assert(s.reverse() =~= seq![last] + s0.reverse());

        let res1 = s.fold_left(acc, f);
        let res2 = s.reverse().fold_right(g, acc);
        assert(
            res2 == s.reverse().fold_right_alt(g, acc)
        ) by {
            s.reverse().lemma_fold_right_alt(g, acc)
        }

        assert(
            res1 == f(s0.fold_left(acc, f), last)
        );

        assert(s.reverse().first() == last);
        assert(s.reverse().subrange(1, s.reverse().len() as int) =~= s0.reverse());
        assert(
            res2 == g(last, s0.reverse().fold_right_alt(g, acc))
        );
        assert(
            res2 ==  g(last, s0.reverse().fold_right(g, acc))
        ) by {
            s0.reverse().lemma_fold_right_alt(g, acc)
        }

        assert(
            res2 == f(s0.reverse().fold_right(g, acc), last)
        );
        // assert(
        //     s.fold_left(acc, f) == s.reverse().fold_right(g, acc)
        // ) by
        // {
        lemma_fold_reverse(s0, acc, f, g);
        // }

        // assert(s.reverse().reverse() =~= s);

    }
}


// pub proof fn lemma_fold_reverse_2<A, B>(s:Seq<A>, acc:B,  f:spec_fn(B, A) -> B, g:spec_fn(A, B) -> B)
//     requires
//         forall |a:A, b:B| #[trigger]f(b, a) == g(a, b)
//     ensures
//         s.reverse().fold_left(acc, f) == s.fold_right(g, acc),
// {
//     lemma_fold_reverse(s.reverse(), acc, f, g);
//     assert(s.reverse().reverse() =~= s);
// }




pub open spec fn commutative_foldl<A, B>(f: spec_fn(B, A) -> B) -> bool {
    forall|x: A, y: A, v: B| #[trigger] f(f(v, x), y) == f(f(v, y), x)
}

// For a commutative fold_right operator, any folding order
// (i.e., any permutation) produces the same result.
pub proof fn lemma_fold_left_permutation<A, B>(l1: Seq<A>, l2: Seq<A>, f: spec_fn(B, A) -> B, v: B)
    requires
        commutative_foldl(f),
        l1.to_multiset() == l2.to_multiset(),
    ensures
        l1.fold_left(v, f) == l2.fold_left(v, f),
    decreases l1.len(),
{
    let g = |a:A, b:B| f(b, a);

    assert(vstd::seq_lib::commutative_foldr(g));

    assert(l1.fold_left(v, f) == l1.reverse().fold_right(g, v)) by {
        lemma_fold_reverse(l1, v, f, g)
    };
    assert(l2.fold_left(v, f) == l2.reverse().fold_right(g, v)) by{
        lemma_fold_reverse(l2, v, f, g)
    };

    assert(l1.reverse().to_multiset() =~= l2.reverse().to_multiset()) by{
        lemma_reverse_to_multiset(l1);
        lemma_reverse_to_multiset(l2);
    }

    vstd::seq_lib::lemma_fold_right_permutation(l1.reverse(), l2.reverse(), g, v)
}


proof fn lemma_reverse_to_multiset<A>(s:Seq<A>)
  ensures s.reverse().to_multiset() =~= s.to_multiset()
  decreases s.len(),
{
    broadcast use vstd::seq_lib::group_seq_properties;

    if s.len() == 0 {}
    else {
        let s2 = s.drop_first();
        let e = s.first();
        assert(s =~= seq![e] + s2);
        assert(s.to_multiset() =~= seq![e].to_multiset().add(s2.to_multiset())) by{
            vstd::seq_lib::lemma_multiset_commutative(seq![e], s2)
        }
        assert(s.reverse() =~= s2.reverse().push(e));
        assert(s.reverse().to_multiset() =~= s2.reverse().to_multiset().insert(e));
        lemma_reverse_to_multiset(s2);
    }
}



pub proof fn lemma_remove_value_commut<T>(x:Seq<T>, y:T, z:T)
    ensures
        x.remove_value(y).remove_value(z)
        =~= x.remove_value(z).remove_value(y)
{
    admit()
}


pub proof fn lemma_fold_left_preserves_inv<A, B>
    (l: Seq<A>, f: spec_fn(B, A) -> B, v: B, inv:spec_fn(B) -> bool)
    requires
        inv(v),
        forall |e:A, acc:B| inv(acc) ==> #[trigger]inv(f(acc, e)),
    ensures
        inv(l.fold_left(v, f))
    decreases l.len(),
{
    if l.len() > 0 {
        let l0 = l.drop_last();
        let r0 = l0.fold_left(v, f);
        assert(l.fold_left(v, f) == f(r0, l.last()));
        assert(inv(r0)) by{
            lemma_fold_left_preserves_inv(l0, f, v, inv);
        }
    }
}


pub proof fn lemma_fold_left_preserves_inv_2<A, B>
    (l: Seq<A>, f: spec_fn(B, A) -> B, v: B, inv:spec_fn(B) -> bool, inv_e:spec_fn(A)->bool)
    requires
        inv(v),
        forall |e:A, acc:B| (inv_e(e) && inv(acc)) ==> #[trigger]inv(f(acc, e)),
        forall |e:A| l.contains(e) ==> #[trigger]inv_e(e),
    ensures
        inv(l.fold_left(v, f))
    decreases l.len(),
{
    if l.len() > 0 {
        let l0 = l.drop_last();
        let r0 = l0.fold_left(v, f);
        assert(l.fold_left(v, f) == f(r0, l.last()));
        assert(inv(r0)) by{
            lemma_fold_left_preserves_inv_2(l0, f, v, inv, inv_e);
        }
    }
}




pub proof fn lemma_fold_left_permutation_with_inv<A, B>
    (l1: Seq<A>, l2: Seq<A>, f: spec_fn(B, A) -> B, v: B, inv:spec_fn(B) -> bool)
    requires
        inv(v),
        forall |e:A, acc:B| inv(acc) ==> #[trigger]inv(f(acc, e)),
        forall |x:A, y:A, acc:B| inv(acc) ==> #[trigger]f(f(acc, x), y) == f(f(acc, y), x),
        l1.to_multiset() == l2.to_multiset(),
    ensures
        l1.fold_left(v, f) == l2.fold_left(v, f),
    // decreases l1.len(),
{
    admit()
}


}