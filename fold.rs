use vstd::prelude::*;

verus!{


pub proof fn lemma_remove_value_commut<T>(x:Seq<T>, y:T, z:T)
    ensures
        x.remove_value(y).remove_value(z)
        =~= x.remove_value(z).remove_value(y)
{
    if x.len() == 0 {
        x.index_of_first_ensures(y);
        x.index_of_first_ensures(z);
    }
    else {
        x.index_of_first_ensures(z);
        x.index_of_first_ensures(y);

        let i = x.index_of_first(z);
        let j = x.index_of_first(y);

        match (i, j) {
            (None, None) => {},
            (None, Some(j)) => {
                assert(!x.remove_value(y).contains(z));
                x.remove(j).index_of_first_ensures(z)
            },
            (Some(i), None) =>{
                assert(!x.remove_value(z).contains(y));
                x.remove(i).index_of_first_ensures(y)
            }
            (Some(i), Some(j)) => {
                if y == z {}
                else {
                    assert(i != j);
                    if i < j {
                        assert(x.remove(i).index_of_first(y) == Some(j-1)) by {
                            x.remove(i).index_of_first_ensures(y);
                            assert(x.remove(i)[j-1] == y);
                        }
                        assert(x.remove(j).index_of_first(z) == Some(i)) by {
                            x.remove(j).index_of_first_ensures(z);
                            assert(x.remove(j)[i] == z);
                        }
                    }
                    else{
                        assert(x.remove(i).index_of_first(y) == Some(j)) by {
                            x.remove(i).index_of_first_ensures(y);
                            assert(x.remove(i)[j] == y);
                        }
                        assert(x.remove(j).index_of_first(z) == Some(i-1)) by {
                            x.remove(j).index_of_first_ensures(z);
                            assert(x.remove(j)[i-1] == z);
                        }
                    }
                }
            }
        }
    }
}


pub proof fn lemma_fold_left_preserves_inv<A, B>
    (l: Seq<A>, f: spec_fn(B, A) -> B, v: B, inv:spec_fn(B) -> bool)
    requires
        inv(v),
        forall |e:A, v:B| inv(v) && l.contains(e) ==> #[trigger]inv(f(v, e)),
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

pub proof fn lemma_fold_left_preserves_inv_3<A, B>
    (l: Seq<A>, f: spec_fn(B, A) -> B, v: B, inv:spec_fn(B, Seq<A>) -> bool)
    requires
        inv(v, seq![]),
        forall |i:int| 0 <= i < l.len() ==>
            #[trigger]inv(l.take(i).fold_left(v, f), l.take(i)) ==>
            inv(l.take(i+1).fold_left(v, f), l.take(i+1)),
    ensures
        inv(l.fold_left(v, f), l)
    decreases l.len(),
{
    if l.len() == 0 {
        assert(l =~= seq![]);
    }
    else {
        let l0 = l.drop_last();
        let r0 = l0.fold_left(v, f);
        assert(l.fold_left(v, f) == f(r0, l.last()));
        assert(forall |i:int| 0 <= i < l0.len() ==>
            l0.take(i) =~= l.take(i)
        );
        assert forall |i:int| 0 <= i < l0.len() &&
            #[trigger]inv(l0.take(i).fold_left(v, f), l0.take(i)) implies
            inv(l0.take(i+1).fold_left(v, f), l0.take(i+1)) by
        {
            assert(inv(l.take(i).fold_left(v, f), l.take(i)));
            assert(inv(l.take(i+1).fold_left(v, f), l.take(i+1)));
            assert(l.take(i+1) =~= l0.take(i+1));
            assert(inv(l0.take(i+1).fold_left(v, f), l0.take(i+1)));
        }

        assert(inv(r0, l0)) by {
            lemma_fold_left_preserves_inv_3(l0, f, v, inv);
        }

        assert(l0 =~= l.take(l0.len() as int));
        assert(inv(l.take(l0.len() as int).fold_left(v, f), l.take(l0.len() as int)));
        assert(l.take(l0.len() as int + 1) =~= l);

    }
}

pub proof fn lemma_fold_right_preserves_inv<A, B>
    (l: Seq<A>, f: spec_fn(A, B) -> B, v: B, inv:spec_fn(B) -> bool)
    requires
        inv(v),
        forall |e:A, v:B| (l.contains(e) && inv(v)) ==> #[trigger]inv(f(e, v)),
    ensures
        inv(l.fold_right(f, v))
    decreases l.len(),
{
    if l.len() > 0 {
        let l0 = l.drop_last();
        assert(forall |e:A| #[trigger]l0.contains(e) ==> l.contains(e));
        assert(l.contains(l.last()));
        assert(l.fold_right(f, v) == l0.fold_right(f, f(l.last(), v)));
        lemma_fold_right_preserves_inv(l0, f, f(l.last(), v), inv);
    }
}



pub proof fn lemma_fold_right_commute_one_with_inv<A, B>
    (s:Seq<A>, a: A, f: spec_fn(A, B) -> B, v: B, inv:spec_fn(B)->bool)
    requires
        forall |v:B, x:A, y:A|
            inv(v) && (s.contains(x) || x == a) && (s.contains(y) || y == a)
            ==> #[trigger]f(x, f(y, v)) == f(y, f(x, v)),

        forall |v:B, x:A| (s.contains(x) || x == a) && inv(v) ==> #[trigger]inv(f(x, v)),

        inv(v),
    ensures
        s.fold_right(f, f(a, v)) == f(a, s.fold_right(f, v)),
    decreases s.len(),
{
    if s.len() > 0 {
        assert(forall |x:A| #[trigger]s.drop_last().contains(x) ==> s.contains(x));
        assert(s.contains(s.last()));
        lemma_fold_right_commute_one_with_inv(s.drop_last(), a, f, f(s.last(), v), inv);
    }
}


pub proof fn lemma_fold_right_permutation_with_inv<A, B>(l1: Seq<A>, l2: Seq<A>, f: spec_fn(A, B) -> B, v: B, inv:spec_fn(B)->bool)
    requires
        forall |v:B, x:A, y:A|
            inv(v) && l1.contains(x) && l1.contains(y)
            ==> #[trigger]f(x, f(y, v)) == f(y, f(x, v)),

        forall |v:B, x:A| l1.contains(x) && inv(v) ==> #[trigger]inv(f(x, v)),

        inv(v),

        l1.to_multiset() == l2.to_multiset(),
    ensures
        l1.fold_right(f, v) == l2.fold_right(f, v),
    decreases l1.len(),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;

    if l1.len() > 0 {
        let a = l1.last();
        let i = l2.index_of(a);
        let l2r = l2.subrange(i + 1, l2.len() as int).fold_right(f, v);
        assert(l1.to_multiset().count(a) > 0);

        assert(forall |x:A| #[trigger]l2.contains(x) ==> l2.to_multiset().contains(x));
        assert(forall |x:A| #[trigger]l2.contains(x) ==> l1.contains(x));

        assert(l1.contains(a));

        assert(forall |x:A| #[trigger] l2.subrange(i + 1, l2.len() as int).contains(x) ==> l2.contains(x));
        assert(forall |x:A| #[trigger]l1.drop_last().contains(x) ==> l1.contains(x));
        assert(forall |x:A| #[trigger]l2.subrange(0, i).contains(x) ==> l2.contains(x));


        assert(inv(l2r)) by {
            lemma_fold_right_preserves_inv(l2.subrange(i + 1, l2.len() as int), f, v, inv)
        };


        lemma_fold_right_commute_one_with_inv(l1.drop_last(), a, f, v, inv);
        lemma_fold_right_commute_one_with_inv(l2.subrange(0, i), a, f, l2r, inv);

        l2.lemma_fold_right_split(f, v, i + 1);
        l2.remove(i).lemma_fold_right_split(f, v, i);

        assert(l2.subrange(0, i + 1).drop_last() == l2.subrange(0, i));
        assert(l1.drop_last() == l1.remove(l1.len() - 1));

        assert(l2.remove(i).subrange(0, i) == l2.subrange(0, i));
        assert(l2.remove(i).subrange(i, l2.remove(i).len() as int) == l2.subrange(
            i + 1,
            l2.len() as int,
        ));
        lemma_fold_right_permutation_with_inv(l1.drop_last(), l2.remove(i), f, v, inv);
    } else {
        assert(l2.to_multiset().len() == 0);
    }
}

pub proof fn lemma_fold_left_permutation_with_inv<A, B>
    (l1: Seq<A>, l2: Seq<A>, f: spec_fn(B, A) -> B, v: B, inv:spec_fn(B) -> bool)
    requires
        forall |v:B, x:A, y:A|
            inv(v) && l1.contains(x) && l1.contains(y)
            ==> #[trigger]f(f(v, x), y) == f(f(v, y), x),

        forall |v:B, x:A| l1.contains(x) && inv(v) ==> #[trigger]inv(f(v, x)),

        inv(v),

        l1.to_multiset() == l2.to_multiset(),
    ensures
        l1.fold_left(v, f) == l2.fold_left(v, f),
{

    let g = |a:A, b:B| f(b, a);
    assert((|b:B, a:A| g(a, b)) =~= f);

    assert(l1.fold_left(v, f) == l1.reverse().fold_right(g, v)) by {
        l1.lemma_reverse_fold_right(v, g)
    };
    assert(l2.fold_left(v, f) == l2.reverse().fold_right(g, v)) by{
        l2.lemma_reverse_fold_right(v, g)
    };

    assert(l1.reverse().to_multiset() =~= l2.reverse().to_multiset()) by{
        l1.lemma_reverse_to_multiset();
        l2.lemma_reverse_to_multiset();
    }

    assert(forall |x:A| #[trigger] l1.reverse().contains(x) ==> l1.contains(x));
    assert(forall |x:A| #[trigger] l2.reverse().contains(x) ==> l2.contains(x));

    lemma_fold_right_permutation_with_inv(l1.reverse(), l2.reverse(), g, v,
        inv,
    );
}

}