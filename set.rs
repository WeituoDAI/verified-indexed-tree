use vstd::prelude::*;

verus!{



pub broadcast proof fn lemma_set_to_seq_len<A>(s:Set<A>)
	requires s.finite()
	ensures #[trigger]s.to_seq().len() == s.len()
  decreases s.len()
{
  if s.len() == 0 {}
  else {
    let x = choose |x:A| #[trigger] s.contains(x) 
      && s.to_seq() =~= seq![x] + s.remove(x).to_seq();
    assert(s.remove(x).to_seq().len() == s.remove(x).len()) by {
      lemma_set_to_seq_len(s.remove(x))
    }
  }
}

pub broadcast proof fn lemma_set_to_seq_no_duplicates<A>(s:Set<A>)
	requires s.finite()
	ensures #[trigger] s.to_seq().no_duplicates()
  decreases s.len()
{
  if s.len() == 0 {}
  else {
    let x = choose |x:A| #[trigger] s.contains(x) 
      && s.to_seq() =~= seq![x] + s.remove(x).to_seq();
    assert(s.remove(x).to_seq().no_duplicates()) by {
      lemma_set_to_seq_no_duplicates(s.remove(x))
    }
    if s.remove(x).to_seq().contains(x) {
      lemma_set_to_seq_contains_2(s.remove(x), x);
      assert(false);
    }
  }
}

pub proof fn lemma_seq_to_set_drop<A>(s:Seq<A>)
  requires
    s.len() > 0,
    s.no_duplicates(),
  ensures
    s.to_set() =~= s.drop_last().to_set().insert(s.last())
{
  assert forall |a:A| #[trigger]s.to_set().contains(a) implies 
    s.drop_last().to_set().contains(a) || a == s.last() by
  {
    let i = choose |i:int| s[i] == a && 0 <= i < s.len();
    if i == s.len() - 1 {}
    else { assert(s.drop_last()[i] == a) }
  }
}



pub broadcast proof fn lemma_set_to_seq_contains<T>(s:Set<T>, v:T)
	requires
    s.finite(),
    s.contains(v),
	ensures
		#[trigger] s.to_seq().contains(v)
	decreases
		s.len()
{
	if s.len() == 0{}
	else {
    let v0 = choose |x:T| (#[trigger]s.contains(x) &&
        s.to_seq() =~=  Seq::<T>::empty().push(x) + s.remove(x).to_seq());
    if v0 == v {
      assert(s.to_seq()[0] == v0)
    }
    else {
      assert(s.remove(v0).to_seq().contains(v)) by{
        lemma_set_to_seq_contains(s.remove(v0), v);
      }
      let i0 = choose |i:int| 
        (s.remove(v0).to_seq()[i] == v && 0 <= i < s.remove(v0).to_seq().len());
      assert(s.to_seq()[1 + i0] == v);
    }						
	}	
}


pub broadcast proof fn lemma_set_to_seq_contains_2<T>(s:Set<T>, v:T)
	requires
    s.finite(),
    #[trigger]s.to_seq().contains(v),
	ensures
		s.contains(v)
	decreases
		s.len()
{
	if s.len() == 0{}
	else {
    let i0 = choose |i:int| s.to_seq()[i] == v && 0 <= i < s.to_seq().len();
    let v0 = choose |x:T| #[trigger]s.contains(x) &&
          s.to_seq() =~= Seq::<T>::empty().push(x) + s.remove(x).to_seq();
    if i0 == 0{}
    else{
      assert(s.to_seq()[i0] == s.remove(v0).to_seq()[i0 - 1]);
      assert(s.remove(v0).contains(v)) by{
        assert(s.remove(v0).to_seq().contains(v));
        lemma_set_to_seq_contains_2(s.remove(v0), v);
      }
    }
	}
}


pub proof fn lemma_set_map_finite<A, B>(s:Set<A>, f:spec_fn(A) -> B)
    requires s.finite()
    ensures s.map(f).finite(), s.map(f).len() <= s.len(),
    decreases s.len()
{
    let s2 = s.map(f);
    if s.len() == 0 {
        assert(s.is_empty());
        assert(s2.is_empty());
    }
    else {
        let x = s.choose();
        let s0 = s.remove(x);
        assert(s0.len() < s.len());
        assert(s2 =~= s0.map(f).insert(f(x)));
        lemma_set_map_finite(s0, f);
    }
}


pub proof fn lemma_no_duplicates_seq_to_set_to_multiset<A>(s1:Seq<A>, s2:Seq<A>)
  requires
    s1.no_duplicates(),
    s2.no_duplicates(),
    s1.to_set() =~= s2.to_set(),
  ensures
    s1.to_multiset() =~= s2.to_multiset()
{
  s1.lemma_multiset_has_no_duplicates();
  s2.lemma_multiset_has_no_duplicates();

  assert forall |e:A| s1.to_multiset().contains(e) implies s2.to_multiset().contains(e) by {
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    assert(s1.contains(e));
    assert(s1.to_set().contains(e));
    assert(s2.contains(e));
  }

  assert forall |e:A| s2.to_multiset().contains(e) implies s1.to_multiset().contains(e) by {
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    assert(s2.contains(e));
    assert(s2.to_set().contains(e));
    assert(s1.contains(e));
  }
}


pub open spec fn product_set<A, B>(s1:Set<A>, s2:Set<B>) -> Set<(A, B)>{
  Set::new(|e:(A, B)| s1.contains(e.0) && s2.contains(e.1))
}

pub proof fn lemma_product_set_finite<A, B>(s1:Set<A>, s2:Set<B>)
  requires s1.finite(), s2.finite()
  ensures product_set(s1, s2).finite()
  decreases s1.len()
{
  let s = product_set(s1, s2);
  if s1.len() == 0 {
    assert(s1.is_empty());
    assert(s.is_empty())
  }
  else{
    let k = s1.choose();
    let s10 = s1.remove(k);
    assert(s10.len() < s1.len());
    let s0 = product_set(s10, s2);
    assert(s0.finite()) by {
      lemma_product_set_finite(s10, s2)
    }
    let new_elements : Set<(A, B)> = s2.map(|e:B| (k, e));
    assert(new_elements.finite()) by {
      s2.lemma_map_finite(|e:B| (k, e))
    }
    assert(s =~= s0 + new_elements);
  }
}


}//verus!
