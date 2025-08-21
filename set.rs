use vstd::prelude::*;

verus!{


pub proof fn lemma_set_to_seq_no_duplicates<A>(s:Set<A>)
	requires s.finite()
	ensures s.to_seq().no_duplicates()
  decreases s.len()
{
  if s.len() == 0 {}
  else {
    let x = choose |x:A| #[trigger] s.contains(x) 
      && s.to_seq() =~= seq![x] + s.remove(x).to_seq();
    assert(s.remove(x).to_seq().no_duplicates()) by {
      lemma_set_to_seq_no_duplicates(s.remove(x))
    }
    s.remove(x).lemma_to_seq_to_set_id()
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