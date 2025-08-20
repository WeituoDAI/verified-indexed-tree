use vstd::prelude::*;
use crate::types::*;
// use std::collections::HashMap;


verus!{

broadcast use vstd::std_specs::hash::group_hash_axioms;


//efficient implementation
impl<T> IndexTree<T>{
    #[verifier::external_body]
    pub fn take_children(&mut self, id: usize) -> (res:Vec<usize>)
        requires old(self).nodes@.contains_key(id)
        ensures
            self.nodes@.dom() =~= old(self).nodes@.dom(),
            forall |i:usize| i!=id && #[trigger]self.nodes@.contains_key(i) ==> self.nodes@[i] == old(self).nodes@[i],
            self.nodes@[id].id == old(self).nodes@[id].id,
            self.nodes@[id].val == old(self).nodes@[id].val,
            self.nodes@[id].child@ =~= seq![],
            res@ =~= old(self).nodes@[id].child@,
    {
        self.nodes.get_mut(&id).map(|node| {
            std::mem::take(&mut node.child)
        }).unwrap()
    }

    #[verifier::loop_isolation(false)]
    pub fn revoke(&mut self, id:usize)
        requires
            old(self)@.wf(),
            old(self)@.contains(id),
        ensures
            self@.wf(),
            self@ =~= old(self)@.revoke(id),
        decreases
            old(self)@.measure(),
    {
        let children = self.take_children(id);

        proof{
            assert(children@ =~= old(self)@.childs_seq(id));
            assert(self@ =~= old(self)@.remove_edges_from(id));
            assert(self@.wf()) by {
                old(self)@.lemma_remove_edges_from_wf(id)
            }

            assert(forall |j:int| 0 <= j < children@.len() ==> #[trigger]self@.has_no_parent(children@[j])) by{
                old(self)@.lemma_remove_edges_from_ensures(id)
            }
            assert(children@.no_duplicates());

            assert forall |j:int, k:int| 0 <= j < k < children@.len() implies
                !#[trigger]self@.has_path(children@[j], children@[k]) by
            {
                if self@.has_path(children@[j], children@[k]){
                    assert(old(self)@.has_path(children@[j], children@[k])) by{
                        old(self)@.lemma_remove_edges_from_path(id)
                    }
                }
                broadcast use AbsTree::lemma_parent_to_path;
                old(self)@.lemma_path_contradict(id, children@[j], children@[k])
            }
        }
        // about measure
        proof{
            assert(children@.len() > 0 ==> self@.measure() < old(self)@.measure()) by{
                old(self)@.lemma_remove_edges_from_measure(id)
            }
        }

        let ghost prev = *self;


        for i in 0..children.len()
            invariant
                self@.wf(),
                children@.no_duplicates(),

                self@ =~= children@.subrange(0, i as int).fold_left(
                        prev@,
                        |s:AbsTree<T>, x:usize| s.revoke_and_remove_self(x),
                    ),

                //I1
                forall |j:int| i <= j < children@.len() ==> #[trigger]self@.contains(children@[j]),
                
                //I2
                forall |j:int| i <= j < children@.len() ==> #[trigger]self@.has_no_parent(children@[j]),

                //I3
                forall |j:int, k:int| i <= j < k < children@.len() ==>
                   !#[trigger]self@.has_path(children@[j], children@[k]),

                //measure
                children@.len() > 0 ==> prev@.measure() < old(self)@.measure(),
                self@.measure() <= prev@.measure(),            
        {
            let ghost t0 = *self;

            let child = children[i];
            proof{
                assert(self@.contains(child)) by {
                    assert(child == children@.subrange(i as int, children@.len() as int)[0]);
                }
            }
            self.revoke(child);

            let ghost t1 = *self;

            proof{
                t0@.lemma_revoke_wf(child);
                assert(t1@.childs(child).is_empty());
                assert(t1@.contains(child));
                assert(t1@.has_no_parent(child)) by {
                    assert(t0@.has_no_parent(child));
                    if !t1@.has_no_parent(child){
                        let p = choose |p:usize| t1@.is_parent_of(p, child);
                        assert(t1@.is_parent_of(p, child));
                        assert(t0@.is_parent_of(p, child)) by {
                            t0@.lemma_revoke_path0(child)
                        }
                    }
                }
            }

            self.nodes.remove(&child);
            proof{
                assert(self@ =~= t1@.remove_node(child)) by {
                    t1@.lemma_remove_free_node(child)
                }
                assert(
                    children@.subrange(0, i + 1).drop_last()
                    =~= children@.subrange(0, i as int)
                );

                assert(self@.wf()) by {
                    t1@.lemma_remove_node_wf(child)
                }

                //I1
                assert forall |j:int| i + 1 <= j < children@.len() implies #[trigger]self@.contains(children@[j]) by{
                    assert(self@ =~= t0@.revoke_and_remove_self(child));
                    let q = children@[j];
                    assert(q != child);
                    assert(self@.dom() =~= t0@.dom() - t0@.descendants(child) - set![child]) by {
                        t0@.lemma_revoke_and_remove_self_wf(child)
                    }
                    assert(!t0@.descendants(child).contains(q)); // by I5
                }

                //I2
                assert forall |j:int| i + 1 <= j < children@.len() implies #[trigger]self@.has_no_parent(children@[j]) by{
                    let q = children@[j];
                    if !self@.has_no_parent(q){
                        let p = choose |p:usize| self@.is_parent_of(p, q);
                        assert(self@.is_parent_of(p, q));
                        assert(t1@.is_parent_of(p, q)) by{
                            t1@.lemma_remove_node_path0(child)
                        }
                        assert(t0@.is_parent_of(p, q)) by {
                            t0@.lemma_revoke_path0(child)
                        }
                        assert(!t0@.has_no_parent(q));
                    }
                }

                //I3
                assert forall |j:int, k:int| i <= j < k < children@.len() implies
                   !#[trigger]self@.has_path(children@[j], children@[k]) by
                {
                    let p = children@[j];
                    let q = children@[k];
                    if self@.has_path(p, q){
                        assert(t1@.has_path(p, q)) by{
                            t1@.lemma_remove_node_path(child)
                        }
                        assert(t0@.has_path(p, q)) by {
                            t0@.lemma_revoke_path0(child)
                        }
                        t0@.lemma_path_contradict(child, p, q);
                    }
                }
            }

            //measure
            proof{
                assert(self@.measure() <= t0@.measure()) by{
                    t0@.lemma_revoke_and_remove_self_measure(child)
                }
            }
        }

        proof{ old(self)@.main_lemma(id); }

    }

}


}//verus!


