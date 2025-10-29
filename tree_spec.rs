use vstd::prelude::*;
use crate::types::*;

verus!{

#[verifier::ext_equal]
pub struct Tree<T>{
    pub id : usize,
    pub val : T,
    pub child : Seq<Tree<T>>,
    // child : Map<usize, Tree<T>>,
}


impl<T> AbsTree<T>{

    pub open spec fn tree_view(self, id:usize) -> Tree<T>
        decreases self.height(id) when self.contains(id) && self.wf()
    {
        let node = self.nodes[id];
        Tree{
            id,
            val : node.val,
            child : node.child.map(
                        |i:int, y:usize|
                        if self.is_parent_of(id, y) {
                            proof{
                                assert(self.height(y) < self.height(id)) by {
                                    self.lemma_height(id, y)
                                }
                            }
                            self.tree_view(y)
                        }
                        else { arbitrary() }
                    )
        }
    }

    // pub open spec fn is_a_tree(self, root:usize) -> bool{
    //     &&& self.wf()
    //     &&& self.contains(root)
    //     &&& forall |y:usize| #[trigger] self.contains(y) ==> self.has_path(root, y)
    // } 
}



impl<T> Tree<T>{

    pub open spec fn revoke(self, id:usize) -> Self
        decreases self
    {
        if self.id == id {
            Self {
                id,
                val : self.val,
                child : seq![]
            }
        }
        else {
            Self{
                id : self.id,
                val : self.val,
                child : self.child.map(
                            |i:int, y:Tree<T>|
                            if self.child.contains(y) {
                                y.revoke(id)
                            }
                            else {
                                arbitrary()
                            }
                        )
            }
        }
    }

}



impl<T> AbsTree<T>{

    // main lemma
    // this lemma covers the normal case : the node(id) to be revoked is a descendant of the root
    pub proof fn lemma_tree_revoke(self, root:usize, id:usize)
        requires
            self.wf(),
            self.contains(root),
            self.contains(id),
            root == id || self.has_path(root, id),
        ensures
            self.revoke(id).tree_view(root)
            ==
            self.tree_view(root).revoke(id)
        decreases self.height(root),
    {
        let s1 = self.revoke_alt(id);
        assert(s1 == self.revoke(id)) by { self.lemma_revoke_alt(id) }
        assert(s1.wf()) by { self.lemma_revoke_wf(id) }
        let res1 = self.revoke(id).tree_view(root);
        let res2 = self.tree_view(root).revoke(id);

        if id == root {
            assert(res2.child.len() == 0);
            assert(res1.child == res2.child);
            assert(res1 == res2);
        }
        else {
            assert(!self.descendants(id).contains(root)) by {
                if self.descendants(id).contains(root) {
                    assert(self.has_path(id, root));
                    assert(self.has_path(id, id)) by {
                        self.lemma_path_trans(id, root, id)
                    }
                    assert(false)
                }
            }
            assert(s1.contains(root)) by {
                self.lemma_revoke_ensures(id)
            }
            assert(s1.nodes[root] == self.nodes[root]) by {
                self.revoke_alt_ensures(id)
            }
            assert(res1.id == root);
            assert(res1.val == self.nodes[root].val);

            assert(res2.id == root);
            assert(res2.val == self.nodes[root].val);

            let child1 = self.revoke(id).nodes[root].child;
            let child2 = self.tree_view(root).child;

            assert(child1 == self.nodes[root].child);

            assert(res1.child == res2.child) by {

                assert(res1.child == 
                    s1.nodes[root].child.map(
                        |i:int, y:usize|
                        if s1.is_parent_of(root, y) {
                            s1.tree_view(y)
                        }
                        else { arbitrary() }
                    )                    
                );

                assert(res2.child ==
                    self.tree_view(root).child.map(
                        |i:int, y:Tree<T>|
                        if self.tree_view(root).child.contains(y) {
                            y.revoke(id)
                        }
                        else {
                            arbitrary()
                        }
                    )
                );

                assert(res1.child.len() == res2.child.len());
                assert forall |i:int| 0 <= i < res1.child.len()
                    implies res1.child[i] == res2.child[i]
                by {

                    let t1 = res1.child[i];
                    let t2 = res2.child[i];
                    assert(t1 == self.revoke(id).tree_view(self.revoke(id).nodes[root].child[i]));
                    assert(t1 == self.revoke(id).tree_view(self.nodes[root].child[i]));
                    assert(t2 == self.tree_view(root).child[i].revoke(id));   
                    assert(t2 == self.tree_view(self.nodes[root].child[i]).revoke(id));             

                    let y = self.nodes[root].child[i];
                    assert(t1 == self.revoke(id).tree_view(y));
                    assert(t2 == self.tree_view(y).revoke(id));

                    assert(self.contains(y));
                    assert(self.is_parent_of(root, y));

                    assert(self.height(y) < self.height(root)) by {
                        self.lemma_height(root, y)
                    }

                    if y == id || self.has_path(y, id){
                        assert(t1 == t2) by { self.lemma_tree_revoke(y, id) }
                    }
                    else{
                        assert(!self.has_path(y, id));
                        assert(y != id);

                        assert(!self.has_path(id, y)) by {
                            if self.has_path(id, y) {
                                self.lemma_has_path_ensures(id, y);

                                if self.is_parent_of(id, y) {
                                    assert(root == id);
                                    assert(false)
                                }
                                let z = choose |z:usize| self.has_path(id, z) && self.is_parent_of(z, y);
                                assert(self.is_parent_of(z, y));
                                assert(z == root);
                                assert(self.has_path(id, root));
                                assert(self.has_path(root, root)) by {
                                    self.lemma_path_trans(root, id, root)
                                }
                                assert(false)
                            }
                        }
                        assert(t1 == t2) by { self.lemma_tree_revoke_aux(y, id) }
                    }
                }
            }
        }
    }

    proof fn lemma_tree_revoke_aux(self, root:usize, id:usize)
        requires
            self.wf(),
            self.contains(root),
            self.contains(id),
            root != id,
            !self.has_path(root, id),
            !self.has_path(id, root),
        ensures
            self.revoke(id).tree_view(root)
            ==
            self.tree_view(root).revoke(id)
        decreases
            self.height(root),
    {
        let s1 = self.revoke_alt(id);
        assert(s1 == self.revoke(id)) by { self.lemma_revoke_alt(id) }
        assert(s1.wf()) by { self.lemma_revoke_wf(id) }
        let res1 = self.revoke(id).tree_view(root);
        let res2 = self.tree_view(root).revoke(id);

        assert(!self.descendants(id).contains(root)) by {
            if self.descendants(id).contains(root) {
                assert(self.has_path(id, root));
                assert(self.has_path(id, id)) by {
                    self.lemma_path_trans(id, root, id)
                }
                assert(false)
            }
        }
        assert(s1.contains(root)) by {
            self.lemma_revoke_ensures(id)
        }
        assert(s1.nodes[root] == self.nodes[root]) by {
            self.revoke_alt_ensures(id)
        }
        assert(res1.id == root);
        assert(res1.val == self.nodes[root].val);

        assert(res2.id == root);
        assert(res2.val == self.nodes[root].val);

        let child1 = self.revoke(id).nodes[root].child;
        let child2 = self.tree_view(root).child;

        assert(child1 == self.nodes[root].child);

        assert(res1.child == res2.child) by {

            assert(res1.child == 
                s1.nodes[root].child.map(
                    |i:int, y:usize|
                    if s1.is_parent_of(root, y) {
                        s1.tree_view(y)
                    }
                    else { arbitrary() }
                )                    
            );

            assert(res2.child ==
                self.tree_view(root).child.map(
                    |i:int, y:Tree<T>|
                    if self.tree_view(root).child.contains(y) {
                        y.revoke(id)
                    }
                    else {
                        arbitrary()
                    }
                )
            );

            assert(res1.child.len() == res2.child.len());
            assert forall |i:int| 0 <= i < res1.child.len()
                implies res1.child[i] == res2.child[i]
            by {

                let t1 = res1.child[i];
                let t2 = res2.child[i];
                assert(t1 == self.revoke(id).tree_view(self.revoke(id).nodes[root].child[i]));
                assert(t1 == self.revoke(id).tree_view(self.nodes[root].child[i]));
                assert(t2 == self.tree_view(root).child[i].revoke(id));   
                assert(t2 == self.tree_view(self.nodes[root].child[i]).revoke(id));             

                let y = self.nodes[root].child[i];
                assert(t1 == self.revoke(id).tree_view(y));
                assert(t2 == self.tree_view(y).revoke(id));

                assert(self.contains(y));
                assert(self.is_parent_of(root, y));
                assert(self.has_path(root, y)) by {
                    self.lemma_parent_to_path(root, y)
                }
                assert(y != id);
                assert(!self.has_path(y, id)) by {
                    if self.has_path(y, id) {
                        self.lemma_parent_to_path(root, y);
                        assert(self.has_path(root, id)) by {
                            self.lemma_path_trans(root, y, id)
                        }
                    }
                }
                assert(!self.has_path(id, y)) by {
                    if self.has_path(id, y) {
                        self.lemma_has_path_ensures(id, y);
                        if self.is_parent_of(id, y) {
                            assert(id == root);
                            assert(false)
                        }
                        else {
                            let z = choose |z:usize| self.has_path(id, z) && self.is_parent_of(z, y);
                            assert(self.is_parent_of(z, y));
                            assert(z == root);
                            assert(false)
                        }
                    }
                }
                assert(self.height(y) < self.height(root)) by { self.lemma_height(root, y) }
                assert(t1 == t2) by { self.lemma_tree_revoke_aux(y, id) }
            }
        }
    }

}


}//verus