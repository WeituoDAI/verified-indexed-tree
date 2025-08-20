use vstd::prelude::*;
// use std::collections::HashMap;
use crate::types::*;

verus!{


impl<T> NodeAbs<T>{
    pub open spec fn remove_child(self, j:usize) -> Self{
        Self{
            id : self.id,
            val : self.val,
            child : self.child.remove_value(j),
        }
    }

    proof fn lemma_remove_child_commut()
        ensures
            crate::fold::commutative_foldl(
                |x:Self, y:usize| Self::remove_child(x, y)
            )
    {
        let f = |x:Self, y:usize| Self::remove_child(x, y);
        assert forall|x: usize, y: usize, v: Self| true implies #[trigger] f(f(v, x), y) == f(f(v, y), x) by
        {
            let r1 = f(f(v, x), y);
            let r2 = f(f(v, y), x);
            assert(r1.id == r2.id);
            assert(r1.val == r2.val);
            assert(r1.child =~= v.child.remove_value(x).remove_value(y));
            assert(r2.child =~= v.child.remove_value(y).remove_value(x));
            crate::fold::lemma_remove_value_commut(v.child, x, y);
        }
    }
}


// for further use, we should reconsider the visibility of spec fn
impl<T> AbsTree<T>{
    pub open spec fn dom(self) -> Set<usize>{
        self.nodes.dom()
    }

    #[verifier::inline]
    pub open spec fn contains(self, id:usize) -> bool{
        self.nodes.contains_key(id)
    }

    // may make this closed
    pub open spec fn is_parent_of(self, parent:usize, child:usize) -> bool{
        &&& self.contains(parent)
        &&& self.contains(child)
        &&& self.nodes[parent].child.contains(child)
    }

    pub closed spec fn has_path(self, parent:usize, child:usize) -> bool{
        exists |i:int| self.has_path_i(parent, child, i)
    }

    pub closed spec fn has_path_i(self, parent:usize, child:usize, i:int) -> bool
        decreases i
    {
        if i <= 0 { false }
        else if i == 1 { self.is_parent_of(parent, child) }
        else {
            exists |z:usize| self.is_parent_of(parent, z) && self.has_path_i(z, child, i-1)
        }
    }

    pub open spec fn descendants(self, id:usize) -> Set<usize>{
        Set::new(|x:usize| self.has_path(id, x))
    }

    pub open spec fn childs(self, id:usize) -> Set<usize>{
        Set::new(|x:usize| self.is_parent_of(id, x))
    }

    pub open spec fn childs_seq(self, id:usize) -> Seq<usize>{
        self.nodes[id].child
    }

    pub open spec fn has_no_parent(self, id:usize) -> bool{
        forall |i:usize| !self.is_parent_of(i, id)
    }
}


// wf predicates
impl<T> AbsTree<T>{
    pub open spec fn wf_0(self) -> bool{
        &&& forall |i:usize| #[trigger] self.contains(i) ==>
                self.nodes[i].child.to_set().subset_of(self.dom())
        &&& forall |i:usize| #[trigger] self.contains(i) ==>
                self.nodes[i].child.no_duplicates()
    }

    pub open spec fn finite(self) -> bool
    {
        self.dom().finite()
    }

    pub open spec fn acyclic(self) -> bool{
        forall |i:usize| ! #[trigger]self.has_path(i, i)
    }

    pub open spec fn no_common_child(self) -> bool{
        forall |i:usize, j:usize, k:usize|
            self.is_parent_of(i, k) && self.is_parent_of(j, k)
            ==> i == j
    }

    pub open spec fn wf(self) -> bool{
        &&& self.wf_0()
        &&& self.finite()
        &&& self.no_common_child()
        &&& self.acyclic()
    }
}


// tree operations:
// remove_node, revoke, revoke_and_remove_self, remove_one_edge, remove_edges_from
impl<T> AbsTree<T>{
    spec fn spec_nodes_remove(id:usize, x:Map<usize, NodeAbs<T>>, y:usize) -> Map<usize, NodeAbs<T>>
        recommends
            x.contains_key(y) 
    {
        x.insert(y, x[y].remove_child(id))
    }

    proof fn spec_nodes_remove_commut(id:usize)
        ensures
            crate::fold::commutative_foldl(
                |x:Map<usize, NodeAbs<T>>, y:usize| Self::spec_nodes_remove(id, x, y)
            )
    {
        let f = |x:Map<usize, NodeAbs<T>>, y:usize| Self::spec_nodes_remove(id, x, y);
        assert forall|x: usize, y: usize, v: Map<usize, NodeAbs<T>>| true implies #[trigger] f(f(v, x), y) == f(f(v, y), x) by
        {}
    }

    pub closed spec fn remove_edges_to(self, id:usize) -> Self{
        let nodes = self.nodes;
        let dom = nodes.dom();
        let seq = dom.to_seq(); 
        let nodes = seq.fold_left(nodes, |x:Map<usize, NodeAbs<T>>, y:usize|
            Self::spec_nodes_remove(id, x, y)
        );
        Self{ nodes }
    }

    proof fn lemma_remove_edges_to_0(pre:Map<usize, NodeAbs<T>>, id:usize, seq:Seq<usize>)
        requires
            pre.dom().finite(),
            seq.to_set().subset_of(pre.dom()),

        ensures 
            seq.fold_left(pre, |x:Map<usize, NodeAbs<T>>, y:usize|
                Self::spec_nodes_remove(id, x, y)
            ).dom() =~= pre.dom()
        decreases seq.len(),
    {
        if seq.len() == 0 {}
        else {
            let seq1 = seq.drop_last();
            let last = seq.last();
            let f = |x:Map<usize, NodeAbs<T>>, y:usize|
                Self::spec_nodes_remove(id, x, y);
            let res1 = seq1.fold_left(pre, f);
            assert(res1.dom() =~= pre.dom()) by {Self::lemma_remove_edges_to_0(pre, id, seq1)};         
            let res = seq.fold_left(pre, f);
            assert(res =~= f(res1, last));
            assert(res =~= 
                Self::spec_nodes_remove(id, res1, last)
            );
            assert(res1.dom() =~= pre.dom());
        }
    }

    proof fn lemma_remove_edges_to_1(pre:Map<usize, NodeAbs<T>>, post:Map<usize, NodeAbs<T>>, id:usize, seq:Seq<usize>)
        requires
            pre.dom().finite(),
            seq.to_set().subset_of(pre.dom()),
            seq.no_duplicates(),
            post =~=
                seq.fold_left(pre, |x:Map<usize, NodeAbs<T>>, y:usize|
                    Self::spec_nodes_remove(id, x, y)),
        ensures 
            post.dom() =~= pre.dom(),
            forall |i:usize| #[trigger]seq.contains(i) ==>
                post[i] =~=
                pre[i].remove_child(id),
            forall |i:usize| !#[trigger]seq.contains(i) ==>
                post[i] =~= pre[i],

        decreases seq.len(),
    {
        Self::lemma_remove_edges_to_0(pre, id, seq);
        assert(post.dom() =~= pre.dom());
        if seq.len() == 0 {}
        else {
            let f = |x:Map<usize, NodeAbs<T>>, y:usize|
                Self::spec_nodes_remove(id, x, y);
            let seq1 = seq.drop_last();
            let last = seq.last();
            let res1 = seq1.fold_left(pre, f);
            let res = seq.fold_left(pre, f);
            Self::lemma_remove_edges_to_1(pre, res1, id, seq1);
            assert(res =~= f(res1, last));

            assert forall |i:usize| !#[trigger]seq.contains(i) implies
                post[i] =~= pre[i] by
            {
                assert(!seq1.contains(i));
            }


            assert forall |i:usize| #[trigger]seq.contains(i) implies
                post[i] =~=
                pre[i].remove_child(id) by
            {
                assert(
                    res =~= Self::spec_nodes_remove(id, res1, last)
                );

                if i != last {
                    assert(seq =~= seq1.push(last));
                    assert(seq1.contains(i));
                }
                else{
                    assert(post[last] =~= res1[last].remove_child(id));
                    assert(res1[last] =~= pre[last]) by {
                        assert(!seq1.contains(last)) by {
                            assert(seq.no_duplicates())
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_remove_edges_to_ensures(pre:Self, post:Self, id:usize)
        requires
            pre.finite(),
            post =~= pre.remove_edges_to(id),
        ensures
            post.dom() =~= pre.dom(),
            forall |i:usize| #[trigger]pre.contains(i) ==>
                post.nodes[i] =~=
                pre.nodes[i].remove_child(id),
    {
        let dom = pre.dom();
        let seq = dom.to_seq();
        assert(seq.no_duplicates()) by {
            crate::set::lemma_set_to_seq_no_duplicates(dom)
        }
        dom.lemma_to_seq_to_set_id();
        Self::lemma_remove_edges_to_1(pre.nodes, post.nodes, id, seq);
    }

    proof fn lemma_remove_edges_to_twice(self, id:usize)
        requires
            self.wf(),
            self.contains(id),
        ensures
            self.remove_edges_to(id).remove_edges_to(id) =~= self.remove_edges_to(id)
    {
        let r1 = self.remove_edges_to(id);
        let r2 = r1.remove_edges_to(id);
        Self::lemma_remove_edges_to_ensures(self, r1, id);
        Self::lemma_remove_edges_to_ensures(r1, r2, id);
        assert(r2.dom() =~= r1.dom());

        assert(forall |i:usize|
            #[trigger] self.contains(i) ==>
                r1.nodes[i] =~= self.nodes[i].remove_child(id)
        );
        assert(forall |i:usize|
            #[trigger] self.contains(i) ==>
                r2.nodes[i] =~= self.nodes[i].remove_child(id).remove_child(id)
        );

        assert forall |i:usize|
            #[trigger] self.contains(i)
            implies
            self.nodes[i].remove_child(id) =~= self.nodes[i].remove_child(id).remove_child(id)
        by {
            let child = self.nodes[i].child;
            assert(child.no_duplicates());
            assert(!child.remove_value(id).contains(id)) by {
                child.index_of_first_ensures(id)
            }
            child.remove_value(id).index_of_first_ensures(id);
        }
    }
        
    pub open spec fn remove_node(self, id:usize) -> Self
    {
        if self.contains(id){
            let s = self.remove_edges_to(id);
            Self{
                nodes : s.nodes.remove(id)
            }
        }
        else {
            self
        }
    }

    proof fn lemma_remove_node_ensures(self, id:usize)
        requires
            self.finite(),
        ensures
            !self.contains(id) ==> self.remove_node(id) =~= self,
            self.contains(id) ==>
                self.remove_node(id).dom() =~= self.dom().remove(id),
            self.contains(id) ==>
                forall |i:usize| #[trigger]self.remove_node(id).contains(i) ==>
                    self.remove_node(id).nodes[i] =~=
                    self.nodes[i].remove_child(id),
            self.remove_node(id).finite(),
    {
        if self.contains(id){
            let s = self.remove_edges_to(id);
            Self::lemma_remove_edges_to_ensures(self, s, id)
        }
    }

    pub open spec fn revoke(self, id:usize) -> Self{
        self.descendants(id).to_seq().fold_left(
            self,
            |s:Self, y:usize| s.remove_node(y)
        )
    }

    pub proof fn lemma_revoke_ensures(self, id:usize)
        requires
            self.wf(),
        ensures
            self.revoke(id).dom() =~= self.dom() - self.descendants(id)
    {
        assert(self.descendants(id).finite()) by{
            self.lemma_descendants(id)
        }
        self.lemma_revoke_ensures_aux(self.descendants(id).to_seq());
        self.descendants(id).lemma_to_seq_to_set_id()
    }

    proof fn lemma_revoke_ensures_aux(self, seq:Seq<usize>)
        requires
            self.wf(),
        ensures
            seq.fold_left(
                self,
                |s:Self, y:usize| s.remove_node(y)
            ).dom()
            =~= self.dom() - seq.to_set(),
        decreases seq.len()
    {
        let f = |s:Self, y:usize| s.remove_node(y);
        if seq.len() == 0 {}
        else {
            let seq1 = seq.drop_last();
            let last = seq.last();
            let r1 = seq1.fold_left(self, f);
            self.lemma_revoke_ensures_aux(seq1);
            assert(r1.dom() =~= self.dom() - seq1.to_set());
            let res = seq.fold_left(self, f);
            assert(res =~= r1.remove_node(last));
            r1.lemma_remove_node_ensures(last);
            assert(res.dom() =~= r1.dom().remove(last));
            assert(res.dom() =~= self.dom() - seq1.to_set() - set![last]);
            assert(self.dom() - seq1.to_set() - set![last] 
                =~= self.dom() - (seq1.to_set() + set![last])
            );
            assert(seq1.to_set() + set![last] =~= seq.to_set()) by {
                assert(seq =~= seq1.push(last));
            }
        }
    }

    pub open spec fn revoke_and_remove_self(self, id:usize) -> Self{
        self.revoke(id).remove_node(id)
    }

    pub open spec fn remove_one_edge(self, parent:usize, child:usize) -> Self
    {
        if self.contains(parent){
            let nodes = self.nodes;
            let node = nodes[parent];
            let new_node = NodeAbs{
                val : node.val,
                id : node.id,
                child : node.child.remove_value(child),
            };   
            let new_nodes = nodes.insert(parent, new_node);
            Self{
                nodes : new_nodes
            }
        }
        else {
            self
        }
    }

    pub open spec fn remove_edges_from(self, parent:usize) -> Self{
        if self.contains(parent){
            let node = self.nodes[parent];
            let new_node = NodeAbs{
                id : node.id,
                child : seq![],
                val : node.val,
            };
            Self{
                nodes : self.nodes.insert(parent, new_node)
            }
        }
        else {
            self
        }
    }
}


// lemmas for path
impl<T> AbsTree<T>{
    pub proof fn has_path_ensures(self, x:usize, y:usize)
        requires self.has_path(x, y)
        ensures self.contains(x), self.contains(y)
    {
        let i = choose |i:int| self.has_path_i(x, y, i);
        self.has_path_i_ensures(x, y, i);
    }

    proof fn has_path_i_ensures(self, x:usize, y:usize, i:int)
        requires self.has_path_i(x, y, i)
        ensures self.contains(x), self.contains(y)
        decreases i
    {
        if i == 1 {}
        else {
            let z = choose |z:usize| self.is_parent_of(x, z) && self.has_path_i(z, y, i-1);
            self.has_path_i_ensures(z, y, i-1)
        }
    }

    pub proof fn lemma_path_trans(self, x:usize, y:usize, z:usize)
        requires
            self.has_path(x, y),
            self.has_path(y, z),
        ensures
            self.has_path(x, z),
    {
        let i = choose |i:int| self.has_path_i(x, y, i);
        let j = choose |j:int| self.has_path_i(y, z, j);
        self.lemma_has_path_i_trans(x, y, z, i, j)
    }

    proof fn lemma_has_path_i_trans(self, x:usize, y:usize, z:usize, i:int, j:int)
        requires
            self.has_path_i(x, y, i),
            self.has_path_i(y, z, j),
        ensures
            self.has_path_i(x, z, i + j)
        decreases i
    {
        if i == 1 {}
        else if i > 1 {
            let w = choose |w:usize| self.is_parent_of(x, w) && self.has_path_i(w, y, i-1);
            assert(self.has_path_i(w, z, i - 1 + j)) by {
                self.lemma_has_path_i_trans(w, y, z, i-1, j)
            }
        }
    }

    pub proof fn lemma_path_contradict(self, x:usize, y:usize, z:usize)
        requires
            self.wf(), //no common child
            self.is_parent_of(x, y),
            self.is_parent_of(x, z),
            y != z,
        ensures
            !self.has_path(y, z),
            // !self.has_path(z, y),
    {
        if self.has_path(y, z){
            self.lemma_has_path_ensures(y, z);
            if self.is_parent_of(y, z){
                assert(y == x);
                assert(self.is_parent_of(x, y));
                self.lemma_parent_to_path(x, y);
                assert(false);
            }   
            else{
                let w = choose |w:usize| self.has_path(y, w) && self.is_parent_of(w, z);
                assert(self.is_parent_of(w, z));
                assert(w == x);
                assert(self.has_path(y, x));
                assert(self.has_path(x, y)) by {self.lemma_parent_to_path(x, y)};
                assert(self.has_path(x, x)) by {self.lemma_path_trans(x, y, x)};
            }
        }
    }

    pub broadcast proof fn lemma_parent_to_path(self, x:usize, y:usize)
        requires
            self.is_parent_of(x, y),
        ensures
            #[trigger]self.has_path(x, y)
    {
        assert(self.has_path_i(x, y, 1))
    }

    pub proof fn lemma_has_path_i_ensures(self, x:usize, y:usize, i:int)
        requires
            self.has_path_i(x, y, i)
        ensures
            i >= 1,
            i == 1 ==> self.is_parent_of(x, y),
            i > 1 ==>
                exists |z:usize| self.has_path_i(x, z, i-1) && self.is_parent_of(z, y)
        decreases i
    {
        if i > 1 {
            let z = choose |z:usize| self.is_parent_of(x, z) && self.has_path_i(z, y, i-1);
            if i == 2{
                assert(self.is_parent_of(z, y));
                assert(self.has_path_i(x, z, 1));
            }
            else {
                self.lemma_has_path_i_ensures(z, y, i-1);
                let w = choose |w:usize|
                    self.has_path_i(z, w, i-2) && self.is_parent_of(w, y);
                assert(self.is_parent_of(x, z));
                assert(self.has_path_i(x, w, i-1))
            }
        }
    }

    pub proof fn lemma_has_path_ensures(self, x:usize, y:usize)
        requires
            self.has_path(x, y)
        ensures
            self.contains(x),
            self.contains(y),
            self.is_parent_of(x, y)
            ||
            (
                exists |z:usize| self.has_path(x, z) && self.is_parent_of(z, y)
                &&
                exists |z:usize| self.is_parent_of(x, z) && self.has_path(z, y)
            )
    {
        self.has_path_ensures(x, y);
        let i = choose |i:int| self.has_path_i(x, y, i);
        if i == 1 {
            assert(self.is_parent_of(x, y))
        }
        else {
            let z = choose |z:usize| self.is_parent_of(x, z) && self.has_path_i(z, y, i-1);
            assert(self.has_path_i(z, y, i-1));
            assert(self.has_path(z, y));
            self.lemma_has_path_i_ensures(x, y, i)
        }
    }
}


// lemmas for descendants
impl<T> AbsTree<T>{
    pub proof fn lemma_descendants(self, id:usize)
        requires self.wf()
        ensures self.descendants(id).subset_of(self.dom())
    {
        assert forall |x:usize| #[trigger]self.has_path(id, x) implies self.contains(x) by{
            self.has_path_ensures(id, x)
        }
    }

    pub proof fn lemma_descendants_0(self, id:usize)
        requires !self.contains(id)
        ensures self.descendants(id).is_empty()
    {
        if !self.descendants(id).is_empty() {
            let k = self.descendants(id).choose();
            assert(self.has_path(id, k));
            self.lemma_has_path_ensures(id, k);
        }
    }

    pub proof fn lemma_des_childs_empty(self, id:usize)
        requires
            self.wf(),
            self.childs_seq(id).len() == 0,
        ensures
            self.descendants(id).is_empty(),
    {
        assert forall |y:usize| #[trigger]self.has_path(id, y) implies false by
        {
            self.lemma_has_path_ensures(id, y);
            if self.is_parent_of(id, y){
                assert(self.childs_seq(id).contains(y));
                assert(false)
            }
            else {
                let  z = choose |z:usize| self.is_parent_of(id, z) && self.has_path(z, y);
                assert(self.is_parent_of(id, z));
                assert(self.childs_seq(id).contains(z));
                assert(false)
            }
        }
    }
}


// lemmas about path and tree operation
impl<T> AbsTree<T>{

    // for remove_node
    pub proof fn lemma_remove_node_path0(self, id:usize)
        requires
            self.wf(),
        ensures
            forall |x:usize, y:usize|
                x != id && y != id &&
                self.is_parent_of(x, y) ==>
                #[trigger]self.remove_node(id).is_parent_of(x, y),

            forall |x:usize, y:usize|
                #[trigger]self.remove_node(id).is_parent_of(x, y)
                ==> self.is_parent_of(x, y),

            //structure specific
            forall |x:usize|
                self.contains(x) &&
                x != id && !self.is_parent_of(x, id) ==>
                #[trigger]self.remove_node(id).nodes[x] =~= self.nodes[x]
                && #[trigger] self.remove_node(id).contains(x),
    {
        self.lemma_remove_node_ensures(id);

        assert forall |x:usize, y:usize|
                x != id && y != id &&
                self.is_parent_of(x, y) implies
                #[trigger]self.remove_node(id).is_parent_of(x, y) by
        {
            if self.contains(id){
                let post = self.remove_node(id);
                assert(post.contains(x));
                assert(post.contains(y));
                assert(post.nodes[x] =~= self.nodes[x].remove_child(id));
                assert(self.nodes[x].child.contains(y));
                let j = choose |j:int| 0<=j<self.nodes[x].child.len() && self.nodes[x].child[j] == y;
                self.nodes[x].child.index_of_first_ensures(id);
                let index = self.nodes[x].child.index_of_first(id);
                match index {
                    None => {
                        assert(post.nodes[x].child.contains(y));
                    },
                    Some(index) => {
                        assert(post.nodes[x].child =~= self.nodes[x].child.remove(index));
                        assert(self.nodes[x].child[index] == id);
                        assert(self.nodes[x].child[index] != y);
                        if index > j {
                            assert(post.nodes[x].child[j] == y);
                        }
                        else {
                            assert(index != j);
                            assert(post.nodes[x].child[j - 1] == y);
                        }
                    }
                }
            }
        }

        assert forall |x:usize, y:usize|
                #[trigger]self.remove_node(id).is_parent_of(x, y)
                implies self.is_parent_of(x, y) by
        {
            if self.contains(id){

                let post = self.remove_node(id);
                if x == id {   }
                else if y == id {}
                else {
                    assert(x != id && y != id);
                    assert(post.contains(x));
                    assert(post.contains(y));
                    assert(self.contains(x));
                    assert(self.contains(y));
                    assert(post.nodes[x] =~= self.nodes[x].remove_child(id));
                    assert(post.nodes[x].child.contains(y));
                    let j = choose |j:int| 0<=j<post.nodes[x].child.len() && post.nodes[x].child[j] == y;
                    self.nodes[x].child.index_of_first_ensures(id);
                    let index = self.nodes[x].child.index_of_first(id);
                    match index {
                        None => {},
                        Some(index) => {
                            if index > j {
                                assert(self.nodes[x].child[j] == y);
                            }
                            else {
                                assert(self.nodes[x].child[j + 1] == y);
                            }
                        }
                    }
                }
            }
        }

        assert forall |x:usize|
                self.contains(x) &&
                x != id && !self.is_parent_of(x, id) 
                implies
                #[trigger]self.remove_node(id).nodes[x] =~= self.nodes[x] by
        {
            if self.contains(id){
                let post = self.remove_node(id);
                assert(post.contains(x));
                assert(post.nodes[x] =~= self.nodes[x].remove_child(id));

                assert(!self.nodes[x].child.contains(id));
                self.nodes[x].child.index_of_first_ensures(id);
                assert(post.nodes[x] =~= self.nodes[x]);
            }    
        }
    }

    pub proof fn lemma_remove_node_path(self, id:usize)
        requires
            self.wf()
        ensures
            forall |x:usize, y:usize|
                x != id && y != id &&
                !self.has_path(id, y) &&
                self.has_path(x, y) ==>
                #[trigger]self.remove_node(id).has_path(x, y),    
            
            forall |x:usize, y:usize|
                #[trigger]self.remove_node(id).has_path(x, y)
                ==> self.has_path(x, y)    
    {
        assert forall |x:usize, y:usize|
            x != id && y != id &&
            !self.has_path(id, y) &&
            self.has_path(x, y) implies 
            #[trigger]self.remove_node(id).has_path(x, y) by
        {
            let i = choose |i:int| self.has_path_i(x, y, i);
            self.lemma_remove_node_path_i_1(id, x, y, i);
        }

        assert forall |x:usize, y:usize|
            #[trigger]self.remove_node(id).has_path(x, y)
            implies self.has_path(x, y) by
        {
            let i = choose |i:int| self.remove_node(id).has_path_i(x, y, i);
            self.lemma_remove_node_path_i_2(id, x, y, i);
        }
    }

    proof fn lemma_remove_node_path_i_1(self, id:usize, x:usize, y:usize, i:int)
        requires
            self.wf(),
            x != id,
            y != id,
            !self.has_path(id, y),
            self.has_path_i(x, y, i)
        ensures
            self.remove_node(id).has_path(x, y),
        decreases i
    {
        let post = self.remove_node(id);
        if i == 1 {
            assert(post.is_parent_of(x, y)) by {
                self.lemma_remove_node_path0(id);
            }
            assert(post.has_path_i(x, y, 1))
        }
        else {
            let z = choose |z:usize| self.is_parent_of(x, z) && self.has_path_i(z, y, i-1);
            assert(self.has_path_i(z, y, i-1));
            assert(z != id);
            assert(post.is_parent_of(x, z)) by {
                self.lemma_remove_node_path0(id);
            }
            assert(post.has_path(z, y)) by {
                self.lemma_remove_node_path_i_1(id, z, y, i-1)
            }
            assert(post.has_path(x, z)) by {
                post.lemma_parent_to_path(x, z)
            }
            post.lemma_path_trans(x, z, y)
        }
    }

    proof fn lemma_remove_node_path_i_2(self, id:usize, x:usize, y:usize, i:int)
        requires
            self.wf(),
            self.remove_node(id).has_path_i(x, y, i),
        ensures
            self.has_path(x, y)
        decreases i
    {
        if i == 1 {
            assert(self.is_parent_of(x, y)) by {
                self.lemma_remove_node_path0(id)
            }
            self.lemma_parent_to_path(x, y)
        }
        else{
            let post = self.remove_node(id);
            let z = choose|z:usize| post.is_parent_of(x, z) && post.has_path_i(z, y, i-1);
            assert(self.is_parent_of(x, z)) by{
                self.lemma_remove_node_path0(id)
            } 
            self.lemma_parent_to_path(x, z);
            assert(self.has_path(z, y)) by{
                self.lemma_remove_node_path_i_2(id, z, y, i-1);
            }
            self.lemma_path_trans(x, z, y)
        }
    }


    // for revoke
    pub proof fn lemma_revoke_path0(self, id:usize)
        requires self.wf(),
        ensures
            forall |x:usize, y:usize| #[trigger]self.revoke(id).has_path(x, y) ==> self.has_path(x, y),
            forall |x:usize, y:usize| #[trigger]self.revoke(id).is_parent_of(x, y) ==> self.is_parent_of(x, y),
    {
        assert forall |x:usize, y:usize| #[trigger]self.revoke(id).has_path(x, y)
            implies self.has_path(x, y) by
        {
            self.lemma_descendants(id);
            self.lemma_revoke_path0_aux_2(x, y, self.descendants(id).to_seq());
        }

        assert forall |x:usize, y:usize| #[trigger]self.revoke(id).is_parent_of(x, y)
            implies self.is_parent_of(x, y) by
        {
            self.lemma_descendants(id);
            self.lemma_revoke_path0_aux_1(x, y, self.descendants(id).to_seq());
        }
    }

    proof fn lemma_revoke_path0_aux_1(self, x:usize, y:usize, seq:Seq<usize>)
        requires
            self.wf(),
            seq.fold_left(self, |b:Self, a:usize| b.remove_node(a)).is_parent_of(x, y),
        ensures
            self.is_parent_of(x, y),
        decreases seq.len()
    {
        if seq.len() > 0 {
            let seq1 = seq.drop_last();
            let last = seq.last();
            let res = seq.fold_left(self, |b:Self, a:usize| b.remove_node(a));
            let res1 = seq1.fold_left(self, |b:Self, a:usize| b.remove_node(a));
            assert(res1.wf()) by{
                assert forall |b:Self, a:usize| b.wf() implies #[trigger]b.remove_node(a).wf() by{
                    b.lemma_remove_node_wf(a)
                }
                crate::fold::lemma_fold_left_preserves_inv(
                    seq1, |b:Self, a:usize| b.remove_node(a), self, |b:Self| b.wf()
                )
            }
            assert(res == res1.remove_node(last));
            assert(res1.is_parent_of(x, y)) by {
                res1.lemma_remove_node_path0(last)
            }
            self.lemma_revoke_path0_aux_1(x, y, seq1)
        }
    }

    proof fn lemma_revoke_path0_aux_2(self, x:usize, y:usize, seq:Seq<usize>)
        requires
            self.wf(),
            seq.fold_left(self, |b:Self, a:usize| b.remove_node(a)).has_path(x, y),
        ensures
            self.has_path(x, y),
        decreases seq.len()
    {
        if seq.len() > 0 {
            let seq1 = seq.drop_last();
            let last = seq.last();
            let res = seq.fold_left(self, |b:Self, a:usize| b.remove_node(a));
            let res1 = seq1.fold_left(self, |b:Self, a:usize| b.remove_node(a));
            assert(res1.wf()) by{
                assert forall |b:Self, a:usize| b.wf() implies #[trigger]b.remove_node(a).wf() by{
                    b.lemma_remove_node_wf(a)
                }
                crate::fold::lemma_fold_left_preserves_inv(
                    seq1, |b:Self, a:usize| b.remove_node(a), self, |b:Self| b.wf()
                )
            }
            assert(res == res1.remove_node(last));
            assert(res1.has_path(x, y)) by {
                res1.lemma_remove_node_path(last)
            }
            self.lemma_revoke_path0_aux_2(x, y, seq1)
        }
    }

    proof fn lemma_revoke_path2(self, id:usize)
        requires
            self.wf()
        ensures
            forall |x:usize, y:usize|
                x != id &&
                !self.has_path(id, y) &&
                self.is_parent_of(x, y) ==>
                #[trigger]self.revoke(id).is_parent_of(x, y),
    {
        self.lemma_descendants(id);
        let des = self.descendants(id).to_seq();
        assert(self.descendants(id).finite());
        let f = |s:Self, y:usize| s.remove_node(y);
        let post = self.revoke(id);
        assert(post == des.fold_left(self, f));
        assert forall |x:usize, y:usize|
                x != id &&
                !self.has_path(id, y) &&
                self.is_parent_of(x, y) implies
                #[trigger]self.revoke(id).is_parent_of(x, y) by
        {
            let inv = |s:Self| (!s.has_path(id, y)) && s.wf() && s.is_parent_of(x, y);

            assert forall |e:usize, acc:Self| (des.contains(e) && inv(acc)) implies #[trigger]inv(f(acc, e)) by{
                acc.lemma_remove_node_wf(e);
                acc.lemma_remove_node_path(e);
                self.descendants(id).lemma_to_seq_to_set_id();
                assert(self.descendants(id).contains(e));
                assert(self.has_path(id, e));
                assert(f(acc, e).wf());
                assert(!f(acc, e).has_path(id, y)) by {
                    if acc.remove_node(e).has_path(id, y) {
                        assert(acc.has_path(id, y));
                        assert(false);
                    }
                }
                assert(f(acc, e).is_parent_of(x, y)) by {
                    assert(self.has_path(id, e));
                    assert(x != e) by {
                        if x == e {
                            assert(self.has_path(id, x));
                            self.lemma_parent_to_path(x, y);
                            assert(self.has_path(x, y));
                            self.lemma_path_trans(id, x, y);
                            assert(false)
                        }
                    }
                    assert(acc.remove_node(e).is_parent_of(x, y)) by {
                        acc.lemma_remove_node_path0(e);
                    }
                }
            }
            crate::fold::lemma_fold_left_preserves_inv(des, f, self, inv);
        }
    }

    pub proof fn lemma_revoke_path(self, id:usize)
        requires
            self.wf()
        ensures
            forall |x:usize, y:usize|
                x != id &&
                !self.has_path(id, y) &&
                self.has_path(x, y) ==>
                #[trigger]self.revoke(id).has_path(x, y),
    {
        assert forall |x:usize, y:usize|
            x != id &&
            !self.has_path(id, y) &&
            self.has_path(x, y) implies
            #[trigger]self.revoke(id).has_path(x, y) by
        {
            let i = choose |i:int| self.has_path_i(x, y, i);
            self.lemma_revoke_path_i(id, x, y, i);
        }
    }

    proof fn lemma_revoke_path_i(self, id:usize, x:usize, y:usize, i:int)
        requires
            self.wf(),
            x != id,
            ! self.has_path(id, y),
            self.has_path_i(x, y, i),
        ensures
            self.revoke(id).has_path(x, y),
        decreases i
    {
        if i == 1 {
            assert(self.revoke(id).is_parent_of(x, y)) by {
                self.lemma_revoke_path2(id)
            }
            self.revoke(id).lemma_parent_to_path(x, y)
        }
        else {
            let z = choose |z:usize| self.is_parent_of(x, z) && self.has_path_i(z, y, i-1);
            assert(z != id);
            assert(!self.has_path(id, z)) by {
                if self.has_path(id, z) {
                    assert(self.has_path(z, y));
                    self.lemma_path_trans(id, z, y);
                }
            }
            assert(self.revoke(id).is_parent_of(x, z)) by {
                self.lemma_revoke_path2(id)
            }
            self.revoke(id).lemma_parent_to_path(x, z);
            self.lemma_revoke_path_i(id, z, y, i-1);
            self.revoke(id).lemma_path_trans(x, z, y)
        }
    }


    // for remove_one_edge
    pub proof fn lemma_remove_one_edge_path0(self, parent:usize, child:usize)
        requires
            self.wf(),
        ensures
            forall |x:usize, y:usize|
                #[trigger]self.remove_one_edge(parent, child).is_parent_of(x, y)
                ==> self.is_parent_of(x, y),
            forall |x:usize, y:usize|
                y != child &&
                self.is_parent_of(x, y) ==>
                #[trigger]self.remove_one_edge(parent, child).is_parent_of(x, y),
    {
        assert forall |x:usize, y:usize|
            #[trigger]self.remove_one_edge(parent, child).is_parent_of(x, y)
            implies self.is_parent_of(x, y) by
        {
            if !self.contains(parent){}
            else if !self.is_parent_of(parent, child){
                self.nodes[parent].child.index_of_first_ensures(child)
            }
            else {
                self.nodes[parent].child.index_of_first_ensures(child);
                self.lemma_remove_one_edge_ensures(parent, child);
            }
        }

        assert forall |x:usize, y:usize|
            y != child &&
            self.is_parent_of(x, y) implies
            #[trigger]self.remove_one_edge(parent, child).is_parent_of(x, y) by
        {
            let post = self.remove_one_edge(parent, child);

            if !self.contains(parent){}
            else if !self.is_parent_of(parent, child){
                self.nodes[parent].child.index_of_first_ensures(child)
            }
            else {
                self.nodes[parent].child.index_of_first_ensures(child);
                self.lemma_remove_one_edge_ensures(parent, child);

                if x != parent {}
                else {
                    assert(self.is_parent_of(parent, y));
                    assert(y != child);
                    let old_child = self.nodes[parent].child;
                    let new_child = post.nodes[parent].child;
                    let i = old_child.index_of_first(child);
                    assert(i is Some);
                    let i = i.unwrap();
                    assert(new_child =~= old_child.remove(i));
                    assert(old_child.contains(y));
                    assert(old_child[i] == child);
                    assert(new_child.contains(y)) by {
                        let j = choose |j:int| 0 <= j <old_child.len() && old_child[j] == y;
                        assert(old_child[j] == y);
                        if i < j {
                            assert(new_child[j-1] == old_child[j]);
                        }
                        else {
                            assert(new_child[j] == old_child[j]);
                        }
                    }                    
                    assert(post.is_parent_of(parent, y));
                }
            }
        }
    }

    proof fn lemma_remove_one_edge_path111(self, parent:usize, child:usize)
        requires
            self.wf(),
        ensures
            !self.remove_one_edge(parent, child).is_parent_of(parent, child)
    {
        if self.contains(parent){
            self.nodes[parent].child.index_of_first_ensures(child);
        }
    }

    proof fn lemma_remove_one_edge_path11(self, parent:usize, child:usize, z:usize)
        requires
            self.wf(),
            self.is_parent_of(parent, child),
            self.remove_one_edge(parent, child).is_parent_of(z, child),
        ensures
            false
    {
        assert(z != parent) by {
            self.lemma_remove_one_edge_path111(parent, child)
        }
        assert(self.is_parent_of(z, child)) by {
            self.lemma_remove_one_edge_path0(parent, child)
        }
        assert(z == parent);
    }

    pub proof fn lemma_remove_one_edge_path1(self, parent:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(parent, child),
        ensures
            forall|z:usize| !self.remove_one_edge(parent, child).has_path(z, child),
    {
        let post = self.remove_one_edge(parent, child);
        assert forall|z:usize| true implies !post.has_path(z, child)  by{
            if post.has_path(z, child){
                post.lemma_has_path_ensures(z, child);
                if post.is_parent_of(z, child){
                    self.lemma_remove_one_edge_path11(parent, child, z)
                }
                else {
                    let w = choose |w:usize| post.has_path(z, w) && post.is_parent_of(w, child);
                    assert(post.is_parent_of(w, child));
                    self.lemma_remove_one_edge_path11(parent, child, w)
                }
            }
        }
    }

    pub proof fn lemma_remove_one_edge_path(self, parent:usize, child:usize)
        requires
            self.wf(),
        ensures
            forall |x:usize, y:usize|
                #[trigger]self.remove_one_edge(parent, child).has_path(x, y)
                ==> self.has_path(x, y),

            forall |x:usize, y:usize|
                x != child && y != child &&
                !self.has_path(child, y) &&
                self.has_path(x, y) ==>
                #[trigger]self.remove_one_edge(parent, child).has_path(x, y),
    {
        assert forall |x:usize, y:usize|
            #[trigger]self.remove_one_edge(parent, child).has_path(x, y)
            implies self.has_path(x, y) by
        {
            let i = choose |i:int| self.remove_one_edge(parent, child).has_path_i(x, y, i);
            self.lemma_remove_one_edge_path_aux_1(parent, child, x, y, i)
        }

        assert forall |x:usize, y:usize|
            x != child && y != child &&
            !self.has_path(child, y) &&
            self.has_path(x, y) implies 
            #[trigger]self.remove_one_edge(parent, child).has_path(x, y) by
        {
            let i = choose |i:int| self.has_path_i(x, y, i);
            self.lemma_remove_one_edge_path_aux_2(parent, child, x, y, i)
        }
    }

    proof fn lemma_remove_one_edge_path_aux_1(self, parent:usize, child:usize, x:usize, y:usize, i:int)
        requires
            self.wf(),
            self.remove_one_edge(parent, child).has_path_i(x, y, i)
        ensures
            self.has_path(x, y),
        decreases i
    {
        let post = self.remove_one_edge(parent, child);
        if i == 1 {
            assert(self.is_parent_of(x, y)) by {
               self.lemma_remove_one_edge_path0(parent, child)
            }
            self.lemma_parent_to_path(x, y)
        }
        else {
            let z = choose |z:usize| post.is_parent_of(x, z) && post.has_path_i(z, y, i-1);
            assert(self.is_parent_of(x, z)) by {
               self.lemma_remove_one_edge_path0(parent, child)
            }
            self.lemma_parent_to_path(x, z);
            self.lemma_remove_one_edge_path_aux_1(parent, child, z, y, i-1);
            self.lemma_path_trans(x, z, y);
        }
    }

    proof fn lemma_remove_one_edge_path_aux_2(self, parent:usize, child:usize, x:usize, y:usize, i:int)
        requires
            self.wf(),
            x != child,
            y != child,
            !self.has_path(child, y),
            self.has_path_i(x, y, i),
        ensures
            self.remove_one_edge(parent, child).has_path(x, y),
        decreases i
    {
        let post = self.remove_one_edge(parent, child);
        if i == 1 {
            assert(post.is_parent_of(x, y)) by {
               self.lemma_remove_one_edge_path0(parent, child)
            }
            post.lemma_parent_to_path(x, y)
        }
        else {
            let z = choose |z:usize| self.is_parent_of(x, z) && self.has_path_i(z, y, i-1);
            assert(post.is_parent_of(x, z)) by {
               self.lemma_remove_one_edge_path0(parent, child)
            }
            post.lemma_parent_to_path(x, z);
            self.lemma_remove_one_edge_path_aux_2(parent, child, z, y, i-1);
            post.lemma_path_trans(x, z, y);
        }
    }
}   


// prove that tree operations preserve wf predicates
impl<T> AbsTree<T>{
    pub proof fn lemma_remove_node_wf(self, id:usize)
        requires self.wf(),
        ensures
            self.remove_node(id).wf(),
            self.remove_node(id).dom() =~= self.dom().remove(id),
    {
        let post = self.remove_node(id);
        self.lemma_remove_node_ensures(id);
        assert(self.remove_node(id).dom() =~= self.dom().remove(id));
        self.lemma_remove_node_path(id);
        self.lemma_remove_node_path0(id);
        assert forall |i:usize| #[trigger] post.contains(i) implies 
                post.nodes[i].child.to_set().subset_of(post.dom())
                && post.nodes[i].child.no_duplicates() by
        {
            assert(i != id);
            if self.contains(id){
                assert(post.nodes[i] =~= self.nodes[i].remove_child(id));
                assert(post.nodes[i].child =~= self.nodes[i].child.remove_value(id));
                self.nodes[i].child.index_of_first_ensures(id);
            }
        }
        assert(post.wf_0());
        assert(post.finite());
        assert(post.no_common_child()) by {
            assert forall |i:usize, j:usize, k:usize|
                post.is_parent_of(i, k) && post.is_parent_of(j, k)
                implies i == j by
            {
                assert(self.is_parent_of(i, k));
                assert(self.is_parent_of(j, k));
                assert(i == j)
            }
        }
        assert(post.acyclic()) by {
            if !post.acyclic(){
                let p = choose |p:usize| post.has_path(p, p);
                assert(self.has_path(p, p));
            }
        }
    }

    pub proof fn lemma_revoke_wf(self, id:usize)
        requires self.wf(),
        ensures
            self.revoke(id).wf(),
            self.contains(id) ==> self.revoke(id).contains(id),
            self.contains(id) ==> self.revoke(id).childs(id).is_empty(),
            self.contains(id) ==> self.revoke(id).descendants(id).is_empty(),
            self.revoke(id).dom() =~= self.dom() - self.descendants(id),
    {
        self.lemma_revoke_ensures(id);

        assert forall |acc:Self, x:usize| acc.wf() implies #[trigger]acc.remove_node(x).wf() by
        {
            acc.lemma_remove_node_wf(x)
        }
        self.lemma_descendants(id);
        let f = |acc:Self, x:usize| acc.remove_node(x);
        let inv = |acc:Self| acc.wf();
        crate::fold::lemma_fold_left_preserves_inv(
            self.descendants(id).to_seq(), f, self, inv
        );
        assert(self.revoke(id) == self.descendants(id).to_seq().fold_left(self, f));
        assert(inv(self.revoke(id)));

        assert(self.contains(id) ==> self.revoke(id).childs(id).is_empty()) by {
            if self.contains(id) && !self.revoke(id).childs(id).is_empty(){
                let e = self.revoke(id).childs(id).choose();
                assert(self.revoke(id).is_parent_of(id, e));
                assert(self.has_path(id, e)) by {
                    assert(self.revoke(id).has_path(id, e)) by {
                        self.revoke(id).lemma_parent_to_path(id, e);
                    }
                    self.lemma_revoke_path0(id)
                }
                assert(self.revoke(id).dom() =~= self.dom() - self.descendants(id));
                assert(self.descendants(id).contains(e));
                assert(!self.revoke(id).dom().contains(e));
            }
        }

        assert(self.contains(id) ==> self.revoke(id).descendants(id).is_empty()) by {
            if self.contains(id) && !self.revoke(id).descendants(id).is_empty(){
                let e = self.revoke(id).descendants(id).choose();
                assert(self.revoke(id).has_path(id, e));
                assert(self.has_path(id, e)) by {
                    self.lemma_revoke_path0(id)
                }
                assert(self.revoke(id).contains(e)) by { self.revoke(id).has_path_ensures(id, e)}
                assert(self.revoke(id).dom() =~= self.dom() - self.descendants(id));
                assert(self.descendants(id).contains(e));
                assert(!self.revoke(id).dom().contains(e));
            }
        }
    }

    pub proof fn lemma_revoke_and_remove_self_wf(self, id:usize)
        requires self.wf(),
        ensures
            self.revoke_and_remove_self(id).wf(),
            self.contains(id) ==> !self.revoke_and_remove_self(id).contains(id),
            self.revoke_and_remove_self(id).dom() =~= self.dom() - self.descendants(id) - set![id],
    {
        self.lemma_revoke_wf(id);
        self.revoke(id).lemma_remove_node_wf(id);
    }

    pub proof fn lemma_remove_one_edge_wf(self, parent:usize, child:usize)
        requires self.wf(),
        ensures
            self.remove_one_edge(parent, child).wf(),
            self.remove_one_edge(parent, child).dom() =~= self.dom(),
    {
        if self.contains(parent){
            let post = self.remove_one_edge(parent, child);
            assert(post.finite());
            assert forall |i:usize| #[trigger] post.contains(i) implies 
                    post.nodes[i].child.to_set().subset_of(post.dom())
                    && post.nodes[i].child.no_duplicates() by
            {
                if i == parent {
                    assert(post.nodes[i].child =~= self.nodes[i].child.remove_value(child));
                    self.nodes[i].child.index_of_first_ensures(child)
                }
                else {
                    assert(self.nodes[i] =~= post.nodes[i])
                }
            }

            assert(post.wf_0());
            assert(post.no_common_child()) by {
                assert forall |i:usize, j:usize, k:usize|
                    post.is_parent_of(i, k) && post.is_parent_of(j, k)
                    implies i == j by
                {
                    self.lemma_remove_one_edge_path0(parent, child);
                    assert(self.is_parent_of(i, k));
                    assert(self.is_parent_of(j, k));
                    assert(i == j)
                }
            }

            assert(post.acyclic()) by {
                if !post.acyclic(){
                    let p = choose |p:usize| post.has_path(p, p);
                    assert(post.has_path(p, p));
                    assert(self.has_path(p, p)) by{
                        self.lemma_remove_one_edge_path(parent, child);
                    }
                    assert(!self.acyclic());
                }
            }
        }
    }

    pub proof fn lemma_remove_edges_from_wf(self, id:usize)
        requires
            self.wf(),
            self.contains(id),
        ensures
            self.remove_edges_from(id).wf(),
    {
        self.remove_edges_from_eqv_fold_remove_edge(id);
        assert forall |s:Self, x:usize| s.wf() implies #[trigger] s.remove_one_edge(id, x).wf()
        by{
            s.lemma_remove_one_edge_wf(id, x)
        }
        crate::fold::lemma_fold_left_preserves_inv(
            self.childs_seq(id),
            |s:Self, x:usize| s.remove_one_edge(id, x),
            self,
            |s:Self| s.wf()
        );
    }
}


impl<T> AbsTree<T>{
    pub proof fn lemma_remove_free_node(self, id:usize)
        requires
            self.wf(),
            self.contains(id),
            self.has_no_parent(id),
            self.childs(id).is_empty(),
        ensures
           (Self{
                nodes : self.nodes.remove(id)
            })
            =~= self.remove_node(id)
    {
        self.lemma_remove_node_ensures(id);

        let res1 = Self{ nodes : self.nodes.remove(id) };
        let res2 = self.remove_node(id);
        assert(res1.dom() =~= res2.dom());

        assert forall |i:usize| #[trigger] res1.contains(i) implies
            res1.nodes[i] =~= res2.nodes[i] by
        {
            assert(res1.nodes[i] == self.nodes[i]);
            assert(res2.nodes[i].child =~= self.nodes[i].child.remove_value(id));

            assert(!self.nodes[i].child.contains(id)) by {
                if self.nodes[i].child.contains(id){
                    assert(self.is_parent_of(i, id));
                    assert(false)
                }
            }
            self.nodes[i].child.index_of_first_ensures(id)
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_remove_one_edge_eqv_remove_edges_to(self, parent:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(parent, child),
        ensures
            self.remove_one_edge(parent, child) =~= self.remove_edges_to(child)
        decreases self.dom().len()
    {
        let nodes = self.nodes;
        let node = nodes[parent];
        let new_node = NodeAbs{
            val : node.val,
            id : node.id,
            child : node.child.remove_value(child),
        };   
        let new_nodes = nodes.insert(parent, new_node);

        let res2 = self.remove_one_edge(parent, child);
        assert(res2.nodes =~= new_nodes);

        assert(self.wf());
        assert forall |i:usize| i!=parent && #[trigger]self.nodes.contains_key(i)
            implies !self.nodes[i].child.contains(child) by
        {
            if self.nodes[i].child.contains(child){
                assert(self.is_parent_of(i, child));
                assert(self.is_parent_of(parent, child));
                assert(i == parent);
                assert(false);
            }
        }

        let seq = nodes.dom().to_seq();
        assert(seq.contains(parent)) by {
            nodes.dom().contains(parent);
            nodes.dom().lemma_to_seq_to_set_id()
        }
        // let seq0 = seq.remove_value(parent);
        let i = seq.index_of_first(parent);
        seq.index_of_first_ensures(parent);
        assert(i is Some);
        let i = i.unwrap();
        let seq0 = seq.remove(i);
        assert(seq0 =~= seq.remove_value(parent));

        let seq1 = seq0.push(parent);

        assert(seq1.to_multiset() =~= seq.to_multiset()) by {
            broadcast use vstd::seq_lib::group_to_multiset_ensures;
            assert(seq0.to_multiset() =~= seq.to_multiset().remove(parent));
            assert(seq1.to_multiset() =~= seq0.to_multiset().insert(parent));
        }

        let f =  |x:Map<usize, NodeAbs<T>>, y:usize| Self::spec_nodes_remove(child, x, y);
        let nodes2 = seq.fold_left(nodes, f);
        let res2 = self.remove_edges_to(child);
        assert(res2.nodes =~= nodes2);
        assert(crate::fold::commutative_foldl(f)) by {
            Self::spec_nodes_remove_commut(child)
        }
        assert(
            nodes2 =~= seq1.fold_left(nodes, f)
        ) by {
            crate::fold::lemma_fold_left_permutation(seq, seq1, f, nodes)
        }

        let tmp = seq0.fold_left(nodes, f);
        let nodes20 = seq1.fold_left(nodes, f);
        assert(seq0 =~= seq1.drop_last());
        assert(nodes20 =~= f(tmp, parent));

        assert(tmp =~= nodes) by {
            assert forall |j:int| #![all_triggers]0 <= j < seq0.len() implies
                nodes.contains_key(seq0[j]) &&
                !nodes[seq0[j]].child.contains(child) by
            {
                assert(seq0[j] != parent) by{
                    assert(seq0 =~= seq.remove_value(parent));
                    assert(seq.no_duplicates()) by {
                        crate::set::lemma_set_to_seq_no_duplicates(self.dom())
                    };
                }
                assert(self.nodes.contains_key(seq0[j])) by{
                    assert(seq0.to_set().subset_of(seq.to_set()));
                    assert(seq.to_set() =~= self.nodes.dom()) by {
                        assert(seq =~= self.nodes.dom().to_seq());
                        self.nodes.dom().lemma_to_seq_to_set_id();
                    }
                }
            }
            Self::lemma_remove_one_edge_eqv_remove_edges_to_aux(seq0, nodes, child)
        }
    }

    proof fn lemma_remove_one_edge_eqv_remove_edges_to_aux(
        s:Seq<usize>,
        nodes : Map<usize, NodeAbs<T>>,
        child : usize,
    )
        requires
            forall |j:int|#![all_triggers] 0 <= j < s.len() ==>
                nodes.contains_key(s[j])
                && !nodes[s[j]].child.contains(child),
        ensures
            s.fold_left(
                nodes,
                |x:Map<usize, NodeAbs<T>>, y:usize| Self::spec_nodes_remove(child, x, y)
            ) =~= nodes,
        decreases s.len()
    {
        if s.len() >= 1 {
            let f = |x:Map<usize, NodeAbs<T>>, y:usize| Self::spec_nodes_remove(child, x, y);
            let s0 = s.drop_last();
            let last = s.last();
            let r0 = s0.fold_left(nodes, f);
            assert(r0 =~= nodes) by {
                assert forall |j:int| #![all_triggers] 0 <= j < s0.len() implies
                    nodes.contains_key(s0[j])
                    && !nodes[s0[j]].child.contains(child) by 
                {
                    assert(s0[j] == s[j]);
                    assert(nodes.contains_key(s[j]));
                    assert(!nodes[s[j]].child.contains(child)) 
                }
                Self::lemma_remove_one_edge_eqv_remove_edges_to_aux(s0, nodes, child)
            };
            let r = f(nodes, last);
            assert(r =~= nodes) by {
                assert(
                    !nodes[last].child.contains(child)
                );
                assert(r =~= 
                            nodes.insert(last, 
                                NodeAbs{ id : nodes[last].id, 
                                        val : nodes[last].val, 
                                        child: nodes[last].child.remove_value(child)}));
                nodes[last].child.index_of_first_ensures(child);
                assert(nodes[last].child.remove_value(child) =~= nodes[last].child);
            }
        }
    }
}

// remove_one_edge commut
impl<T> AbsTree<T>{
    pub proof fn lemma_remove_one_edge_commut(self, p1:usize, c1:usize, p2:usize, c2:usize)
        ensures
            self.remove_one_edge(p1, c1).remove_one_edge(p2, c2)
            =~=
            self.remove_one_edge(p2, c2).remove_one_edge(p1, c1)
    {
        let res1 = self.remove_one_edge(p1, c1).remove_one_edge(p2, c2).nodes;
        let res2 = self.remove_one_edge(p2, c2).remove_one_edge(p1, c1).nodes;
        let nodes = self.nodes;

        if self.contains(p1) && self.contains(p2){
            let n1 = nodes[p1];
            // let n2 = nodes[p2];
            let new_node1 = NodeAbs{
                val : n1.val,
                id : n1.id,
                child : n1.child.remove_value(c1),
            };


            if p1 == p2 {
                // let r1 = self.remove_one_edge(p1, c1).nodes;
                // assert(r1 =~= nodes.insert(p1, new_node1));
                let new_node2 = NodeAbs{
                    val : new_node1.val,
                    id : new_node1.id,
                    child : new_node1.child.remove_value(c2),
                };
                let new_node3 = NodeAbs{
                    val : n1.val,
                    id : n1.id,
                    child : n1.child.remove_value(c2).remove_value(c1),
                };
                // assert(res1 =~= r1.insert(p2, new_node2));
                assert(res1 =~= nodes.insert(p1, new_node2));
                assert(res2 =~= nodes.insert(p1, new_node3));
                crate::fold::lemma_remove_value_commut(n1.child, c1, c2);
            }
            else {}
        }
        else if !self.contains(p1) {}
        else {}
    }
}

// remove_node commut
impl<T> AbsTree<T>{
    pub proof fn lemma_remove_node_commut()
        ensures
            forall |v:Self, x:usize, y:usize|
                v.finite() ==>
                #[trigger]v.remove_node(x).remove_node(y)
                ==
                v.remove_node(y).remove_node(x)
    {
        assert forall|v:Self, x:usize, y:usize| #[trigger] 
            v.finite() implies
            #[trigger]v.remove_node(x).remove_node(y)
            ==
            v.remove_node(y).remove_node(x) by
        {
            if !v.contains(x) && !v.contains(y) {}
            else if v.contains(x) && !v.contains(y) {
                assert(v.remove_node(y) =~= v);
                assert(v.remove_node(y).finite());
                v.remove_node(y).lemma_remove_node_ensures(x);
            }
            else if !v.contains(x) && v.contains(y) {
                assert(v.remove_node(x) =~= v);
                assert(v.remove_node(x).finite());
                v.remove_node(x).lemma_remove_node_ensures(y);
            }
            else {
                assert(v.contains(x));
                assert(v.contains(y));
                v.lemma_remove_node_commut_aux(x, y)
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_remove_node_commut_aux(self, a:usize, b:usize)
        requires self.contains(a), self.contains(b), self.finite(),
        ensures self.remove_node(a).remove_node(b) =~= self.remove_node(b).remove_node(a)
    {
        if a == b {}
        else {
            let nodes_orig = self.nodes;
            assert(self.remove_node(a).contains(b)) by {self.lemma_remove_node_ensures(a)};
            assert(self.remove_node(b).contains(a)) by {self.lemma_remove_node_ensures(b)};
            
            let f1 = |x:Map<usize, NodeAbs<T>>, y:usize| Self::spec_nodes_remove(a, x, y);
            let f2 = |x:Map<usize, NodeAbs<T>>, y:usize| Self::spec_nodes_remove(b, x, y);
            
            let res1 = self.remove_node(a).remove_node(b);
            let res2 = self.remove_node(b).remove_node(a);

            let seq0 = self.nodes.dom().to_seq();


            self.lemma_remove_node_ensures(a);
            let res12 = self.remove_node(a);
            res12.lemma_remove_node_ensures(b);
            assert(res1.dom() =~= self.dom().remove(a).remove(b));
            assert(forall |i:usize| #[trigger]res1.contains(i) ==>
                res1.nodes[i] =~=
                self.nodes[i].remove_child(a).remove_child(b)
            );


            let res22 = self.remove_node(b);
            self.lemma_remove_node_ensures(b);
            res22.lemma_remove_node_ensures(a);
            assert(res2.dom() =~= self.dom().remove(b).remove(a));
            assert(forall |i:usize| #[trigger]res2.contains(i) ==>
                res2.nodes[i] =~=
                self.nodes[i].remove_child(b).remove_child(a)
            );

            assert(res1.dom() =~= res2.dom());

            assert forall |i:usize| #[trigger]res2.contains(i) implies
                self.nodes[i].remove_child(a).remove_child(b) =~=
                self.nodes[i].remove_child(b).remove_child(a)
            by {
                NodeAbs::<T>::lemma_remove_child_commut();
                let g  = |x:NodeAbs<T>, y:usize| NodeAbs::remove_child(x, y);
                assert(g(g(self.nodes[i], a), b) =~= g(g(self.nodes[i], b), a));
            }
            assert(res2.nodes =~= res1.nodes);
            assert(res1 =~= res2);
        }
    }
}

// revoke commut
impl<T> AbsTree<T>{
    pub proof fn lemma_revoke_commut(self, i:usize, j:usize)
        requires
            self.wf(),
        ensures
            self.revoke(i).revoke(j) =~= self.revoke(j).revoke(i)
    {
        if !self.contains(i){
            assert(self.descendants(i).is_empty()) by {
                self.lemma_descendants_0(i)
            }
            self.lemma_revoke_ensures(i);
            self.lemma_revoke_ensures(j);
            assert(!self.revoke(j).contains(i));
            assert(self.revoke(j).descendants(i).is_empty()) by {
                self.revoke(j).lemma_descendants_0(i)
            }
        }
        else if !self.contains(j){
            assert(self.descendants(j).is_empty()) by {
                self.lemma_descendants_0(j)
            }
            self.lemma_revoke_ensures(i);
            self.lemma_revoke_ensures(j);
            assert(!self.revoke(i).contains(j));
            assert(self.revoke(i).descendants(j).is_empty()) by {
                self.revoke(i).lemma_descendants_0(j)
            }
        }
        else {
            if self.has_path(i, j){
                assert(i != j);
                self.lemma_revoke_commut_2(i, j)
            }
            else if self.has_path(j, i){
                self.lemma_revoke_commut_2(j, i)
            }
            else {
                if i == j {}
                else {
                    self.lemma_revoke_commut_1(i, j)
                }
            }
        }
    }


    pub proof fn lemma_revoke_commut_1(self, i:usize, j:usize)
        requires
            self.wf(),
            self.contains(i), self.contains(j),
            !self.has_path(i, j),
            !self.has_path(j, i),
            i != j,
        ensures
            self.revoke(i).revoke(j) =~= self.revoke(j).revoke(i)
    {
        let des1 = self.descendants(i);
        let des2 = self.revoke(i).descendants(j);

        let des10 = self.descendants(j);
        let des20 = self.revoke(j).descendants(i);

        let res1 = self.revoke(i).revoke(j);
        let res2 = self.revoke(j).revoke(i);

        let f = |s:Self, id:usize| s.remove_node(id);

        assert(res1 =~= des2.to_seq().fold_left(des1.to_seq().fold_left(self, f), f));

        assert(res1 =~= (des1.to_seq() + des2.to_seq()).fold_left(self, f)) by {
            let len1 = des1.to_seq().len();
            let len2 = des2.to_seq().len();
            assert((des1.to_seq() + des2.to_seq()).subrange(0, len1 as int) =~= des1.to_seq());
            assert((des1.to_seq() + des2.to_seq()).subrange(len1 as int, len1 as int + len2) =~= des2.to_seq());
            (des1.to_seq() + des2.to_seq()).lemma_fold_left_split(self, f, len1 as int);
        }
        
        assert(res2 =~= (des10.to_seq() + des20.to_seq()).fold_left(self, f)) by {
            let len1 = des10.to_seq().len();
            let len2 = des20.to_seq().len();
            assert((des10.to_seq() + des20.to_seq()).subrange(0, len1 as int) =~= des10.to_seq());
            assert((des10.to_seq() + des20.to_seq()).subrange(len1 as int, len1 as int + len2) =~= des20.to_seq());
            (des10.to_seq() + des20.to_seq()).lemma_fold_left_split(self, f, len1 as int);
        }


        assert(des2 =~= des10) by {self.lemma_descendants_revoke_1(i, j)}
        assert(des1 =~= des20) by {self.lemma_descendants_revoke_1(j, i)}

        assert(des10.to_seq() + des20.to_seq() =~= des2.to_seq() + des1.to_seq());

        let s1 = des1.to_seq() + des2.to_seq();
        let s2 = des2.to_seq() + des1.to_seq();

        assert(des1.finite() && des2.finite()) by {
            self.lemma_descendants(i);
            self.lemma_descendants(j);
        }

        assert(s1.to_multiset() =~= s2.to_multiset()) by {
            vstd::seq_lib::lemma_seq_union_to_multiset_commutative(des1.to_seq(), des2.to_seq())
        }

        let inv = |s:Self| s.finite();
        Self::lemma_remove_node_commut();
        assert forall |s:Self, x:usize| inv(s) implies #[trigger]inv(f(s, x)) by {
            s.lemma_remove_node_ensures(x);
        }
        crate::fold::lemma_fold_left_permutation_with_inv(
            s1, s2, f, self, inv
        );

        assert(res1 =~= res2);
    }

    pub proof fn lemma_revoke_commut_2(self, i:usize, j:usize)
        requires
            self.wf(),
            self.contains(i), self.contains(j),
            self.has_path(i, j),
            i != j,
        ensures
            self.revoke(i).revoke(j) =~= self.revoke(j).revoke(i),
            self.revoke(j).revoke(i) =~= self.revoke(i),
    {
        let des1 = self.descendants(i);
        let des2 = self.revoke(i).descendants(j);

        let des10 = self.descendants(j);
        let des20 = self.revoke(j).descendants(i);


        assert(des20 + des10 =~= des1) by {
            self.lemma_descendants_revoke_2(i, j);
        }

        assert(des2.is_empty()) by {
            assert(!self.revoke(i).contains(j)) by {
                self.lemma_revoke_ensures(i);
            }
            self.revoke(i).lemma_descendants_0(j)
        }

        let res1 = self.revoke(i).revoke(j);
        let res2 = self.revoke(j).revoke(i);
        let f = |s:Self, id:usize| s.remove_node(id);
        assert(res1 =~= des1.to_seq().fold_left(self, f));
        assert(res2 =~= (des10.to_seq() + des20.to_seq()).fold_left(self, f)) by {
            let len1 = des10.to_seq().len();
            let len2 = des20.to_seq().len();
            assert((des10.to_seq() + des20.to_seq()).subrange(0, len1 as int) =~= des10.to_seq());
            assert((des10.to_seq() + des20.to_seq()).subrange(len1 as int, len1 as int + len2) =~= des20.to_seq());
            (des10.to_seq() + des20.to_seq()).lemma_fold_left_split(self, f, len1 as int);
        }

        assert(des1.finite()) by {
            self.lemma_descendants(i);
        }
        assert(des10.finite()) by {
            self.lemma_descendants(j);
        }
        assert(self.revoke(j).wf()) by{
            self.lemma_revoke_wf(j)
        }
        assert(des20.finite()) by {
            self.revoke(j).lemma_descendants(i);
        }
        des1.lemma_to_seq_to_set_id();
        des10.lemma_to_seq_to_set_id();
        des20.lemma_to_seq_to_set_id();

        assert(des1.to_seq().to_multiset() =~= (des10.to_seq() + des20.to_seq()).to_multiset()) by {

            assert(des1 =~= des10 + des20);
            
            assert(des1.to_seq().no_duplicates()) by{
                crate::set::lemma_set_to_seq_no_duplicates(des1);
            }
            assert(des10.to_seq().no_duplicates()) by{
                crate::set::lemma_set_to_seq_no_duplicates(des10);
            }
            assert(des20.to_seq().no_duplicates()) by{
                crate::set::lemma_set_to_seq_no_duplicates(des20);
            }

            assert((des10.to_seq() + des20.to_seq()).to_set() =~= des10.to_seq().to_set() + des20.to_seq().to_set()) by{
                vstd::seq_lib::seq_to_set_distributes_over_add(des10.to_seq(), des20.to_seq());
            }

            let s = des10.to_seq() + des20.to_seq();


            assert forall |e:usize| des10.contains(e) && des20.contains(e) implies false by
            {
                assert(self.has_path(j, e));
                assert(!self.revoke(j).contains(e)) by{
                    self.lemma_revoke_ensures(j);
                }
                assert(self.revoke(j).has_path(i, e));
                assert(self.revoke(j).contains(e)) by {
                    self.revoke(j).lemma_has_path_ensures(i, e)
                }
            }

            assert(s.no_duplicates()) by {
                assert forall|p, q| (0 <= p < s.len() && 0 <= q < s.len() && p != q) && s[p] == s[q] implies false by {
                    let l1 = des10.to_seq().len();
                    let l2 = des20.to_seq().len();

                    if p < l1 && q < l1 {
                        assert(des10.to_seq().no_duplicates());
                        assert(false)
                    }
                    else if l1 <= p && l1 <= q {
                        assert(des20.to_seq().no_duplicates());
                        assert(false)
                    }
                    else if p < l1 && l1 <= q{
                        assert(des10.contains(s[p]));
                        assert(des20.contains(s[q]));
                    }
                    else {
                        assert(des10.contains(s[q]));
                        assert(des20.contains(s[p]));
                    }
                }
            }
            
            crate::set::lemma_no_duplicates_seq_to_set_to_multiset(des1.to_seq(), s);
        }

        let inv = |s:Self| s.wf();
        assert forall |v:Self, x:usize, y:usize|
            inv(v)
            implies #[trigger]f(f(v, x), y) == f(f(v, y), x)
        by
        {
            Self::lemma_remove_node_commut()
        }

        assert forall |v:Self, x:usize| inv(v) implies #[trigger]inv(f(v, x)) by {
            v.lemma_remove_node_wf(x)
        }

        assert(res1 == res2) by {
            crate::fold::lemma_fold_left_permutation_with_inv(
                des1.to_seq(),
                des10.to_seq() + des20.to_seq(),
                f,
                self,
                inv,
            )
        }
    }


    proof fn lemma_descendants_revoke_1(self, i:usize, j:usize)
        requires
            self.wf(),
            self.contains(i), self.contains(j),
            !self.has_path(i, j),
            !self.has_path(j, i),
            i != j,
        ensures
            self.revoke(i).descendants(j) =~= self.descendants(j)
    {
        assert forall |x:usize| self.has_path(j, x) implies
            #[trigger]self.revoke(i).has_path(j, x) by
        {
            assert(!self.has_path(i, x)) by {
                if self.has_path(i, x) {
                    self.lemma_path_cross(i, j, x)
                }
            }
            self.lemma_revoke_path(i);
        }
        assert(self.descendants(j).subset_of(self.revoke(i).descendants(j)));

        assert forall |x:usize| #[trigger]self.revoke(i).has_path(j, x) implies
            self.has_path(j, x) by
        {
            self.lemma_revoke_path0(i)
        }
        assert(self.revoke(i).descendants(j).subset_of(self.descendants(j)));
    }

    proof fn lemma_descendants_revoke_2(self, i:usize, j:usize)
        requires
            self.wf(),
            self.contains(i), self.contains(j),
            self.has_path(i, j),
            i != j,
        ensures
            self.revoke(j).descendants(i) + self.descendants(j) =~=
                self.descendants(i)
    {
        assert forall |x:usize| self.has_path(j, x) implies self.has_path(i, x) by
        {
            self.lemma_path_trans(i, j, x)
        }
        assert(self.descendants(j).subset_of(self.descendants(i)));
        assert forall |x:usize| #[trigger]self.revoke(j).has_path(i, x) implies self.has_path(i, x) by
        {
            self.lemma_revoke_path0(j)
        }
        assert(self.revoke(j).descendants(i).subset_of(self.descendants(i)));
        assert((self.revoke(j).descendants(i) + self.descendants(j)).subset_of(self.descendants(i)));


        assert forall |x:usize| self.has_path(i, x) && !self.has_path(j, x) implies
            #[trigger]self.revoke(j).has_path(i, x)
        by{
            self.lemma_revoke_path(j);
        }
        assert(self.descendants(i).subset_of(self.revoke(j).descendants(i) + self.descendants(j)));
    } 

    proof fn lemma_path_cross(self, x:usize, y:usize, z:usize)
        requires
            self.wf(),
            self.has_path(x, z),
            self.has_path(y, z),
            x != y,
        ensures
            self.has_path(x, y) || self.has_path(y, x)
    {
        let i = choose |i:int| self.has_path_i(x, z, i);
        self.lemma_path_cross_i(x, y, z, i)
    }

    proof fn lemma_path_cross_i(self, x:usize, y:usize, z:usize, i:int)
        requires
            self.wf(),
            self.has_path_i(x, z, i),
            self.has_path(y, z),
            x != y,
        ensures
            self.has_path(x, y) || self.has_path(y, x)
        decreases i
    {
        if i == 1 {
            assert(self.is_parent_of(x, z));
            self.lemma_has_path_ensures(y, z);
            assert(!self.is_parent_of(y, z));
            self.lemma_has_path_ensures(y, z);
            let w = choose |w:usize| self.has_path(y, w) && self.is_parent_of(w, z);
            assert(self.is_parent_of(w, z));
            assert(w == x);
            assert(self.has_path(y, x));
        }
        else {
            let v = choose |v:usize| self.is_parent_of(x, v) && self.has_path_i(v, z, i-1);

            assert(self.is_parent_of(x, v));
            if v == y {
                self.lemma_parent_to_path(x, y)
            }
            else {
                assert(self.has_path(v, z));
                self.lemma_path_cross_i(v, y, z, i-1);
                if self.has_path(v, y) {
                    self.lemma_parent_to_path(x, v);
                    self.lemma_path_trans(x, v, y);
                }
                else {
                    assert(self.has_path(y, v));
                    self.lemma_path_cross_i(x, y, v, 1);
                }
            }

        }
    }


}

// revoke_and_remove_self commut
impl<T> AbsTree<T>{
    pub proof fn lemma_revoke_and_remove_self_commut(self, i:usize, j:usize)
        requires
            self.wf(),
        ensures
            self.revoke_and_remove_self(i).revoke_and_remove_self(j)
            =~=
            self.revoke_and_remove_self(j).revoke_and_remove_self(i),
    {
        if i != j {
            let r1 = self.revoke(i);
            let r2 = self.revoke(j);
            let res1 = self.revoke_and_remove_self(i).revoke_and_remove_self(j);
            let res2 = self.revoke_and_remove_self(j).revoke_and_remove_self(i);

            if !self.contains(i) {
                self.lemma_descendants_0(i);
                assert(res1 =~= self.revoke_and_remove_self(j));
                self.lemma_revoke_and_remove_self_wf(j);
                assert(!self.revoke_and_remove_self(j).contains(i));
                self.revoke_and_remove_self(j).lemma_descendants_0(i);
                assert(res2 =~= self.revoke_and_remove_self(j));
            }
            else if !self.contains(j) {
                self.lemma_descendants_0(j);
                assert(res2 =~= self.revoke_and_remove_self(i));
                self.lemma_revoke_and_remove_self_wf(i);
                assert(!self.revoke_and_remove_self(i).contains(j));
                self.revoke_and_remove_self(i).lemma_descendants_0(j);
                assert(res1 =~= self.revoke_and_remove_self(i));
            }
            else {
                self.lemma_revoke_wf(i);
                assert(self.revoke(i).remove_node(i).revoke(j) =~= self.revoke(i).revoke(j).remove_node(i)) by {
                    r1.lemma_revoke_and_remove_self_commut_1(i, j);
                }

                assert(res1 =~= self.revoke(i).revoke(j).remove_node(i).remove_node(j));
                self.lemma_revoke_commut(i, j);

                assert(res1 =~= self.revoke(j).revoke(i).remove_node(i).remove_node(j));
                self.lemma_revoke_wf(j);
                self.revoke(j).lemma_revoke_wf(i);
                assert(self.revoke(j).revoke(i).remove_node(i).remove_node(j) =~=  self.revoke(j).revoke(i).remove_node(j).remove_node(i)) by {
                    Self::lemma_remove_node_commut()
                }

                assert(res1 =~= self.revoke(j).revoke(i).remove_node(j).remove_node(i));

                assert(self.revoke(j).revoke(i).remove_node(j) =~= self.revoke(j).remove_node(j).revoke(i)) by {
                    r2.lemma_revoke_and_remove_self_commut_1(j, i);
                }
            }

        }
    }


    proof fn lemma_revoke_and_remove_self_commut_1(self, i:usize, j:usize)
        requires
            self.wf(),
            self.contains(i),
            self.descendants(i).is_empty(),
            i != j,
        ensures
            self.remove_node(i).revoke(j)
            =~=
            self.revoke(j).remove_node(i),
    {
        let s1 = self.remove_node(i);
        let des1 = s1.descendants(j);
        let des0 = self.descendants(j);
        assert(s1.wf()) by {
            self.lemma_remove_node_wf(i)
        }
        if self.has_path(j, i) {
            assert(self.descendants(j).contains(i));
            assert(!self.revoke(j).contains(i)) by {
                self.lemma_revoke_wf(j)
            }
            assert(self.revoke(j).remove_node(i) =~= self.revoke(j));
            s1.lemma_descendants(j);
            assert(!des1.contains(i)) by {
                self.lemma_remove_node_ensures(i);
                assert(!s1.contains(i));
                assert(des1.subset_of(s1.dom()));
            }
            assert forall |e:usize| s1.has_path(j, e) implies self.has_path(j, e) by {
                self.lemma_remove_node_path(i)
            }
            assert(des1.subset_of(des0));
            assert(des1.insert(i).subset_of(des0));

            assert forall |e:usize |self.has_path(j, e) && e != i implies #[trigger]self.remove_node(i).has_path(j, e) by{
                self.lemma_remove_node_path(i);
                assert(j != i);
                assert(e != i);
                assert(!self.has_path(i, e)) by{
                    if self.has_path(i, e) {
                        assert(self.descendants(i).contains(e))
                    }
                }
            }

            assert(des0 =~= des1.insert(i));
            let l1 = des1.insert(i).to_seq();
            let l2 = seq![i] + des1.to_seq();

            assert(l1.to_multiset() =~= l2.to_multiset()) by{
                des0.lemma_to_seq_to_set_id();
                des1.lemma_to_seq_to_set_id();
                assert(l2.to_set() =~= des1.to_seq().to_set().insert(i)) by {
                    assert(l2.to_set() =~= set![i] + des1.to_seq().to_set()) by {
                        vstd::seq_lib::seq_to_set_distributes_over_add(seq![i], des1.to_seq());
                        assert(seq![i].to_set() =~= set![i]) by {
                            let v : Seq<usize> = seq![];
                            assert(v.to_set().is_empty());
                            assert(v.push(i).to_set() =~= v.to_set().insert(i)) by {
                                v.lemma_push_to_set_commute(i)
                            }
                        }
                    }
                }
                assert(l1.to_set() =~= l2.to_set());
                assert(l1.no_duplicates()) by {
                    crate::set::lemma_set_to_seq_no_duplicates(des0)
                }
                assert(l2.no_duplicates()) by {
                    crate::set::lemma_set_to_seq_no_duplicates(des1);
                    assert(!des1.contains(i))
                }
                crate::set::lemma_no_duplicates_seq_to_set_to_multiset(l1, l2);
            }

            let res1 = self.remove_node(i).revoke(j);
            let res2 = self.revoke(j);
            let f = |s:Self, x:usize| s.remove_node(x);

            assert(res2 =~= l1.fold_left(self, f));


            assert(res1 =~= l2.fold_left(self, f)) by {
                assert(self.remove_node(i) =~= seq![i].fold_left(self, f)) by {
                    reveal_with_fuel(vstd::seq::Seq::fold_left, 2)
                }
                assert(res1 =~= des1.to_seq().fold_left(seq![i].fold_left(self, f), f));
                (seq![i] + des1.to_seq()).lemma_fold_left_split(self, f, 1);
                assert((seq![i] + des1.to_seq()).subrange(0, 1) =~= seq![i]);
                assert((seq![i] + des1.to_seq()).subrange(1, (seq![i] + des1.to_seq()).len() as int) =~= des1.to_seq());
            }

            let inv = |s:Self| s.wf();
            assert forall |v:Self, x:usize| inv(v) implies #[trigger] inv(f(v, x)) by {
                v.lemma_remove_node_wf(x)
            }
            assert forall |v:Self, x:usize, y:usize| inv(v) implies #[trigger] f(f(v, x), y) == f(f(v, y), x) by {
                Self::lemma_remove_node_commut()
            }
            crate::fold::lemma_fold_left_permutation_with_inv(
                l1,
                l2,
                f,
                self,
                inv,
            )
        }
        else if self.has_path(i, j){
            assert(self.descendants(i).contains(j));
            assert(false);
        }
        else {
            self.lemma_descendants(j);
            s1.lemma_descendants(j);
            assert(des1 =~= des0) by {
                assert forall |e:usize|#[trigger]self.remove_node(i).has_path(j, e) implies self.has_path(j, e) by {
                    self.lemma_remove_node_path(i);
                }
                assert forall |e:usize| self.has_path(j, e) implies #[trigger]self.remove_node(i).has_path(j, e) by {
                    self.lemma_remove_node_path(i);
                    assert(j != i);
                    assert(e != i);
                    assert(!self.has_path(i, e)) by {
                        if self.has_path(i, e){
                            self.lemma_path_cross(i, j, e)
                        }
                    }
                }
            }
            let res1 = self.remove_node(i).revoke(j);
            let res2 = self.revoke(j).remove_node(i);
            let f = |s:Self, x:usize| s.remove_node(x);
            assert(res1 =~= (seq![i] + des1.to_seq()).fold_left(self, f)) by {
                assert(self.remove_node(i) =~= seq![i].fold_left(self, f)) by {
                    reveal_with_fuel(vstd::seq::Seq::fold_left, 2)
                }
                assert(res1 =~= des1.to_seq().fold_left(seq![i].fold_left(self, f), f));
                (seq![i] + des1.to_seq()).lemma_fold_left_split(self, f, 1);
                assert((seq![i] + des1.to_seq()).subrange(0, 1) =~= seq![i]);
                assert((seq![i] + des1.to_seq()).subrange(1, (seq![i] + des1.to_seq()).len() as int) =~= des1.to_seq());
            }

            assert(res2 =~= (des0.to_seq() + seq![i]).fold_left(self, f)) by {
                assert((des0.to_seq() + seq![i]).drop_last() =~= des0.to_seq());
            }

            assert(des0 =~= des1);
            assert(des0.to_seq().no_duplicates()) by {
                crate::set::lemma_set_to_seq_no_duplicates(des0);
            }
            assert(des1.to_seq().no_duplicates()) by {
                crate::set::lemma_set_to_seq_no_duplicates(des1);
            }
            assert(des0.to_seq().to_multiset() =~= des1.to_seq().to_multiset()) by{
                crate::set::lemma_no_duplicates_seq_to_set_to_multiset(des0.to_seq(), des1.to_seq())
            }
            assert((des0.to_seq() + seq![i]).to_multiset() =~= 
                des0.to_seq().to_multiset().insert(i)
            ) by {
                assert(des0.to_seq() + seq![i] =~= des0.to_seq().push(i));
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
            }

            assert((seq![i] + des1.to_seq()).to_multiset() =~= 
                des1.to_seq().to_multiset().insert(i)
            ) by {
                assert(seq![i] + des1.to_seq() =~= des1.to_seq().insert(0, i));
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
            }

            assert((des0.to_seq() + seq![i]).to_multiset() =~= (seq![i] + des1.to_seq()).to_multiset());

            assert(res1 =~= res2) by {
                let inv = |s:Self| s.wf();
                assert forall |v:Self, x:usize| inv(v) implies #[trigger] inv(f(v, x)) by {
                    v.lemma_remove_node_wf(x)
                }
                assert forall |v:Self, x:usize, y:usize| inv(v) implies #[trigger] f(f(v, x), y) == f(f(v, y), x) by {
                    Self::lemma_remove_node_commut()
                }
                crate::fold::lemma_fold_left_permutation_with_inv(
                    des0.to_seq() + seq![i],
                    seq![i] + des0.to_seq(),
                    f,
                    self,
                    inv,
                )
            }
        }
    }
}



impl<T> AbsTree<T>{

    pub proof fn lemma_remove_one_edge_ensures(self, parent:usize, child:usize)
        requires
            self.is_parent_of(parent, child)
        ensures
            ({
                let post = self.remove_one_edge(parent, child);
                &&& post.dom() =~= self.dom()
                &&& forall |i:usize| #[trigger] self.contains(i) && i != parent
                        ==> post.nodes[i] =~= self.nodes[i]
                &&& post.nodes[parent].id == self.nodes[parent].id
                &&& post.nodes[parent].val == self.nodes[parent].val
                &&& post.nodes[parent].child == self.nodes[parent].child.remove_value(child)
            })
    {}

    proof fn lemma_remove_first_edge(self, parent:usize, child:usize)
        requires
            self.is_parent_of(parent, child),
            self.childs_seq(parent).first() == child,
        ensures
            self.remove_one_edge(parent, child).childs_seq(parent)
            =~= self.childs_seq(parent).drop_first(),
    {
        let childs_seq = self.childs_seq(parent);
        childs_seq.index_of_first_ensures(child);
    }

    proof fn remove_edges_from_eqv_fold_remove_edge(self, parent:usize)
        requires
            self.nodes.contains_key(parent),
            self.wf(),
        ensures
            self.childs_seq(parent).fold_left(
                self,
                |b:Self, a:usize| b.remove_one_edge(parent, a)
            )        
            =~= self.remove_edges_from(parent)
    {
        let f = |b:Self, a:usize| b.remove_one_edge(parent, a);
        let childs_seq = self.childs_seq(parent);
        let res = childs_seq.fold_left(self, f);

        let inv_2 = |s:Self, l:Seq<usize>|
            s.nodes.contains_key(parent)
            && s.nodes.dom() =~= self.nodes.dom()
            && (forall |i:usize| i!=parent && #[trigger]s.nodes.contains_key(i) ==> s.nodes[i] == self.nodes[i])
            && s.nodes[parent].id == self.nodes[parent].id
            && s.nodes[parent].val == self.nodes[parent].val
            && s.nodes[parent].child =~= 
                l.fold_left(
                    self.nodes[parent].child,
                    |b:Seq<usize>, a:usize| b.remove_value(a)
                );
        
        assert forall |i:int| 0 <= i < childs_seq.len() &&
            #[trigger]inv_2(childs_seq.take(i).fold_left(self, f), childs_seq.take(i)) implies
            inv_2(childs_seq.take(i+1).fold_left(self, f), childs_seq.take(i+1))
        by {
            assert(childs_seq.take(i) =~= childs_seq.take(i+1).drop_last());
        };

        assert(inv_2(res, childs_seq)) by {
            crate::fold::lemma_fold_left_preserves_inv_3(childs_seq, f, self, inv_2)
        }
        // assert(
        //     res.nodes[parent].child =~=
        //     childs_seq.fold_left(
        //         childs_seq,
        //         |b:Seq<usize>, a:usize| b.remove_value(a)
        //     )
        // );
        assert(res.nodes[parent].child =~= seq![]) by {
            Self::lemma_fold_remove_value(childs_seq);
        }
        // Self::lemma_remove_edges_from_ensures(self, parent, res)
    }

    proof fn lemma_fold_remove_value<A>(s:Seq<A>)
        ensures
            s.fold_left(
                s,
                |b:Seq<A>, a:A| b.remove_value(a)
            )
            =~= seq![]
        decreases s.len()
    {
        Self::lemma_fold_remove_value_2(s, s.len() as int)
    }

    proof fn lemma_fold_remove_value_2<A>(s:Seq<A>, i:int)
        requires
            0 <= i <= s.len(),
        ensures
            s.subrange(0, i).fold_left(
                s,
                |b:Seq<A>, a:A| b.remove_value(a)
            )
            =~= s.subrange(i, s.len() as int)
        decreases i
    {
        if i == 0 {}
        else {
            let s1 = s.subrange(0, i);
            let s2 = s.subrange(0, i - 1);
            let v = s1.last();
            assert(v == s[i-1]);
            assert(s2 =~= s1.drop_last());
            let res = s1.fold_left(s, |b:Seq<A>, a:A| b.remove_value(a));
            let res1 = s2.fold_left(s, |b:Seq<A>, a:A| b.remove_value(a));
            assert(res == res1.remove_value(v));
            assert(res1 =~= s.subrange(i - 1, s.len() as int)) by {
                Self::lemma_fold_remove_value_2(s, i-1);
            }
            assert(s.subrange(i-1, s.len() as int)[0] == v);

            res1.index_of_first_ensures(v);
            assert(res =~= res1.remove(0));
            assert(s.subrange(i as int, s.len() as int) =~= s.subrange(i - 1, s.len() as int).remove(0))
        }
    }

    pub proof fn lemma_remove_edges_from_path(self, id:usize)
        requires
            self.wf(),
        ensures
            forall |x:usize, y:usize|
                #[trigger]self.remove_edges_from(id).has_path(x, y) ==> self.has_path(x, y)
    {
        assert forall |x:usize, y:usize|
            #[trigger]self.remove_edges_from(id).has_path(x, y) implies self.has_path(x, y) by
        {
            if self.contains(id){
                self.remove_edges_from_eqv_fold_remove_edge(id);
                self.lemma_remove_edges_from_path_aux(id, x, y, self.childs_seq(id));
            }
        }
    }

    proof fn lemma_remove_edges_from_path_aux(self, id:usize, x:usize, y:usize, seq:Seq<usize>)
        requires
            self.wf(),
            seq.fold_left(self, |b:Self, a:usize| b.remove_one_edge(id, a)).has_path(x, y)
        ensures
            self.has_path(x, y),
        decreases seq.len()
    {   
        if seq.len() > 0{
            let last = seq.last();
            let seq1 = seq.drop_last();
            let f = |b:Self, a:usize| b.remove_one_edge(id, a);
            let res = seq.fold_left(self, f);
            let res1 = seq1.fold_left(self, f);
            assert(res == res1.remove_one_edge(id, last));
            assert(res1.wf()) by {
                assert forall |b:Self, a:usize| b.wf() implies #[trigger] f(b, a).wf() by{
                    b.lemma_remove_one_edge_wf(id, a)
                }
                crate::fold::lemma_fold_left_preserves_inv(
                    seq1, f, self, |b:Self| b.wf()
                )
            }
            assert(res1.has_path(x, y)) by {
                res1.lemma_remove_one_edge_path(id, last)
            }
            self.lemma_remove_edges_from_path_aux(id, x, y, seq1)
        }
    }

    pub proof fn lemma_remove_edges_from_ensures(self, id:usize)
        requires
            self.contains(id),
            self.wf(),
        ensures
            forall |child:usize| self.is_parent_of(id, child)
                ==> #[trigger] self.remove_edges_from(id).has_no_parent(child),
    {
        assert forall |child:usize| self.is_parent_of(id, child)
            implies #[trigger] self.remove_edges_from(id).has_no_parent(child) by
        {
            let post = self.remove_edges_from(id);
            if !post.has_no_parent(child) {
                let parent = choose |parent:usize| post.is_parent_of(parent, child);
                assert(self.is_parent_of(parent, child));
                assert(parent != id);
            }
        }
    }

    proof fn lemma_remove_one_edge_and_remove_node(self, parent:usize, child:usize)
        requires    
            self.wf(),
            self.is_parent_of(parent, child)
        ensures
            self.remove_one_edge(parent, child).remove_node(child)
            =~= self.remove_node(child)
    {
        let r1 = self.remove_edges_to(child);
        let r2 = self.remove_one_edge(parent, child);
        assert(r1 =~= r2) by {
            self.lemma_remove_one_edge_eqv_remove_edges_to(parent, child);
        }
        let res1 = r2.remove_node(child);
        let res2 = self.remove_node(child);
        assert(res2.nodes =~= r1.nodes.remove(child));
        assert(res2.nodes =~= r2.nodes.remove(child));
        let r22 = r2.remove_edges_to(child);
        assert(r22 =~= r2) by {
            self.lemma_remove_edges_to_twice(child)
        }
    }
}


// the main lemma used in `IndexTree::<T>::revoke`
// prove that : 
//     self ---remove_edges_from(id)--->
//          ---revoke_and_remove_self(child) for each child of id in the original tree
//     <==>
//     self --- revoke(id)
impl<T> AbsTree<T>{
    pub proof fn main_lemma(self, id:usize)
        requires
            self.wf(),
            self.contains(id),
        ensures
            self.childs_seq(id).fold_left(
                self.remove_edges_from(id),
                |s:Self, x:usize| s.revoke_and_remove_self(x)
            )
            =~= self.revoke(id)
        decreases
            self.childs_seq(id),
    {
        let childs_seq = self.childs_seq(id);

        if childs_seq.len() == 0 {
            assert(self.descendants(id).is_empty()) by {
                self.lemma_des_childs_empty(id)
            }
            assert(self.remove_edges_from(id) =~= self) by {
                self.remove_edges_from_eqv_fold_remove_edge(id);
            }
        }

        else {
            let child1 = childs_seq.first();
            let s1 = self.remove_edges_from(id);
            let f = |b:Self, a:usize| b.remove_one_edge(id, a);

            assert(s1 =~= childs_seq.fold_left(self, f)) by {
                self.remove_edges_from_eqv_fold_remove_edge(id)
            }
            let childs_seq2 = childs_seq.drop_first();
            let s0 = self.remove_one_edge(id, child1);
            assert(s0.wf()) by {
                self.lemma_remove_one_edge_wf(id, child1);
            }
            assert(s1.wf()) by {
                self.lemma_remove_edges_from_wf(id);
            }

            assert(childs_seq.fold_left(self, f)
                =~=
                childs_seq2.fold_left(s0, f)) by 
            {
                childs_seq.lemma_fold_left_alt(self, f);
                childs_seq2.lemma_fold_left_alt(s0, f)
            }
            
            let g = |s:Self, x:usize| s.revoke_and_remove_self(x);
            let res = childs_seq.fold_left(self.remove_edges_from(id), g);

            assert(res =~=
                childs_seq.fold_left(childs_seq2.fold_left(s0, f), g)
            );
            assert(s1 =~= childs_seq2.fold_left(s0, f));

            let childs_perm = childs_seq2 + seq![child1];

            assert(childs_perm.to_multiset() =~= childs_seq.to_multiset()) by{
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
                assert(childs_perm =~= childs_seq2.push(child1));
                assert(childs_seq =~= childs_seq2.insert(0, child1));
            }

            let inv = |s:Self| s.wf();
            assert forall |s:Self, x:usize| inv(s) implies #[trigger] inv(g(s, x)) by {
                s.lemma_revoke_and_remove_self_wf(x)
            }
            assert forall |s:Self, x:usize, y:usize| inv(s) implies #[trigger]
                g(g(s, x), y) == g(g(s, y), x) by
            {
                s.lemma_revoke_and_remove_self_commut(x, y)
            }
            assert(
                childs_perm.fold_left(s1, g)
                ==
                childs_seq.fold_left(s1, g)
            ) by 
            {
                crate::fold::lemma_fold_left_permutation_with_inv(
                    childs_perm,
                    childs_seq,
                    g,
                    s1,
                    inv,
                )
            }

            assert(childs_perm.drop_last() =~= childs_seq2);
            assert(res =~=
                childs_seq2.
                    fold_left(
                        childs_seq2.fold_left(s0, f),
                        g
                    ).revoke_and_remove_self(child1)
            );


            assert(childs_seq2 =~= s0.childs_seq(id)) by{
                self.lemma_remove_first_edge(id, child1)
            }
            assert(childs_seq2.fold_left(s0, f) =~= s0.remove_edges_from(id)) by{
                s0.remove_edges_from_eqv_fold_remove_edge(id)
            }

            assert(res =~=
                s0.childs_seq(id).
                    fold_left(
                        s0.remove_edges_from(id),
                        g
                    ).revoke_and_remove_self(child1)
            );

            //induction
            assert(
                s0.childs_seq(id).
                    fold_left(
                        s0.remove_edges_from(id),
                        g
                    )
                =~=
                s0.revoke(id)
            ) by {
                s0.main_lemma(id)
            }

            assert(
                self.remove_one_edge(id, child1)
                    .revoke(id)
                    .revoke_and_remove_self(child1)
                =~=
                self.revoke(id)
            )
            by {
                self.lemma_remove_one_edge_and_revoke(id, child1)
            }
        }
    }

    proof fn lemma_remove_one_edge_and_revoke(self, id:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(id, child),
        ensures
            self.remove_one_edge(id, child)
                .revoke(id)
                .revoke_and_remove_self(child)
            =~=
            self.revoke(id)
    {
        self.lemma_remove_one_edge_child_des(id, child);
        self.lemma_remove_one_edge_des(id, child);

        let des1 = self.descendants(child);
        assert(des1 =~= self.remove_one_edge(id, child).descendants(child));
        let des2 = self.remove_one_edge(id, child).descendants(id);
        let des = self.descendants(id);
        assert(des =~= des1 + des2 + set![child]);
        let s0 = self.remove_one_edge(id, child);
        assert(s0.wf()) by { self.lemma_remove_one_edge_wf(id, child)}

        self.lemma_descendants(child);
        self.lemma_descendants(id);
        s0.lemma_descendants(id);
        des1.lemma_to_seq_to_set_id();
        des2.lemma_to_seq_to_set_id();
        des.lemma_to_seq_to_set_id();

        let f = |s:Self, x:usize| s.remove_node(x);
        let res = self.remove_one_edge(id, child)
                        .revoke(id)
                        .revoke_and_remove_self(child);
        assert(res =~= s0.revoke(id).revoke(child).remove_node(child));

        assert(!s0.has_path(id, child)) by {
            self.lemma_remove_one_edge_path1(id, child)
        }
        assert(!s0.has_path(child, id)) by {
            if s0.has_path(child, id){
                self.lemma_remove_one_edge_path(id, child);
                assert(self.has_path(child, id));
                assert(self.has_path(id, child)) by {
                    self.lemma_parent_to_path(id, child)
                }
                assert(self.has_path(id, id)) by {
                    self.lemma_path_trans(id, child, id)
                }
            }
        }

        assert(s0.revoke(id).descendants(child) =~= s0.descendants(child)) by{
            assert(s0.revoke(id).descendants(child).subset_of(s0.descendants(child))) by{
                s0.lemma_revoke_path0(id);
            }
            assert(s0.descendants(child).subset_of(s0.revoke(id).descendants(child))) by{
                assert forall |y:usize|
                    s0.has_path(child, y) implies #[trigger] s0.revoke(id).has_path(child, y)
                by{
                    s0.lemma_revoke_path(id);
                    assert(child != id) by {
                        if child == id {
                            assert(self.is_parent_of(id, id));
                            self.lemma_parent_to_path(id, id);
                        }
                    }
                    assert(!s0.has_path(id, y)) by {
                        if s0.has_path(id, y){
                            s0.lemma_path_cross(id, child, y)
                        }
                    }
                }
            }
        }

        assert(
            res =~=
                des1.to_seq().fold_left(
                    des2.to_seq().fold_left(
                        s0, f
                    ),
                    f
                ).remove_node(child)
        );
        // s0.lemma_descendants(child);
        // s0.lemma_descendants(id);
        let len2 = des2.to_seq().len();
        let len1 = des1.to_seq().len();
        let des00 = des2.to_seq() + des1.to_seq();
        assert(des00.subrange(0, len2 as int) =~= des2.to_seq());
        assert(des00.subrange(len2 as int, des00.len() as int) =~= des1.to_seq());
        des00.lemma_fold_left_split(s0, f, len2 as int);

        assert(res =~= des00.fold_left(s0, f).remove_node(child));
        assert((des00 + seq![child]).drop_last() =~= des00);
        assert(res =~= (des2.to_seq() + des1.to_seq() + seq![child]).fold_left(s0, f));
        assert(des =~= des1 + des2 + set![child]);

        // assert(!des1.contains(child))
        // assert(!des2.contains(child))
        // assert(des1.disjoint(des2))

        assert((des2.to_seq() + des1.to_seq() + seq![child]).to_multiset()
            =~= (seq![child] + des2.to_seq() + des1.to_seq()).to_multiset()
        ) by {
            assert(seq![child] + des2.to_seq() + des1.to_seq()
                =~= 
                seq![child] + (des2.to_seq() + des1.to_seq())
            );
            vstd::seq_lib::lemma_seq_union_to_multiset_commutative(
                 seq![child],
                 des2.to_seq() + des1.to_seq()
            );
        }
        assert((seq![child] + des2.to_seq() + des1.to_seq()).to_multiset() =~= des.to_seq().to_multiset()) by{
            assert((seq![child] + des2.to_seq() + des1.to_seq()).to_set() =~= des) by {
                assert(des =~= des1 + des2 + set![child]);
                vstd::seq_lib::seq_to_set_distributes_over_add(seq![child], des2.to_seq());
                vstd::seq_lib::seq_to_set_distributes_over_add(seq![child] + des2.to_seq(), des1.to_seq());
                assert(seq![child].to_set() =~= set![child]) by {
                    let v : Seq<usize> = seq![];
                    assert(v.to_set().is_empty());
                    assert(v.push(child).to_set() =~= v.to_set().insert(child)) by {
                        v.lemma_push_to_set_commute(child)
                    }
                }
            }

            assert(des.to_seq().no_duplicates()) by {
                crate::set::lemma_set_to_seq_no_duplicates(des)
            }

            let seq = seq![child] + des2.to_seq() + des1.to_seq();

            assert(seq.no_duplicates()) by{
                assert(!des1.contains(child)) by{
                    assert(!self.has_path(child, child))
                }
                assert(!des2.contains(child)) by {
                    if des2.contains(child){
                        assert(s0.has_path(id, child));
                        self.lemma_remove_one_edge_path1(id, child)
                    }
                }
                assert forall |e:usize| des1.contains(e) implies !#[trigger]des2.contains(e) by {
                    assert(self.has_path(child, e));
                    assert(s0.has_path(child, e));
                    if s0.has_path(id, e){
                        s0.lemma_path_cross(id, child, e);
                    }
                }
                assert(des1.to_seq().no_duplicates()) by {
                    crate::set::lemma_set_to_seq_no_duplicates(des1)
                }
                assert(des2.to_seq().no_duplicates()) by {
                    crate::set::lemma_set_to_seq_no_duplicates(des2)
                }

                assert forall |i:int, j:int| 0 <= i < j < 1 + len2 + len1 implies
                    seq[i] != seq[j] by 
                {
                    if i == 0 {
                        if j < 1 + len2 {
                            assert(des2.contains(seq[j]));
                        }
                        else {
                            assert(des1.contains(seq[j]));
                        }
                    }
                    else if j < 1 + len2 {
                        assert(des2.contains(seq[j]));
                        assert(des2.contains(seq[i]));
                    }
                    else if i < 1 + len2 {
                        assert(des1.contains(seq[j]));
                        assert(des2.contains(seq[i]));
                    }
                    else {
                        assert(des1.contains(seq[j]));
                        assert(des1.contains(seq[i]));
                    }
                }
                
            }

            crate::set::lemma_no_duplicates_seq_to_set_to_multiset(
                seq,
                des.to_seq(),
            )
        }


        assert(res =~= (seq![child] + des2.to_seq() + des1.to_seq()).fold_left(s0, f))
        by{
            assert forall |s:Self, x:usize| s.wf() implies #[trigger]f(s, x).wf() by{
                s.lemma_remove_node_wf(x)
            }
            assert forall |s:Self, x:usize, y:usize| s.wf() implies #[trigger]f(f(s, x), y) == f(f(s, y), x)  by{
                Self::lemma_remove_node_commut()
            }

            crate::fold::lemma_fold_left_permutation_with_inv(
               seq![child] + des2.to_seq() + des1.to_seq(),
               des2.to_seq() + des1.to_seq() + seq![child],
               f,
               s0,
               |s:Self| s.wf(),
            )
        }

        assert((seq![child] + des2.to_seq() + des1.to_seq()).drop_first() =~= des2.to_seq() + des1.to_seq());
        (seq![child] + des2.to_seq() + des1.to_seq()).lemma_fold_left_alt(s0, f);
        assert(res =~=
            (des2.to_seq() + des1.to_seq()).fold_left_alt(
                s0.remove_node(child), f
            )
        );
        assert(self.remove_one_edge(id, child).remove_node(child) =~= self.remove_node(child)) by{
            self.lemma_remove_one_edge_and_remove_node(id, child)
        }
        assert(res =~= 
            (des2.to_seq() + des1.to_seq()).fold_left_alt(
                self.remove_node(child), f
            )
        );
        assert(res =~= 
            (seq![child] + des2.to_seq() + des1.to_seq()).fold_left_alt(
                self, f
            )
        );
        (seq![child] + des2.to_seq() + des1.to_seq()).lemma_fold_left_alt(self, f);
        assert(res =~= 
            (seq![child] + des2.to_seq() + des1.to_seq()).fold_left(
                self, f
            )
        );


        assert(
            des.to_seq().fold_left(self, f) =~=
            (seq![child] + des2.to_seq() + des1.to_seq()).fold_left(self, f)
        )
        by
        {
            assert forall |s:Self, x:usize| s.wf() implies #[trigger]f(s, x).wf() by{
                s.lemma_remove_node_wf(x)
            }
            assert forall |s:Self, x:usize, y:usize| s.wf() implies #[trigger]f(f(s, x), y) == f(f(s, y), x)  by{
                Self::lemma_remove_node_commut()
            }
            crate::fold::lemma_fold_left_permutation_with_inv(
               seq![child] + des2.to_seq() + des1.to_seq(),
               des.to_seq(),
               f,
               self,
               |s:Self| s.wf(),
            )
        }
    }

    proof fn lemma_remove_one_edge_child_des(self, id:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(id, child),
        ensures
            self.remove_one_edge(id, child).descendants(child)
            =~= self.descendants(child)
    {
        assert(self.remove_one_edge(id, child).descendants(child).subset_of(self.descendants(child))) by{
            self.lemma_remove_one_edge_path(id, child)
        }
        assert(self.descendants(child).subset_of(self.remove_one_edge(id, child).descendants(child))) by{
            assert forall |y:usize| self.has_path(child, y) implies
                #[trigger] self.remove_one_edge(id, child).has_path(child, y) by
            {
                self.lemma_remove_one_edge_path_child(id, child, y)
            }
        }
    }

    proof fn lemma_remove_one_edge_path_child(self, id:usize, child:usize, y:usize)
        requires
            self.wf(),
            self.is_parent_of(id, child),
            self.has_path(child, y),
        ensures
            self.remove_one_edge(id, child).has_path(child, y)
    {
        let i = choose |i:int| self.has_path_i(child, y, i);
        self.lemma_remove_one_edge_path_child_aux_2(id, child, y, i);
        // prove by induction on length of path
    }

    proof fn lemma_remove_one_edge_path_child_aux_1(self, parent:usize, child:usize, x:usize, y:usize, i:int)
        requires
            self.wf(),
            self.is_parent_of(parent, child),
            self.has_path(child, x),
            self.has_path_i(x, y, i),
        ensures
            self.remove_one_edge(parent, child).has_path(x, y)
        decreases i
    {
        let post = self.remove_one_edge(parent, child);

        if i == 1 {
            assert(self.is_parent_of(x, y));
            assert(y != child) by {
                if y == child{
                    self.lemma_path_trans(child, x, child);
                }
            }
            assert(post.is_parent_of(x, y)) by{
                self.lemma_remove_one_edge_path0(parent, child)
            }
            post.lemma_parent_to_path(x, y)
        }
        else {
            let z = choose |z:usize|
                self.is_parent_of(x, z) && self.has_path_i(z, y, i-1);
            
            assert(self.has_path(x, z)) by { self.lemma_parent_to_path(x, z) }
            assert(self.has_path(child, z)) by { self.lemma_path_trans(child, x, z)}
            assert(post.has_path(z, y)) by {
                self.lemma_remove_one_edge_path_child_aux_1(parent, child, z, y, i-1)
            }
            assert(post.has_path(x, z)) by {
                self.lemma_remove_one_edge_path_child_aux_1(parent, child, x, z, 1)
            }
            post.lemma_path_trans(x, z, y)
        }
    }

    proof fn lemma_remove_one_edge_path_child_aux_2(self, id:usize, child:usize, y:usize, i:int)
        requires
            self.wf(),
            self.is_parent_of(id, child),
            self.has_path_i(child, y, i),
        ensures
            self.remove_one_edge(id, child).has_path(child, y)
        decreases i
    {
        assert(id != child) by {
            if id == child {
                self.lemma_parent_to_path(id, id)
            }
        }
        let post = self.remove_one_edge(id, child);
        if i == 1 {
            assert(self.is_parent_of(child, y));
            assert(post.nodes[child] =~= self.nodes[child]);
            assert(post.is_parent_of(child, y));
            post.lemma_parent_to_path(child, y)
        }        
        else {
            self.lemma_has_path_i_ensures(child, y, i);
            let z = choose |z:usize| self.has_path_i(child, z, i-1) && self.is_parent_of(z, y);

            assert(post.has_path(child, z)) by {
                self.lemma_remove_one_edge_path_child_aux_2(id, child, z, i-1);
            }
            assert(self.has_path(z, y)) by{
                self.lemma_parent_to_path(z, y)
            }
            assert(post.has_path(z, y)) by {
                self.lemma_remove_one_edge_path_child_aux_1(id, child, z, y, 1)
            }
            post.lemma_path_trans(child, z, y);
        }
    }

    proof fn lemma_remove_one_edge_des(self, id:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(id, child),
        ensures
            self.remove_one_edge(id, child).descendants(id)
            + self.remove_one_edge(id, child).descendants(child)
            + set![child]
            =~= self.descendants(id)
    {
        let set1 = self.remove_one_edge(id, child).descendants(id)
            + self.remove_one_edge(id, child).descendants(child)
            + set![child];
        assert(set1.subset_of(self.descendants(id))) by{
            assert(self.has_path(id, child)) by {
                self.lemma_parent_to_path(id, child)
            }

            assert forall |y:usize|
                #[trigger] self.remove_one_edge(id, child).has_path(id, y)
                implies self.has_path(id, y)
            by
            {
                self.lemma_remove_one_edge_path(id, child)
            }
            assert(self.remove_one_edge(id, child).descendants(id).subset_of(self.descendants(id)));


            assert forall |y:usize|
                #[trigger] self.has_path(child, y)
                implies self.has_path(id, y)
            by
            {
                self.lemma_path_trans(id, child, y)
            }
            self.lemma_remove_one_edge_child_des(id, child);
            assert(self.remove_one_edge(id, child).descendants(child).subset_of(self.descendants(id)));
        }

        assert(self.descendants(id).subset_of(set1)) by{
            let post = self.remove_one_edge(id, child);

            assert forall |y:usize| #[trigger]self.has_path(id, y) && y != child implies
                post.has_path(id, y) || post.has_path(child, y)
            by{

                if self.has_path(child, y) {
                    assert(post.has_path(child, y)) by {
                        self.lemma_remove_one_edge_path_child(id, child, y)
                    }
                }
                else {
                    assert(self.has_path(id, y));
                    assert(!self.has_path(child, y));
                    assert(post =~= self.remove_one_edge(id, child));
                    assert(id != child) by {
                        assert(self.has_path(id, child)) by {
                            self.lemma_parent_to_path(id, child)
                        }
                    }

                    self.lemma_remove_one_edge_path(id, child);
                }
            }
        }    
    }
}


}//verus!