use vstd::prelude::*;
use std::collections::HashMap;

verus!{

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct NodeAbs<T>{
    pub id : usize,
    pub child : Seq<usize>,
    pub val : T,
}

impl<T> Node<T>{
    pub open spec fn view(&self) -> NodeAbs<T>{
        NodeAbs{
            id : self.id,
            val : self.val,
            child : self.child@,
        }
    }
}


#[derive(Debug)]
pub struct Node<T>{
    pub id : usize,
    pub child : Vec<usize>,
    pub val : T,
}
#[derive(Debug)]
pub struct IndexTree<T>{
    pub nodes : HashMap<usize, Node<T>>,
    // pub root : usize,
}

#[verifier::ext_equal]
pub struct AbsTree<T>{
    pub nodes : Map<usize, NodeAbs<T>>,
}


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



impl<T> IndexTree<T>{
    pub open spec fn view(self) -> AbsTree<T>{
        let nodes = self.nodes;
        let nodes = nodes@.map_values(|n:Node<T>| n@);
        AbsTree{
            nodes,
        }
    }
}


impl<T> AbsTree<T>{
    pub open spec fn dom(self) -> Set<usize>{
        self.nodes.dom()
    }

    #[verifier::inline]
    pub open spec fn contains(self, id:usize) -> bool{
        self.nodes.contains_key(id)
    }

    pub open spec fn is_parent_of(self, parent:usize, child:usize) -> bool{
        &&& self.contains(parent)
        &&& self.contains(child)
        &&& self.nodes[parent].child.contains(child)
    }

    pub uninterp spec fn has_path(self, parent:usize, child:usize) -> bool;

    pub proof fn has_path_ensures(self, x:usize, y:usize)
        requires self.has_path(x, y)
        ensures self.contains(x), self.contains(y)
    {
        admit() //doable
    }

    pub open spec fn descendants(self, id:usize) -> Set<usize>{
        Set::new(|x:usize| self.has_path(id, x))
    }

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

    pub open spec fn childs(self, id:usize) -> Set<usize>{
        Set::new(|x:usize| self.is_parent_of(id, x))
    }

    pub open spec fn childs_seq(self, id:usize) -> Seq<usize>{
        self.nodes[id].child
    }

    pub proof fn lemma_childs(self, id:usize)
        requires
            self.childs_seq(id).to_set() =~= self.childs(id)
    {}

    pub open spec fn spec_nodes_remove(id:usize, x:Map<usize, NodeAbs<T>>, y:usize) -> Map<usize, NodeAbs<T>>
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

    ///
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
        // Self::lemma_remove_edges_to_0()
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
        admit()
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

    pub proof fn lemma_revoke_ensures_aux(self, seq:Seq<usize>)
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




// for path
impl<T> AbsTree<T>{
    pub proof fn lemma_path_trans(self, x:usize, y:usize, z:usize)
        requires
            self.wf(), //can be weaker ?
            self.has_path(x, y),
            self.has_path(y, z),
        ensures
            self.has_path(x, z),
    {
        admit() //doable
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
        admit() // doable
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
        admit() //doable
    }

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
        admit() // doable

        // induction on the length of path

        // !self.has_path(id, y)
        // x != id, y != id
         
        // self.has_path(x, y) ==> self.has_path(x, z) && self.is_parent_of(z, y)

        // z != id ?    if z == id then self.is_parent_of(id, y) contradictory
        // so z != id

        // self.has_path(id, z) ??
        // if self.has_path(id, z) then by transitivity, self.has_path(id, y) contradictory
        // so !self.has_path(id, z)
        
        // by induction, we get : post.has_path(x, z)

        // by the previous lemma, we get : post.is_parent_of(z, y)

        // so post.has_path(x, y)
    }

    // pub proof fn lemma_remove_node_desc(self, id:usize)
    //     requires
    //         self.wf()
    //     ensures
    //         forall |x:usize|
    //             x != id &&
    //             !self.has_path(x, id) ==>
    //             #[trigger]self.remove_node(id).descendants(x) =~= self.descendants(x)
    // {
    //     assert forall |x:usize|
    //             x != id &&
    //             !self.has_path(x, id) implies
    //             #[trigger]self.remove_node(id).descendants(x) =~= self.descendants(x) by
    //     {
    //         assert forall |y:usize|
    //             self.descendants(x).contains(y)
    //             implies #[trigger]self.remove_node(id).descendants(x).contains(y)
    //         by{
    //             assert(self.has_path(x, y));
    //             assert(y != id);
    //             self.lemma_remove_node_path(id);
    //         }

    //         assert forall |y:usize|
    //             #[trigger]self.remove_node(id).descendants(x).contains(y)
    //             implies self.descendants(x).contains(y)
    //         by{
    //             self.lemma_remove_node_path(id);
    //         }
    //     }
    // }

    pub proof fn lemma_revoke_path1(self, id:usize)
        requires self.wf(),
        ensures forall |x:usize, y:usize| #[trigger]self.revoke(id).has_path(x, y) ==> self.has_path(x, y)
    {
        admit() // easy, induction on des.len()
    }


    pub proof fn lemma_revoke_path0(self, id:usize)
        requires
            self.wf()
        ensures
            forall |x:usize, y:usize|
                x != id && y != id &&
                !self.has_path(id, x) &&
                self.is_parent_of(x, y) ==>
                #[trigger]self.revoke(id).is_parent_of(x, y),

            //structure specific
            forall |x:usize|
                self.contains(x) &&
                x != id  && !self.has_path(id, x)
                ==> #[trigger] self.revoke(id).nodes[x] =~= self.nodes[x]
                    && self.revoke(id).contains(x)
                ,
    {
        self.lemma_descendants(id);
        let des = self.descendants(id).to_seq();
        assert(self.descendants(id).finite());
        let f = |s:Self, y:usize| s.remove_node(y);
        let post = self.revoke(id);
        assert(post == des.fold_left(self, f));

        assert forall |x:usize, y:usize|
                x != id && y != id &&
                !self.has_path(id, x) &&
                self.is_parent_of(x, y) implies
                #[trigger]self.revoke(id).is_parent_of(x, y) by
        {

            let inv = |s:Self| (!s.has_path(id, x)) && s.wf() && s.is_parent_of(x, y);
            let inv_e = |e:usize| self.has_path(id, e);

            assert forall |e:usize, acc:Self| (inv_e(e) && inv(acc)) implies #[trigger]inv(f(acc, e)) by{
                acc.lemma_remove_node_wf(e);
                acc.lemma_remove_node_path(e);
                assert(f(acc, e).wf());
                assert(!f(acc, e).has_path(id, x)) by {
                    if acc.remove_node(e).has_path(id, x) {
                        assert(acc.has_path(id, x));
                        assert(false);
                    }
                }
                assert(f(acc, e).is_parent_of(x, y)) by {
                    assert(self.has_path(id, e));
                    assert(x != e) by {
                        if x == e {
                            assert(self.has_path(id, x));
                        }
                    }
                    assert(y != e) by {
                        if y == e {
                            assert(self.has_path(id, y));
                            self.lemma_has_path_ensures(id, y);
                            if self.is_parent_of(id, y){
                                assert(id == x);
                                assert(false);
                            }
                            else{
                                let z = choose |z:usize| self.has_path(id, z) && self.is_parent_of(z, y);
                                assert(self.is_parent_of(z, y));
                                assert(z == x);
                                assert(self.has_path(id, x));
                                assert(false);
                            }
                        }
                    }
                    assert(acc.remove_node(e).is_parent_of(x, y)) by {
                        acc.lemma_remove_node_path0(e);
                    }
                }
            }

            assert forall |e:usize| des.contains(e) implies inv_e(e) by {
                self.descendants(id).lemma_to_seq_to_set_id();
                assert(self.descendants(id).contains(e));
                assert(self.has_path(id, e));
            }

            crate::fold::lemma_fold_left_preserves_inv_2(des, f, self, inv, inv_e);

            assert(post.wf());
            assert(!post.has_path(id, x));

        }

        assert forall |x:usize|
            self.contains(x) &&
            x != id  && !self.has_path(id, x)
            implies 
                self.revoke(id).contains(x) &&
                #[trigger] self.revoke(id).nodes[x] =~= self.nodes[x]
            by
        {
            let inv = |s:Self| 
                (!s.has_path(id, x)) && s.wf() && s.nodes[x] =~= self.nodes[x]
                && s.contains(x) 
            ;
            let inv_e = |e:usize| self.has_path(id, e);
            assert forall |e:usize| des.contains(e) implies inv_e(e) by {
                self.descendants(id).lemma_to_seq_to_set_id();
                assert(self.descendants(id).contains(e));
                assert(self.has_path(id, e));
            }

            assert forall |e:usize, acc:Self| (inv_e(e) && inv(acc)) implies #[trigger]inv(f(acc, e)) by{
                acc.lemma_remove_node_wf(e);
                acc.lemma_remove_node_path(e);
                acc.lemma_remove_node_path0(e);
                assert(f(acc, e).wf());
                assert(!f(acc, e).has_path(id, x)) by {
                    if acc.remove_node(e).has_path(id, x) {
                        assert(acc.has_path(id, x));
                        assert(false);
                    }
                }
                assert(f(acc, e).contains(x));
                assert(f(acc, e).nodes[x] =~= self.nodes[x]) by {
                    assert(acc.nodes[x] =~= self.nodes[x]);

                    acc.lemma_remove_node_path0(e);
                    assert(acc.contains(x));
                    assert(e != id) by {
                        if e == id {
                            assert(self.has_path(id, id));
                            assert(self.contains(id));
                            assert(false);
                        }
                    }

                    assert(!acc.is_parent_of(x, e))  by {
                        assert(acc.nodes[x] =~= self.nodes[x]);
                        if acc.is_parent_of(x, e) {
                            assert(self.nodes[x].child.contains(e));
                            assert(self.is_parent_of(x, e));
                            assert(self.has_path(id, e));
                            self.lemma_has_path_ensures(id, e);
                            if self.is_parent_of(id, e){
                                assert(x == id);
                                assert(false);
                            }
                            else {
                                let z = choose |z:usize| self.has_path(id, z) && self.is_parent_of(z, e);
                                assert(self.is_parent_of(z, e));
                                assert(z == id);
                                assert(self.has_path(id, id));
                                assert(self.contains(id));
                                assert(false)
                            }
                        }
                    }
                }
            }
            crate::fold::lemma_fold_left_preserves_inv_2(des, f, self, inv, inv_e);
            assert(post.contains(x));
            assert(post.nodes[x] =~= self.nodes[x]);
        }
    }


    pub proof fn lemma_revoke_path2(self, id:usize)
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
            let inv_e = |e:usize| self.has_path(id, e);

            assert forall |e:usize, acc:Self| (inv_e(e) && inv(acc)) implies #[trigger]inv(f(acc, e)) by{
                acc.lemma_remove_node_wf(e);
                acc.lemma_remove_node_path(e);
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
            assert forall |e:usize| des.contains(e) implies inv_e(e) by {
                self.descendants(id).lemma_to_seq_to_set_id();
                assert(self.descendants(id).contains(e));
                assert(self.has_path(id, e));
            }
            crate::fold::lemma_fold_left_preserves_inv_2(des, f, self, inv, inv_e);
        }   
    }


    pub proof fn lemma_revoke_path22(self, id:usize)
        requires
            self.wf()
        ensures
            forall |x:usize, y:usize|
                x != id &&
                !self.has_path(id, y) &&
                self.has_path(x, y) ==>
                #[trigger]self.revoke(id).has_path(x, y),
    {
        admit() //doable

        // induction on path len

        // x != id, !self.has_path(id, y)
        // self.has_path(x, y)

        // ==> self.has_path(x, z) && self.is_parent_of(z, y)

        // if self.has_path(id, z) then by transitivity, ==> self.has_path(id, y) contradictory
        // so !self.has_path(id, z)

        // by induction ==> self.has_path(x, z)

        // by lemma_revoke_path2 ==> self.is_parent_of(z, y)

        // thus self.has_path(x, y)
    }


    pub proof fn lemma_childs_des(self, parent:usize, childs:Seq<usize>)
        requires
            self.wf(),
            self.contains(parent),
            self.childs_seq(parent) =~= childs,
        ensures
            forall |i:usize| #[trigger]self.descendants(parent).contains(i)
                ==>
                childs.contains(i)
                || (
                    exists |ch:usize| childs.contains(ch) && #[trigger]self.descendants(ch).contains(i)
                )
    {
        assert forall |i:usize| #[trigger]self.descendants(parent).contains(i)
            && !childs.contains(i)    
            implies
                exists |ch:usize| childs.contains(ch) && #[trigger]self.descendants(ch).contains(i)
        by{
            assert(self.has_path(parent, i));
            self.lemma_has_path_ensures(parent, i);

            assert(!self.is_parent_of(parent, i)) by{
                if self.is_parent_of(parent, i){
                    assert(childs.contains(i))
                }
            }
            let z = choose |z:usize| self.is_parent_of(parent, z) && self.has_path(z, i) ;
            assert(self.is_parent_of(parent, z));
            assert(childs.contains(z));
            assert(self.descendants(z).contains(i));
        }
    }

    pub proof fn lemma_des_subset(self, parent:usize, child:usize)
        requires
            self.wf(), //too strong
            self.has_path(parent, child),
        ensures
            self.descendants(child).subset_of(self.descendants(parent))
    {
        assert forall |j:usize| self.has_path(child, j) implies
            self.has_path(parent, j) by
        {
            self.lemma_path_trans(parent, child, j)
        }
    }

    pub proof fn lemma_revoke_parent_des(self, parent:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(parent, child),
        ensures
            self.revoke(child).descendants(parent)
            =~= self.descendants(parent) - self.descendants(child)
    {
        let post = self.revoke(child);
        self.lemma_revoke_path1(child);
        self.lemma_revoke_ensures(child);

        assert forall |e:usize|
                post.descendants(parent).contains(e)
            implies
                self.descendants(parent).contains(e)
                && ! self.descendants(child).contains(e)
        by
        {
            assert(self.descendants(parent).contains(e));
            assert(post.has_path(parent, e));
            post.has_path_ensures(parent, e);
            assert(post.contains(e));
            assert(!self.descendants(child).contains(e));            
        }

        assert forall |e:usize|
                self.descendants(parent).contains(e)
                && ! self.descendants(child).contains(e)
            implies 
                post.descendants(parent).contains(e)
        by
        {
            assert(self.has_path(parent, e));
            assert(!self.has_path(child, e));
            assert(parent != child);
            assert(post.has_path(parent, e)) by{
                self.lemma_revoke_path22(child);
            }
        }
    }



    pub proof fn lemma_remove_one_edge_path0(self, parent:usize, child:usize)
        requires
            self.wf(),
        ensures
            forall |x:usize, y:usize|
                #[trigger]self.remove_one_edge(parent, child).is_parent_of(x, y)
                ==> self.is_parent_of(x, y)
    {
        admit()
    }

    pub proof fn lemma_remove_one_edge_path(self, parent:usize, child:usize)
        requires
            self.wf(),
        ensures
            forall |x:usize, y:usize|
                #[trigger]self.remove_one_edge(parent, child).has_path(x, y)
                ==> self.has_path(x, y)
    {
        admit()
    }


}   


//api preserves wf
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
                    self.lemma_revoke_path1(id)
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
                    self.lemma_revoke_path1(id)
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
                    // assert(post.contains(p)) by {
                    //     post.has_path_ensures(p, p)
                    // }
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
    pub proof fn lemma_remove_par(self, id:usize, parent:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(parent, child),
            !self.has_path(id, child),
            id != child,
        ensures
            self.remove_node(id).is_parent_of(parent, child)
    {
        assert(parent != id) by {
            if parent == id {
                assert(!self.has_path(parent, child));
                self.lemma_parent_to_path(parent, child);
                assert(false)
            }
        }
        self.lemma_remove_node_path0(id);
    }

    pub proof fn lemma_revoke_par(self, id:usize, parent:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(parent, child),
            !self.has_path(id, child),
        ensures
            self.revoke(id).is_parent_of(parent, child)
    {
        self.lemma_revoke_path2(id);
        assert(parent != id) by {
            if parent == id {
                assert(self.is_parent_of(parent, child));
                self.lemma_parent_to_path(parent, child);
                assert(false)
            }
        }
    }

    pub proof fn lemma_revoke_and_remove_self_par(self, id:usize, parent:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(parent, child),
            id != child,
            !self.has_path(id, child),
        ensures
            self.revoke_and_remove_self(id).is_parent_of(parent, child)
    {
        let res = self.revoke_and_remove_self(id);
        let r1 = self.revoke(id);
        assert(res == r1.remove_node(id));
        assert(r1.is_parent_of(parent, child)) by{
            self.lemma_revoke_par(id, parent, child)
        }
        assert(r1.wf()) by { self.lemma_revoke_wf(id) }
        assert(!r1.has_path(id, child)) by{
            if r1.has_path(id, child) {
                assert(self.has_path(id, child)) by{
                    self.lemma_revoke_path1(id)
                }
            }
        }
        r1.lemma_remove_par(id, parent, child)
    }
                

    pub proof fn lemma_000(self, parent:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(parent, child),
            self.childs(child).is_empty(),
        ensures
           (Self{
                nodes : self.remove_one_edge(parent, child).nodes.remove(child)
            })
            =~= self.remove_node(child)
    {
        self.lemma_remove_one_edge_remove_edges_to(parent, child);
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_remove_one_edge_remove_edges_to(self, parent:usize, child:usize)
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
            Self::lemma_aux(seq0, nodes, child)
        }
    }

    proof fn lemma_aux(
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
                Self::lemma_aux(s0, nodes, child)
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




impl<T> AbsTree<T>{
    pub proof fn lemma_childs_revoke(self, parent:usize)
        requires
            self.wf(),
            self.contains(parent),
        ensures
            self.childs_seq(parent).fold_left(
                self,
                |x:Self, y:usize| x.revoke_and_remove_self(y)
            )
            =~=
            self.revoke(parent)
        decreases
            self.childs_seq(parent).len(),
    {
        let seq_child = self.childs_seq(parent);
        let f = |x:Self, y:usize| x.revoke_and_remove_self(y);
        let res = self.childs_seq(parent).fold_left(self, f);


        if seq_child.len() == 0 {
            assert(self.descendants(parent).finite()) by {
                self.lemma_descendants(parent)
            }
            assert(self.descendants(parent).len() == 0) by {
                self.lemma_childs_des(parent, seq_child);
                if self.descendants(parent).len() > 0 {
                    let e = self.descendants(parent).choose();
                    assert(self.descendants(parent).contains(e));
                    assert(!seq_child.contains(e));
                    let ch = choose |ch:usize| seq_child.contains(ch) && #[trigger]self.descendants(ch).contains(e);
                    assert(seq_child.contains(ch));
                    assert(false)
                }
            }
            assert(self.descendants(parent).to_seq().len() == 0) by {
                self.descendants(parent).lemma_to_seq_to_set_id();
                crate::set::lemma_set_to_seq_len(self.descendants(parent))
            }
        }
        else {
            assert(self.contains(parent));

            let child1 = seq_child[0];
            let s1 = seq![child1];
            let s2 = seq_child.subrange(1, seq_child.len() as int);
            let r1 = self.revoke_and_remove_self(child1);

            // assert()

            assert(s2.fold_left(r1, f) == res) by {
                seq_child.lemma_fold_left_split(self, f, 1);
                assert(r1 == s1.fold_left(self, f)) by {
                    reveal_with_fuel(vstd::seq::Seq::fold_left, 2)
                };
                assert(s1 =~= seq_child.subrange(0, 1));
            }

            assert(res =~= s2.fold_left(r1, f));

            ////proof schema

            assert(r1.wf()) by{
                assert(self.contains(child1)) by {
                    assert(self.nodes[parent].child.contains(child1));
                    assert(self.nodes.contains_key(child1))
                }
                self.lemma_revoke_and_remove_self_wf(child1);
            }
            assert(r1.contains(parent)) by {
                self.lemma_revoke_and_remove_self_wf(child1);
                assert(r1.dom() =~= self.dom() - self.descendants(child1) - set![child1]);
                assert(self.contains(parent));
                assert(self.is_parent_of(parent, child1));
                assert(self.has_path(parent, child1)) by { self.lemma_parent_to_path(parent, child1)};
                assert(parent != child1) by {
                    if parent == child1 {
                        assert(self.is_parent_of(parent, parent));
                        assert(self.has_path(parent, parent)) by {
                            self.lemma_parent_to_path(parent, parent)
                        }
                        assert(false);
                    }
                }
                assert(!self.descendants(child1).contains(parent)) by {
                    if self.has_path(child1, parent){
                        assert(self.has_path(parent, parent)) by {
                            self.lemma_path_trans(parent, child1, parent)
                        }
                    }
                }
            }

            assert(r1.childs_seq(parent).len() == s2.len()
                   && r1.childs_seq(parent) =~= s2) by
            {
                // if not
                // we can only prove that
                // r1.childs_seq(parent).to_multiset() =~= s2.to_multiset()
                self.lemma_childs_remvoke_and_remove_aux(parent, child1);
            }
            assert(
                r1.childs_seq(parent).fold_left(r1, f) =~= r1.revoke(parent)
            ) by
            {
                r1.lemma_childs_revoke(parent)
            }

            assert(
                self.revoke(child1).remove_node(child1).revoke(parent) =~= self.revoke(parent)
            ) by
            {
                self.lemma_childs_revoke_aux_2(parent, child1)
            }

        }
    }


    proof fn lemma_childs_remvoke_and_remove_aux(self, parent:usize, child1:usize)
        requires
            self.wf(),
            self.contains(parent),
            self.childs_seq(parent).len() > 0,
            self.childs_seq(parent)[0] == child1,
        ensures
            self.revoke_and_remove_self(child1).childs_seq(parent)
             =~= self.childs_seq(parent).drop_first()      
    {
        assert(self.is_parent_of(parent, child1));
        self.lemma_parent_to_path(parent, child1);
        let post = self.revoke_and_remove_self(child1);
        self.lemma_revoke_path0(child1);
        assert(self.contains(parent));
        assert(parent != child1) by{
            if parent == child1 {
                assert(self.has_path(parent, parent));
                assert(false)
            }
        }
        assert(!self.has_path(child1, parent)) by{
            if self.has_path(child1, parent){
                assert(self.has_path(parent, child1));
                self.lemma_path_trans(parent, child1, parent);
                assert(self.has_path(parent, parent));
                assert(false)
            }
        }

        assert(self.revoke(child1).nodes[parent] =~= self.nodes[parent]);
        assert(self.revoke(child1).contains(parent));

        let r1 = self.revoke(child1);
        let r2 = r1.remove_node(child1);
        assert(r1.childs_seq(parent) =~= self.childs_seq(parent));

        self.lemma_revoke_wf(child1);
        r1.lemma_remove_node_ensures(child1);

        assert(r2.contains(parent));
        assert(r2.nodes[parent] =~= r1.nodes[parent].remove_child(child1));
        assert(r2.nodes[parent].child =~= self.nodes[parent].child.remove_value(child1));

        let seq = self.nodes[parent].child;
        assert(seq[0] == child1);

        let index = seq.index_of_first(child1);
        seq.index_of_first_ensures(child1);
        // assert(index is Some);
        assert(index.unwrap() == 0);
        assert(seq.remove_value(child1) =~= seq.drop_first());
    }

    #[verifier::spinoff_prover]
    proof fn lemma_childs_revoke_aux_2(self, parent:usize, child:usize)
        requires
            self.wf(),
            self.is_parent_of(parent, child)
        ensures
            self.revoke(child).remove_node(child).revoke(parent) =~= self.revoke(parent)
    {
        assert(self.revoke(child).descendants(parent)
            =~= self.descendants(parent) - self.descendants(child)
        ) by
        {
            self.lemma_revoke_parent_des(parent, child)
        }

        assert(self.contains(parent));
        assert(self.contains(child));
        self.lemma_parent_to_path(parent, child);
        assert(parent != child);

        let r1 = self.revoke(child);
        let r2 = r1.remove_node(child);
        let res = r2.revoke(parent);
        let res0 = self.revoke(parent);
        let des1 = self.descendants(parent);
        let des2 = self.descendants(child);

        assert(r1.wf()) by { self.lemma_revoke_wf(child) }
        assert(r2.wf()) by { r1.lemma_remove_node_wf(child)}
        
        assert(r1.descendants(parent) =~= des1 - des2);
        assert(r1.remove_node(child).descendants(parent) =~= r1.descendants(parent) - set![child]) by{
            assert(r1.remove_node(child).descendants(parent).subset_of(r1.descendants(parent))) by{
                r1.lemma_remove_node_path(child)
            }
            assert(!r1.remove_node(child).descendants(parent).contains(child)) by{
                if r1.remove_node(child).has_path(parent, child){
                    r1.remove_node(child).has_path_ensures(parent, child);
                    assert(r1.remove_node(child).contains(child));
                    assert(false)
                }
            }
            assert forall |j:usize| #[trigger]r1.has_path(parent, j) && j != child implies
                r1.remove_node(child).has_path(parent, j) by
            {
                r1.lemma_remove_node_path(child);
                assert(parent != child);
                assert(j != child);
                assert(!r1.has_path(child, j)) by {
                    assert(r1.descendants(child).is_empty()) by {
                        self.lemma_revoke_wf(child)
                    }
                    if r1.has_path(child, j){
                        assert(r1.descendants(child).contains(j))
                    }
                }
            }
        }
        assert(!des2.contains(child));
        let des3 = r2.descendants(parent);
        assert(des3 =~= des1 - des2 - set![child]);
        self.lemma_descendants(parent);
        self.lemma_descendants(child);

        let f = |s:Self, y:usize| s.remove_node(y);

        assert(r1 =~= des2.to_seq().fold_left(self, f));
        assert(r2 =~= f(r1, child));
        assert(r2 =~= des2.to_seq().push(child).fold_left(self, f)) by {
            assert(des2.to_seq().push(child).drop_last() =~= des2.to_seq())
        }

        assert(res =~= des3.to_seq().fold_left(r2, f));
        
        let seq = des2.to_seq().push(child) + des3.to_seq();
        assert(res =~= seq.fold_left(self, f)) by{
            seq.lemma_fold_left_split(
                self, f, des2.to_seq().push(child).len() as int
            );
            assert(seq.subrange(0, des2.to_seq().push(child).len() as int)
                =~= des2.to_seq().push(child)
            );
            assert(seq.subrange(des2.to_seq().push(child).len() as int, seq.len() as int)
                =~= des3.to_seq()
            )
        }

        assert(res0 =~= des1.to_seq().fold_left(self, f));

        assert(des1.to_seq().to_set() =~= des1) by{
            des1.lemma_to_seq_to_set_id()
        }
        assert(des2.to_seq().to_set() =~= des2) by{
            des2.lemma_to_seq_to_set_id()
        }
        assert(des3.to_seq().to_set() =~= des3) by{
            des3.lemma_to_seq_to_set_id()
        }

        assert(seq.to_set() =~= des1) by{
            assert(seq.to_set() =~= des2.to_seq().push(child).to_set() + des3.to_seq().to_set()) by{
                vstd::seq_lib::seq_to_set_distributes_over_add(
                    des2.to_seq().push(child),
                    des3.to_seq()
                )
            }
            assert(des2.to_seq().push(child) =~= des2.to_seq() + seq![child]);
            assert((des2.to_seq() + seq![child]).to_set() =~= des2.to_seq().to_set().insert(child)) by{
                vstd::seq::Seq::lemma_to_set_insert_commutes(des2.to_seq(), child)
            }
            assert(seq.to_set() =~= des2.to_seq().to_set().insert(child) + des3.to_seq().to_set());

            assert(seq.to_set() =~= des2 + set![child] + des3);
            assert(des3 =~= des1 - des2 - set![child]);
            assert(des1 =~= des3 + des2 + set![child]) by{
                assert(des2.subset_of(des1)) by{
                    self.lemma_des_subset(parent, child);
                }
                assert(des1.contains(child)) by {
                    self.is_parent_of(parent, child);
                }
            }
        }

        assert(seq.to_set() =~= des1);

        assert(seq =~= des2.to_seq() + seq![child] + des3.to_seq());

        assert(des1.to_seq().no_duplicates()) by{
            crate::set::lemma_set_to_seq_no_duplicates(des1)
        }

        assert(seq.no_duplicates()) by{
            assert(des2.to_seq().no_duplicates()) by{
                crate::set::lemma_set_to_seq_no_duplicates(des2)
            }
            assert(!des2.contains(child));
            let s1 = des2.to_seq() + seq![child];
            let s2 = des3.to_seq();
            assert(s1.no_duplicates()) by{
                assert forall |i:int, j:int| 0 <= i < j < s1.len() implies s1[i] != s1[j] by
                {
                    if j < des2.to_seq().len() {}
                    else {
                        assert(s1[j] == child);
                        assert(des2.to_seq().contains(s1[i]));
                    }
                }
            }
            assert(des3.to_seq().no_duplicates()) by{
                crate::set::lemma_set_to_seq_no_duplicates(des3)
            }
            assert(s2.no_duplicates());

            assert( (s1 + s2).no_duplicates() ) by{
                assert forall|i: int, j: int| 0 <= i < s1.len() && 0 <= j < s2.len() implies s1[i] != s2[j] by
                {
                    assert((des2 + set![child]).contains(s1[i]));
                    assert(des3.contains(s2[j]));
                    assert(des3 =~= des1 - des2 - set![child]);
                }
                vstd::seq_lib::lemma_no_dup_in_concat(s1, s2);
            } 
        }
        assert(des1.to_seq().to_multiset() =~= seq.to_multiset()) by{
            crate::set::lemma_no_duplicates_seq_to_set_to_multiset(des1.to_seq(), seq)
        }

        assert(res == res0) by{
            let inv = |s:Self| s.wf(); // too strong ?
            assert forall |e:usize, acc:Self| inv(acc) implies #[trigger]inv(f(acc, e)) by
            {
                assert(acc.wf());
                assert(acc.remove_node(e).wf()) by{
                    acc.lemma_remove_node_wf(e)
                }
            };
            assert forall |x:usize, y:usize, acc:Self| inv(acc) implies #[trigger]f(f(acc, x), y) == f(f(acc, y), x) by
            {
                Self::lemma_remove_node_commut()
            }
            crate::fold::lemma_fold_left_permutation_with_inv(
                des1.to_seq(), seq, f, self, inv, |x:usize|true
            )
        }

    }


    proof fn lemma_revoke_non(self, i:usize)
        requires !self.contains(i), self.wf(),
        ensures self.revoke(i) =~= self
    {
        assert(self.descendants(i) =~= Set::empty()) by{
            assert forall |j:usize| !#[trigger]self.has_path(i, j) by{
                if self.has_path(i, j){
                    self.has_path_ensures(i, j)
                }
            }
        }
    }

    proof fn lemma_remove_node_non(self, i:usize)
        requires !self.contains(i), self.wf(),
        ensures self.remove_node(i) =~= self
    {}

    //main lemma 1
    proof fn lemma_remove_node_commut()
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

    // proof fn lemma_remove_edges

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























//exec fn
///////////////////////////////////////////////////////////


impl<T> IndexTree<T>{
    #[verifier::external_body]
    pub fn remove_one_edge(&mut self, parent:usize, child:usize)
        requires
            old(self)@.is_parent_of(parent, child),
            // old(self)@.nodes[parent].child[0] == child,
        ensures
            self@ =~= old(self)@.remove_one_edge(parent, child)
    {
        self.nodes.get_mut(&parent).unwrap().child.remove(0);
        // unimplemented!() //todo
    }
}




impl<T> IndexTree<T>{

    // not efficient
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::loop_isolation(false)]
    pub fn revoke(&mut self, id:usize)
        requires
            old(self).nodes@.contains_key(id),
            old(self)@.wf(),
        ensures
            self@ =~= old(self)@.revoke(id),
        // decreases
        //     old(self).to_cdt().height(id),
    {
        let children = self.nodes.get(&id).unwrap().child.clone();
        assert(children@ =~= self@.childs_seq(id));
        assert(children@.no_duplicates()) by{
            assert(self@.nodes.contains_key(id))
        }

        let ghost prev = *self;

        assert forall |j:int| 0 <= j < children@.len() implies
            #[trigger]self@.nodes.contains_key(children@[j]) by
        {
            assert(self@.contains(id));
        }

        assert forall |j:int| 0 <= j < children@.len() implies
            #[trigger]self@.is_parent_of(id, children@[j]) by
        {}

        assert forall |j:int, k:int| 0 <= j < k < children@.len() implies
            !#[trigger]self@.has_path(children@[j], children@[k]) by
        {
            broadcast use AbsTree::lemma_parent_to_path;
            self@.lemma_path_contradict(id, children@[j], children@[k])
        }

        for i in 0..children.len()
            invariant
                //I1
                self@ =~= children@.subrange(0, i as int).fold_left(
                    prev@, |x:AbsTree<T>, j:usize| x.revoke_and_remove_self(j) 
                ),
                //I2
                self@.wf(),

                //I3 // implied by I4
                // forall |j:int| i <= j < children@.len() ==>
                //    #[trigger]self@.nodes.contains_key(children@[j]),

                //I4
                forall |j:int| i <= j < children@.len() ==>
                   #[trigger]self@.is_parent_of(id, children@[j]),
 
                //I5
                forall |j:int, k:int| i <= j < k < children@.len() ==>
                   !#[trigger]self@.has_path(children@[j], children@[k]),


                //I6
                // self@.nodes[id].child =~= children@.subrange(i as int, children@.len() as int),

                // children@ =~= self.
        {
            let ghost t0 = *self;
            let child = children[i];
            assert(self.nodes@.contains_key(child)) by {
                assert(self@.is_parent_of(id, child));
                assert(self@.nodes.contains_key(child));
                assert(self@.nodes.dom() =~= self.nodes@.dom());
            }

            self.revoke(child);
            let ghost t1 = *self; ////

            proof{
                assert(self@.is_parent_of(id, child)) by {
                    assert(t0@.contains(child));
                    assert(!t0@.has_path(child, child));
                    t0@.lemma_revoke_par(child, id, child);
                };
                t0@.lemma_revoke_wf(child)
            }
            self.remove_one_edge(id, child);
            assert(self@ =~= t1@.remove_one_edge(id, child));
            assert(self@.contains(id));
            assert(self@.contains(child));

            let ghost t2 = *self;//
            self.nodes.remove(&child);

            assert(self@.nodes =~= t2@.nodes.remove(child));

            //I1
            proof{
                assert(self@ =~= t1@.remove_node(child)) by {
                    t1@.lemma_000(id, child);
                }
                assert(self@ =~= t0@.revoke_and_remove_self(child));
                assert(t0@ =~= 
                    children@.subrange(0, i as int).fold_left(
                        prev@, |x:AbsTree<T>, j:usize| x.revoke_and_remove_self(j) 
                    )
                );
                assert(
                    children@.subrange(0, i as int + 1).drop_last() =~=
                    children@.subrange(0, i as int)
                );
            }

            //I2
            proof {
                t0@.lemma_revoke_and_remove_self_wf(child);
            }

            //I3
            // proof{
            //     assert forall |j:int| i + 1 <= j < children@.len() implies 
            //        #[trigger]self@.nodes.contains_key(children@[j]) by
            //     {
            //     }
            // }

            //I4
            proof{
                assert forall |j:int| i + 1 <= j < children@.len() implies
                   #[trigger]self@.is_parent_of(id, children@[j]) by
                {
                    assert(!t0@.has_path(child, children@[j]));
                    t0@.lemma_revoke_and_remove_self_par(child, id, children@[j]);
                }
            }

            //I5
            proof{
                assert forall |j:int, k:int| i + 1 <= j < k < children@.len() implies
                   !#[trigger]self@.has_path(children@[j], children@[k]) by
                {
                    broadcast use AbsTree::lemma_parent_to_path;
                    assert(children@[j] != children@[k]) by{
                        assert(children@.no_duplicates());
                    }
                    self@.lemma_path_contradict(id, children@[j], children@[k])
                }
            }
        }


        proof{
            assert(children@.subrange(0, children@.len() as int) =~= children@);
            assert(
                self@ =~= children@.fold_left(
                    prev@, |x:AbsTree<T>, j:usize| x.revoke_and_remove_self(j) 
                )
            );
            old(self)@.lemma_childs_revoke(id);
        }

    }


}


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

    #[verifier::external_body]
    pub fn revoke_2(&mut self, id:usize)
    {
        let children = self.take_children(id);
        for i in 0..children.len()
        {
            let child = children[i];
            self.revoke(child);
            self.nodes.remove(&child);
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
        let inv_e = |e:usize| true;
        Self::lemma_remove_node_commut();
        assert forall |s:Self, x:usize| inv(s) implies #[trigger]inv(f(s, x)) by {
            s.lemma_remove_node_ensures(x);
        } 
        crate::fold::lemma_fold_left_permutation_with_inv(
            s1, s2, f, self, inv, inv_e
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
                |x:usize| true
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
            self.lemma_revoke_path22(i);
        }
        assert(self.descendants(j).subset_of(self.revoke(i).descendants(j)));

        assert forall |x:usize| #[trigger]self.revoke(i).has_path(j, x) implies
            self.has_path(j, x) by
        {
            self.lemma_revoke_path1(i)
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
            self.lemma_revoke_path1(j)
        }
        assert(self.revoke(j).descendants(i).subset_of(self.descendants(i)));
        assert((self.revoke(j).descendants(i) + self.descendants(j)).subset_of(self.descendants(i)));


        assert forall |x:usize| self.has_path(i, x) && !self.has_path(j, x) implies
            #[trigger]self.revoke(j).has_path(i, x)
        by{
            self.lemma_revoke_path22(j);
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
        admit()
        // prove by induction on the length of path
    }


}

//revoke_and_remove_self commut
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
                |x:usize| true
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
                    |x:usize| true
                )
            }
        }
    }
}



impl<T> AbsTree<T>{

    pub proof fn lemma_remove_one_edge_ensures0(self, parent:usize, child:usize)
        requires
            self.is_parent_of(parent, child)
        ensures
            self.remove_one_edge(parent, child).childs_seq(parent)
            =~= self.childs_seq(parent).remove_value(child)
    {}

    pub proof fn lemma_remove_first_edge(self, parent:usize, child:usize)
        requires
            self.is_parent_of(parent, child),
            self.childs_seq(parent).first() == child,
        ensures
            self.remove_one_edge(parent, child).childs_seq(parent)
            =~= self.childs_seq(parent).drop_first(),
    {
        self.lemma_remove_one_edge_ensures0(parent, child);
        let childs_seq = self.childs_seq(parent);
        childs_seq.index_of_first_ensures(child);
    }



    pub open spec fn remove_edges_from(self, parent:usize) -> Self{
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
        // decreases self.childs_seq(parent)
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



    proof fn lemma_remove_edges_from_ensures(self, id:usize, res:Self)
        requires
            self.nodes.contains_key(id),
            res.nodes.dom() =~= self.nodes.dom(),
            forall |i:usize| i!=id && #[trigger]res.nodes.contains_key(i) ==> res.nodes[i] == self.nodes[i],
            res.nodes[id].id == self.nodes[id].id,
            res.nodes[id].val == self.nodes[id].val,
            res.nodes[id].child =~= seq![],
        ensures
            res =~= self.remove_edges_from(id),
    {}

    // proof fn lemma_remove_one_edge_and_remove_node(self, parent:usize, child:usize)
    //     requires    
    //         self.wf(),
    //         self.is_parent_of(parent, child)
    //     ensures
    //         self.remove_one_edge(parent, child).remove_node(child)
    //         =~= self.remove_node(child)
    // {
    //     let r1 = self.remove_edges_to(child);
    //     let r2 = self.remove_one_edge(parent, child);
    //     assert(r1 =~= r2) by {
    //         self.lemma_remove_one_edge_remove_edges_to(parent, child);
    //     }
    //     let res1 = r2.remove_node(child);
    //     let res2 = self.remove_node(child);
    //     assert(res2.nodes =~= r1.nodes.remove(child));
    //     assert(res2.nodes =~= r2.nodes.remove(child));
    //     let r22 = r2.remove_edges_to(child);
    //     assert(r22 =~= r2) by {
    //         self.lemma_remove_edges_to_twice(child)
    //     }
    // }




    // proof fn lemma_remove_one_edge_commut_remove_node(self, x:usize, y:usize)
    //     requires
    //         self.wf(),
    //     ensures
    //         self.remove_node(x).remove_edges_to(y) =~= self.remove_edges_to(y).remove_node(x)
    // {

    // }
}


// main lemma !!!!!!
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
            admit()
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

            // let r1 = childs_seq2.fold_left(s0, f);
            // assert(r1.)

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
                    |x:usize| true
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
                self.lemma_aux_999(id, child1)
            }
        }
    }

    proof fn lemma_aux_999(self, id:usize, child:usize)
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
        self.lemma_aux_99(id, child);
        self.lemma_aux_9(id, child);

        let des1 = self.descendants(child);
        assert(des1 =~= self.remove_one_edge(id, child).descendants(child));
        let des2 = self.remove_one_edge(id, child).descendants(id);
        let des = self.descendants(id);
        assert(des =~= des1 + des2 + set![child]);

        let s0 = self.remove_one_edge(id, child);
        let f = |s:Self, x:usize| s.remove_node(x);
        let res = self.remove_one_edge(id, child)
                        .revoke(id)
                        .revoke_and_remove_self(child);
        assert(res =~= s0.revoke(id).revoke(child).remove_node(child));

        assert(s0.wf()) by { self.lemma_remove_one_edge_wf(id, child)}
        assert(!s0.has_path(id, child)) by {
            admit()
        }
        assert(!s0.has_path(child, id)) by {
            admit()
        }

        assert(s0.revoke(id).descendants(child) =~= s0.descendants(child)) by{
            assert(s0.revoke(id).descendants(child).subset_of(s0.descendants(child))) by{
                s0.lemma_revoke_path1(id);
            }
            assert(s0.descendants(child).subset_of(s0.revoke(id).descendants(child))) by{
                assert forall |y:usize|
                    s0.has_path(child, y) implies #[trigger] s0.revoke(id).has_path(child, y)
                by{
                    s0.lemma_revoke_path22(id);
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
        s0.lemma_descendants(child);
        s0.lemma_descendants(id);
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
            admit()
        }
        assert((seq![child] + des2.to_seq() + des1.to_seq()).to_multiset() =~= des.to_seq().to_multiset()) by{
            admit()
        }


        assert(
            res =~=
            (seq![child] + des2.to_seq() + des1.to_seq()).fold_left(s0, f)
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
               des2.to_seq() + des1.to_seq() + seq![child],
               f,
               s0,
               |s:Self| s.wf(),
               |x:usize| true 
            )
        }

        assert((seq![child] + des2.to_seq() + des1.to_seq()).drop_first() =~= des2.to_seq() + des1.to_seq());
        (seq![child] + des2.to_seq() + des1.to_seq()).lemma_fold_left_alt(s0, f);
        // (des2.to_seq() + des1.to_seq()).lemma_fold_left_alt(s0.remove_node(child), f);
        assert(res =~=
            (des2.to_seq() + des1.to_seq()).fold_left_alt(
                s0.remove_node(child), f
            )
        );
        assert(self.remove_one_edge(id, child).remove_node(child) =~= self.remove_node(child)) by{
            admit()
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
               |x:usize| true 
            )
        }
    }

    proof fn lemma_aux_99(self, id:usize, child:usize)
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
                self.lemma_aux_99_99(id, child, y)
            }
        }
    }

    proof fn lemma_aux_99_99(self, id:usize, child:usize, y:usize)
        requires
            self.wf(),
            self.is_parent_of(id, child),
            self.has_path(child, y),
        ensures
            self.remove_one_edge(id, child).has_path(child, y)
    {
        admit()
        // prove by induction on length of path
    }

    proof fn lemma_aux_9(self, id:usize, child:usize)
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
            self.lemma_aux_99(id, child);
            assert(self.remove_one_edge(id, child).descendants(child).subset_of(self.descendants(id)));
        }

        admit()
    }



}





}//verus!





pub fn test(){

    let n1 = Node{ id:1, child : vec![2,3], val : String::from("n1")};
    let n2 = Node{ id:2, child : vec![], val : String::from("n2")};
    let n3 = Node{ id:3, child : vec![5, 6], val : String::from("n3")};
    let n4 = Node{ id:4, child : vec![], val : String::from("n4")};
    let n5 = Node{ id:5, child : vec![4], val : String::from("n5")};
    let n6 = Node{ id:6, child : vec![], val : String::from("n6")};

    let mut tree = IndexTree { nodes : HashMap::new()};
    tree.nodes.insert(1, n1);
    tree.nodes.insert(2, n2);
    tree.nodes.insert(3, n3);
    tree.nodes.insert(4, n4);
    tree.nodes.insert(5, n5);
    tree.nodes.insert(6, n6);

    println!("{:?}" , tree);

    // tree.revoke_2(3);
    tree.revoke(3);
    println!("{:?}" , tree);


    // tree.revoke(1);
    // println!("{:?}" , tree);


}