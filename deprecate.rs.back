

// impl<T> AbsTree<T>{
//     pub proof fn lemma_childs_des(self, parent:usize, childs:Seq<usize>)
//         requires
//             self.wf(),
//             self.contains(parent),
//             self.childs_seq(parent) =~= childs,
//         ensures
//             forall |i:usize| #[trigger]self.descendants(parent).contains(i)
//                 ==>
//                 childs.contains(i)
//                 || (
//                     exists |ch:usize| childs.contains(ch) && #[trigger]self.descendants(ch).contains(i)
//                 )
//     {
//         assert forall |i:usize| #[trigger]self.descendants(parent).contains(i)
//             && !childs.contains(i)    
//             implies
//                 exists |ch:usize| childs.contains(ch) && #[trigger]self.descendants(ch).contains(i)
//         by{
//             assert(self.has_path(parent, i));
//             self.lemma_has_path_ensures(parent, i);

//             assert(!self.is_parent_of(parent, i)) by{
//                 if self.is_parent_of(parent, i){
//                     assert(childs.contains(i))
//                 }
//             }
//             let z = choose |z:usize| self.is_parent_of(parent, z) && self.has_path(z, i) ;
//             assert(self.is_parent_of(parent, z));
//             assert(childs.contains(z));
//             assert(self.descendants(z).contains(i));
//         }
//     }

//     pub proof fn lemma_des_subset(self, parent:usize, child:usize)
//         requires
//             self.wf(), //too strong
//             self.has_path(parent, child),
//         ensures
//             self.descendants(child).subset_of(self.descendants(parent))
//     {
//         assert forall |j:usize| self.has_path(child, j) implies
//             self.has_path(parent, j) by
//         {
//             self.lemma_path_trans(parent, child, j)
//         }
//     }

//     pub proof fn lemma_revoke_parent_des(self, parent:usize, child:usize)
//         requires
//             self.wf(),
//             self.is_parent_of(parent, child),
//         ensures
//             self.revoke(child).descendants(parent)
//             =~= self.descendants(parent) - self.descendants(child)
//     {
//         let post = self.revoke(child);
//         self.lemma_revoke_path0(child);
//         self.lemma_revoke_ensures(child);

//         assert forall |e:usize|
//                 post.descendants(parent).contains(e)
//             implies
//                 self.descendants(parent).contains(e)
//                 && ! self.descendants(child).contains(e)
//         by
//         {
//             assert(self.descendants(parent).contains(e));
//             assert(post.has_path(parent, e));
//             post.has_path_ensures(parent, e);
//             assert(post.contains(e));
//             assert(!self.descendants(child).contains(e));            
//         }

//         assert forall |e:usize|
//                 self.descendants(parent).contains(e)
//                 && ! self.descendants(child).contains(e)
//             implies 
//                 post.descendants(parent).contains(e)
//         by
//         {
//             assert(self.has_path(parent, e));
//             assert(!self.has_path(child, e));
//             assert(parent != child);
//             assert(post.has_path(parent, e)) by{
//                 self.lemma_revoke_path(child);
//             }
//         }
//     }
//
//     pub proof fn lemma_revoke_path0(self, id:usize)
//         requires
//             self.wf()
//         ensures
//             forall |x:usize, y:usize|
//                 x != id && y != id &&
//                 !self.has_path(id, x) &&
//                 self.is_parent_of(x, y) ==>
//                 #[trigger]self.revoke(id).is_parent_of(x, y),

//             //structure specific
//             forall |x:usize|
//                 self.contains(x) &&
//                 x != id  && !self.has_path(id, x)
//                 ==> #[trigger] self.revoke(id).nodes[x] =~= self.nodes[x]
//                     && self.revoke(id).contains(x)
//                 ,
//     {
//         self.lemma_descendants(id);
//         let des = self.descendants(id).to_seq();
//         assert(self.descendants(id).finite());
//         let f = |s:Self, y:usize| s.remove_node(y);
//         let post = self.revoke(id);
//         assert(post == des.fold_left(self, f));

//         assert forall |x:usize, y:usize|
//                 x != id && y != id &&
//                 !self.has_path(id, x) &&
//                 self.is_parent_of(x, y) implies
//                 #[trigger]self.revoke(id).is_parent_of(x, y) by
//         {

//             let inv = |s:Self| (!s.has_path(id, x)) && s.wf() && s.is_parent_of(x, y);

//             assert forall |e:usize, acc:Self| (des.contains(e) && inv(acc)) implies #[trigger]inv(f(acc, e)) by{
//                 self.descendants(id).lemma_to_seq_to_set_id();
//                 assert(self.descendants(id).contains(e));
//                 assert(self.has_path(id, e));
//                 acc.lemma_remove_node_wf(e);
//                 acc.lemma_remove_node_path(e);
//                 assert(f(acc, e).wf());
//                 assert(!f(acc, e).has_path(id, x)) by {
//                     if acc.remove_node(e).has_path(id, x) {
//                         assert(acc.has_path(id, x));
//                         assert(false);
//                     }
//                 }
//                 assert(f(acc, e).is_parent_of(x, y)) by {
//                     assert(self.has_path(id, e));
//                     assert(x != e) by {
//                         if x == e {
//                             assert(self.has_path(id, x));
//                         }
//                     }
//                     assert(y != e) by {
//                         if y == e {
//                             assert(self.has_path(id, y));
//                             self.lemma_has_path_ensures(id, y);
//                             if self.is_parent_of(id, y){
//                                 assert(id == x);
//                                 assert(false);
//                             }
//                             else{
//                                 let z = choose |z:usize| self.has_path(id, z) && self.is_parent_of(z, y);
//                                 assert(self.is_parent_of(z, y));
//                                 assert(z == x);
//                                 assert(self.has_path(id, x));
//                                 assert(false);
//                             }
//                         }
//                     }
//                     assert(acc.remove_node(e).is_parent_of(x, y)) by {
//                         acc.lemma_remove_node_path0(e);
//                     }
//                 }
//             }

//             crate::fold::lemma_fold_left_preserves_inv(des, f, self, inv);

//             assert(post.wf());
//             assert(!post.has_path(id, x));

//         }

//         assert forall |x:usize|
//             self.contains(x) &&
//             x != id  && !self.has_path(id, x)
//             implies 
//                 self.revoke(id).contains(x) &&
//                 #[trigger] self.revoke(id).nodes[x] =~= self.nodes[x]
//             by
//         {
//             let inv = |s:Self| 
//                 (!s.has_path(id, x)) && s.wf() && s.nodes[x] =~= self.nodes[x]
//                 && s.contains(x) 
//             ;

//             assert forall |e:usize, acc:Self| (des.contains(e) && inv(acc)) implies #[trigger]inv(f(acc, e)) by{
//                 acc.lemma_remove_node_wf(e);
//                 acc.lemma_remove_node_path(e);
//                 acc.lemma_remove_node_path0(e);
//                 self.descendants(id).lemma_to_seq_to_set_id();
//                 assert(self.descendants(id).contains(e));
//                 assert(self.has_path(id, e));
//                 assert(f(acc, e).wf());
//                 assert(!f(acc, e).has_path(id, x)) by {
//                     if acc.remove_node(e).has_path(id, x) {
//                         assert(acc.has_path(id, x));
//                         assert(false);
//                     }
//                 }
//                 assert(f(acc, e).contains(x));
//                 assert(f(acc, e).nodes[x] =~= self.nodes[x]) by {
//                     assert(acc.nodes[x] =~= self.nodes[x]);

//                     acc.lemma_remove_node_path0(e);
//                     assert(acc.contains(x));
//                     assert(e != id) by {
//                         if e == id {
//                             assert(self.has_path(id, id));
//                             assert(self.contains(id));
//                             assert(false);
//                         }
//                     }

//                     assert(!acc.is_parent_of(x, e))  by {
//                         assert(acc.nodes[x] =~= self.nodes[x]);
//                         if acc.is_parent_of(x, e) {
//                             assert(self.nodes[x].child.contains(e));
//                             assert(self.is_parent_of(x, e));
//                             assert(self.has_path(id, e));
//                             self.lemma_has_path_ensures(id, e);
//                             if self.is_parent_of(id, e){
//                                 assert(x == id);
//                                 assert(false);
//                             }
//                             else {
//                                 let z = choose |z:usize| self.has_path(id, z) && self.is_parent_of(z, e);
//                                 assert(self.is_parent_of(z, e));
//                                 assert(z == id);
//                                 assert(self.has_path(id, id));
//                                 assert(self.contains(id));
//                                 assert(false)
//                             }
//                         }
//                     }
//                 }
//             }
//             crate::fold::lemma_fold_left_preserves_inv(des, f, self, inv);
//             assert(post.contains(x));
//             assert(post.nodes[x] =~= self.nodes[x]);
//         }
//     }
//
//     pub proof fn lemma_remove_node_desc(self, id:usize)
//         requires
//             self.wf()
//         ensures
//             forall |x:usize|
//                 x != id &&
//                 !self.has_path(x, id) ==>
//                 #[trigger]self.remove_node(id).descendants(x) =~= self.descendants(x)
//     {
//         assert forall |x:usize|
//                 x != id &&
//                 !self.has_path(x, id) implies
//                 #[trigger]self.remove_node(id).descendants(x) =~= self.descendants(x) by
//         {
//             assert forall |y:usize|
//                 self.descendants(x).contains(y)
//                 implies #[trigger]self.remove_node(id).descendants(x).contains(y)
//             by{
//                 assert(self.has_path(x, y));
//                 assert(y != id);
//                 self.lemma_remove_node_path(id);
//             }

//             assert forall |y:usize|
//                 #[trigger]self.remove_node(id).descendants(x).contains(y)
//                 implies self.descendants(x).contains(y)
//             by{
//                 self.lemma_remove_node_path(id);
//             }
//         }
//     }
// }

// impl<T> AbsTree<T>{
//     pub proof fn lemma_remove_par(self, id:usize, parent:usize, child:usize)
//         requires
//             self.wf(),
//             self.is_parent_of(parent, child),
//             !self.has_path(id, child),
//             id != child,
//         ensures
//             self.remove_node(id).is_parent_of(parent, child)
//     {
//         assert(parent != id) by {
//             if parent == id {
//                 assert(!self.has_path(parent, child));
//                 self.lemma_parent_to_path(parent, child);
//                 assert(false)
//             }
//         }
//         self.lemma_remove_node_path0(id);
//     }

//     pub proof fn lemma_revoke_par(self, id:usize, parent:usize, child:usize)
//         requires
//             self.wf(),
//             self.is_parent_of(parent, child),
//             !self.has_path(id, child),
//         ensures
//             self.revoke(id).is_parent_of(parent, child)
//     {
//         self.lemma_revoke_path2(id);
//         assert(parent != id) by {
//             if parent == id {
//                 assert(self.is_parent_of(parent, child));
//                 self.lemma_parent_to_path(parent, child);
//                 assert(false)
//             }
//         }
//     }

//     pub proof fn lemma_revoke_and_remove_self_par(self, id:usize, parent:usize, child:usize)
//         requires
//             self.wf(),
//             self.is_parent_of(parent, child),
//             id != child,
//             !self.has_path(id, child),
//         ensures
//             self.revoke_and_remove_self(id).is_parent_of(parent, child)
//     {
//         let res = self.revoke_and_remove_self(id);
//         let r1 = self.revoke(id);
//         assert(res == r1.remove_node(id));
//         assert(r1.is_parent_of(parent, child)) by{
//             self.lemma_revoke_par(id, parent, child)
//         }
//         assert(r1.wf()) by { self.lemma_revoke_wf(id) }
//         assert(!r1.has_path(id, child)) by{
//             if r1.has_path(id, child) {
//                 assert(self.has_path(id, child)) by{
//                     self.lemma_revoke_path0(id)
//                 }
//             }
//         }
//         r1.lemma_remove_par(id, parent, child)
//     }

//     pub proof fn lemma_000(self, parent:usize, child:usize)
//         requires
//             self.wf(),
//             self.is_parent_of(parent, child),
//             self.childs(child).is_empty(),
//         ensures
//            (Self{
//                 nodes : self.remove_one_edge(parent, child).nodes.remove(child)
//             })
//             =~= self.remove_node(child)
//     {
//         self.lemma_remove_one_edge_remove_edges_to(parent, child);
//     }
// }



// impl<T> AbsTree<T>{
//     pub proof fn lemma_childs_revoke(self, parent:usize)
//         requires
//             self.wf(),
//             self.contains(parent),
//         ensures
//             self.childs_seq(parent).fold_left(
//                 self,
//                 |x:Self, y:usize| x.revoke_and_remove_self(y)
//             )
//             =~=
//             self.revoke(parent)
//         decreases
//             self.childs_seq(parent).len(),
//     {
//         let seq_child = self.childs_seq(parent);
//         let f = |x:Self, y:usize| x.revoke_and_remove_self(y);
//         let res = self.childs_seq(parent).fold_left(self, f);


//         if seq_child.len() == 0 {
//             assert(self.descendants(parent).finite()) by {
//                 self.lemma_descendants(parent)
//             }
//             assert(self.descendants(parent).len() == 0) by {
//                 self.lemma_childs_des(parent, seq_child);
//                 if self.descendants(parent).len() > 0 {
//                     let e = self.descendants(parent).choose();
//                     assert(self.descendants(parent).contains(e));
//                     assert(!seq_child.contains(e));
//                     let ch = choose |ch:usize| seq_child.contains(ch) && #[trigger]self.descendants(ch).contains(e);
//                     assert(seq_child.contains(ch));
//                     assert(false)
//                 }
//             }
//             assert(self.descendants(parent).to_seq().len() == 0) by {
//                 self.descendants(parent).lemma_to_seq_to_set_id();
//                 crate::set::lemma_set_to_seq_len(self.descendants(parent))
//             }
//         }
//         else {
//             assert(self.contains(parent));

//             let child1 = seq_child[0];
//             let s1 = seq![child1];
//             let s2 = seq_child.subrange(1, seq_child.len() as int);
//             let r1 = self.revoke_and_remove_self(child1);

//             // assert()

//             assert(s2.fold_left(r1, f) == res) by {
//                 seq_child.lemma_fold_left_split(self, f, 1);
//                 assert(r1 == s1.fold_left(self, f)) by {
//                     reveal_with_fuel(vstd::seq::Seq::fold_left, 2)
//                 };
//                 assert(s1 =~= seq_child.subrange(0, 1));
//             }

//             assert(res =~= s2.fold_left(r1, f));

//             ////proof schema

//             assert(r1.wf()) by{
//                 assert(self.contains(child1)) by {
//                     assert(self.nodes[parent].child.contains(child1));
//                     assert(self.nodes.contains_key(child1))
//                 }
//                 self.lemma_revoke_and_remove_self_wf(child1);
//             }
//             assert(r1.contains(parent)) by {
//                 self.lemma_revoke_and_remove_self_wf(child1);
//                 assert(r1.dom() =~= self.dom() - self.descendants(child1) - set![child1]);
//                 assert(self.contains(parent));
//                 assert(self.is_parent_of(parent, child1));
//                 assert(self.has_path(parent, child1)) by { self.lemma_parent_to_path(parent, child1)};
//                 assert(parent != child1) by {
//                     if parent == child1 {
//                         assert(self.is_parent_of(parent, parent));
//                         assert(self.has_path(parent, parent)) by {
//                             self.lemma_parent_to_path(parent, parent)
//                         }
//                         assert(false);
//                     }
//                 }
//                 assert(!self.descendants(child1).contains(parent)) by {
//                     if self.has_path(child1, parent){
//                         assert(self.has_path(parent, parent)) by {
//                             self.lemma_path_trans(parent, child1, parent)
//                         }
//                     }
//                 }
//             }

//             assert(r1.childs_seq(parent).len() == s2.len()
//                    && r1.childs_seq(parent) =~= s2) by
//             {
//                 // if not
//                 // we can only prove that
//                 // r1.childs_seq(parent).to_multiset() =~= s2.to_multiset()
//                 self.lemma_childs_remvoke_and_remove_aux(parent, child1);
//             }
//             assert(
//                 r1.childs_seq(parent).fold_left(r1, f) =~= r1.revoke(parent)
//             ) by
//             {
//                 r1.lemma_childs_revoke(parent)
//             }

//             assert(
//                 self.revoke(child1).remove_node(child1).revoke(parent) =~= self.revoke(parent)
//             ) by
//             {
//                 self.lemma_childs_revoke_aux_2(parent, child1)
//             }

//         }
//     }


//     proof fn lemma_childs_remvoke_and_remove_aux(self, parent:usize, child1:usize)
//         requires
//             self.wf(),
//             self.contains(parent),
//             self.childs_seq(parent).len() > 0,
//             self.childs_seq(parent)[0] == child1,
//         ensures
//             self.revoke_and_remove_self(child1).childs_seq(parent)
//              =~= self.childs_seq(parent).drop_first()      
//     {
//         assert(self.is_parent_of(parent, child1));
//         self.lemma_parent_to_path(parent, child1);
//         let post = self.revoke_and_remove_self(child1);
//         self.lemma_revoke_path0(child1);
//         assert(self.contains(parent));
//         assert(parent != child1) by{
//             if parent == child1 {
//                 assert(self.has_path(parent, parent));
//                 assert(false)
//             }
//         }
//         assert(!self.has_path(child1, parent)) by{
//             if self.has_path(child1, parent){
//                 assert(self.has_path(parent, child1));
//                 self.lemma_path_trans(parent, child1, parent);
//                 assert(self.has_path(parent, parent));
//                 assert(false)
//             }
//         }

//         assert(self.revoke(child1).nodes[parent] =~= self.nodes[parent]);
//         assert(self.revoke(child1).contains(parent));

//         let r1 = self.revoke(child1);
//         let r2 = r1.remove_node(child1);
//         assert(r1.childs_seq(parent) =~= self.childs_seq(parent));

//         self.lemma_revoke_wf(child1);
//         r1.lemma_remove_node_ensures(child1);

//         assert(r2.contains(parent));
//         assert(r2.nodes[parent] =~= r1.nodes[parent].remove_child(child1));
//         assert(r2.nodes[parent].child =~= self.nodes[parent].child.remove_value(child1));

//         let seq = self.nodes[parent].child;
//         assert(seq[0] == child1);

//         let index = seq.index_of_first(child1);
//         seq.index_of_first_ensures(child1);
//         // assert(index is Some);
//         assert(index.unwrap() == 0);
//         assert(seq.remove_value(child1) =~= seq.drop_first());
//     }

//     #[verifier::spinoff_prover]
//     proof fn lemma_childs_revoke_aux_2(self, parent:usize, child:usize)
//         requires
//             self.wf(),
//             self.is_parent_of(parent, child)
//         ensures
//             self.revoke(child).remove_node(child).revoke(parent) =~= self.revoke(parent)
//     {
//         assert(self.revoke(child).descendants(parent)
//             =~= self.descendants(parent) - self.descendants(child)
//         ) by
//         {
//             self.lemma_revoke_parent_des(parent, child)
//         }

//         assert(self.contains(parent));
//         assert(self.contains(child));
//         self.lemma_parent_to_path(parent, child);
//         assert(parent != child);

//         let r1 = self.revoke(child);
//         let r2 = r1.remove_node(child);
//         let res = r2.revoke(parent);
//         let res0 = self.revoke(parent);
//         let des1 = self.descendants(parent);
//         let des2 = self.descendants(child);

//         assert(r1.wf()) by { self.lemma_revoke_wf(child) }
//         assert(r2.wf()) by { r1.lemma_remove_node_wf(child)}
        
//         assert(r1.descendants(parent) =~= des1 - des2);
//         assert(r1.remove_node(child).descendants(parent) =~= r1.descendants(parent) - set![child]) by{
//             assert(r1.remove_node(child).descendants(parent).subset_of(r1.descendants(parent))) by{
//                 r1.lemma_remove_node_path(child)
//             }
//             assert(!r1.remove_node(child).descendants(parent).contains(child)) by{
//                 if r1.remove_node(child).has_path(parent, child){
//                     r1.remove_node(child).has_path_ensures(parent, child);
//                     assert(r1.remove_node(child).contains(child));
//                     assert(false)
//                 }
//             }
//             assert forall |j:usize| #[trigger]r1.has_path(parent, j) && j != child implies
//                 r1.remove_node(child).has_path(parent, j) by
//             {
//                 r1.lemma_remove_node_path(child);
//                 assert(parent != child);
//                 assert(j != child);
//                 assert(!r1.has_path(child, j)) by {
//                     assert(r1.descendants(child).is_empty()) by {
//                         self.lemma_revoke_wf(child)
//                     }
//                     if r1.has_path(child, j){
//                         assert(r1.descendants(child).contains(j))
//                     }
//                 }
//             }
//         }
//         assert(!des2.contains(child));
//         let des3 = r2.descendants(parent);
//         assert(des3 =~= des1 - des2 - set![child]);
//         self.lemma_descendants(parent);
//         self.lemma_descendants(child);

//         let f = |s:Self, y:usize| s.remove_node(y);

//         assert(r1 =~= des2.to_seq().fold_left(self, f));
//         assert(r2 =~= f(r1, child));
//         assert(r2 =~= des2.to_seq().push(child).fold_left(self, f)) by {
//             assert(des2.to_seq().push(child).drop_last() =~= des2.to_seq())
//         }

//         assert(res =~= des3.to_seq().fold_left(r2, f));
        
//         let seq = des2.to_seq().push(child) + des3.to_seq();
//         assert(res =~= seq.fold_left(self, f)) by{
//             seq.lemma_fold_left_split(
//                 self, f, des2.to_seq().push(child).len() as int
//             );
//             assert(seq.subrange(0, des2.to_seq().push(child).len() as int)
//                 =~= des2.to_seq().push(child)
//             );
//             assert(seq.subrange(des2.to_seq().push(child).len() as int, seq.len() as int)
//                 =~= des3.to_seq()
//             )
//         }

//         assert(res0 =~= des1.to_seq().fold_left(self, f));

//         assert(des1.to_seq().to_set() =~= des1) by{
//             des1.lemma_to_seq_to_set_id()
//         }
//         assert(des2.to_seq().to_set() =~= des2) by{
//             des2.lemma_to_seq_to_set_id()
//         }
//         assert(des3.to_seq().to_set() =~= des3) by{
//             des3.lemma_to_seq_to_set_id()
//         }

//         assert(seq.to_set() =~= des1) by{
//             assert(seq.to_set() =~= des2.to_seq().push(child).to_set() + des3.to_seq().to_set()) by{
//                 vstd::seq_lib::seq_to_set_distributes_over_add(
//                     des2.to_seq().push(child),
//                     des3.to_seq()
//                 )
//             }
//             assert(des2.to_seq().push(child) =~= des2.to_seq() + seq![child]);
//             assert((des2.to_seq() + seq![child]).to_set() =~= des2.to_seq().to_set().insert(child)) by{
//                 vstd::seq::Seq::lemma_to_set_insert_commutes(des2.to_seq(), child)
//             }
//             assert(seq.to_set() =~= des2.to_seq().to_set().insert(child) + des3.to_seq().to_set());

//             assert(seq.to_set() =~= des2 + set![child] + des3);
//             assert(des3 =~= des1 - des2 - set![child]);
//             assert(des1 =~= des3 + des2 + set![child]) by{
//                 assert(des2.subset_of(des1)) by{
//                     self.lemma_des_subset(parent, child);
//                 }
//                 assert(des1.contains(child)) by {
//                     self.is_parent_of(parent, child);
//                 }
//             }
//         }

//         assert(seq.to_set() =~= des1);

//         assert(seq =~= des2.to_seq() + seq![child] + des3.to_seq());

//         assert(des1.to_seq().no_duplicates()) by{
//             crate::set::lemma_set_to_seq_no_duplicates(des1)
//         }

//         assert(seq.no_duplicates()) by{
//             assert(des2.to_seq().no_duplicates()) by{
//                 crate::set::lemma_set_to_seq_no_duplicates(des2)
//             }
//             assert(!des2.contains(child));
//             let s1 = des2.to_seq() + seq![child];
//             let s2 = des3.to_seq();
//             assert(s1.no_duplicates()) by{
//                 assert forall |i:int, j:int| 0 <= i < j < s1.len() implies s1[i] != s1[j] by
//                 {
//                     if j < des2.to_seq().len() {}
//                     else {
//                         assert(s1[j] == child);
//                         assert(des2.to_seq().contains(s1[i]));
//                     }
//                 }
//             }
//             assert(des3.to_seq().no_duplicates()) by{
//                 crate::set::lemma_set_to_seq_no_duplicates(des3)
//             }
//             assert(s2.no_duplicates());

//             assert( (s1 + s2).no_duplicates() ) by{
//                 assert forall|i: int, j: int| 0 <= i < s1.len() && 0 <= j < s2.len() implies s1[i] != s2[j] by
//                 {
//                     assert((des2 + set![child]).contains(s1[i]));
//                     assert(des3.contains(s2[j]));
//                     assert(des3 =~= des1 - des2 - set![child]);
//                 }
//                 vstd::seq_lib::lemma_no_dup_in_concat(s1, s2);
//             } 
//         }
//         assert(des1.to_seq().to_multiset() =~= seq.to_multiset()) by{
//             crate::set::lemma_no_duplicates_seq_to_set_to_multiset(des1.to_seq(), seq)
//         }

//         assert(res == res0) by{
//             let inv = |s:Self| s.wf(); // too strong ?
//             assert forall |e:usize, acc:Self| inv(acc) implies #[trigger]inv(f(acc, e)) by
//             {
//                 assert(acc.wf());
//                 assert(acc.remove_node(e).wf()) by{
//                     acc.lemma_remove_node_wf(e)
//                 }
//             };
//             assert forall |x:usize, y:usize, acc:Self| inv(acc) implies #[trigger]f(f(acc, x), y) == f(f(acc, y), x) by
//             {
//                 Self::lemma_remove_node_commut()
//             }
//             crate::fold::lemma_fold_left_permutation_with_inv(
//                 des1.to_seq(), seq, f, self, inv,
//             )
//         }

//     }


//     // proof fn lemma_revoke_non(self, i:usize)
//     //     requires !self.contains(i), self.wf(),
//     //     ensures self.revoke(i) =~= self
//     // {
//     //     assert(self.descendants(i) =~= Set::empty()) by{
//     //         assert forall |j:usize| !#[trigger]self.has_path(i, j) by{
//     //             if self.has_path(i, j){
//     //                 self.has_path_ensures(i, j)
//     //             }
//     //         }
//     //     }
//     // }

//     // proof fn lemma_remove_node_non(self, i:usize)
//     //     requires !self.contains(i), self.wf(),
//     //     ensures self.remove_node(i) =~= self
//     // {}
// }



// //exec fn
// ///////////////////////////////////////////////////////////


// impl<T> IndexTree<T>{
//     #[verifier::external_body]
//     pub fn remove_one_edge(&mut self, parent:usize, child:usize)
//         requires
//             old(self)@.is_parent_of(parent, child),
//      
//             // old(self)@.nodes[parent].child[0] == child, //todo
//         ensures
//             self@ =~= old(self)@.remove_one_edge(parent, child)
//     {
//         self.nodes.get_mut(&parent).unwrap().child.remove(0);
//         // unimplemented!()
//     }
// }




// impl<T> IndexTree<T>{

//     // not efficient
//     #[verifier::exec_allows_no_decreases_clause]
//     #[verifier::loop_isolation(false)]
//     pub fn revoke(&mut self, id:usize)
//         requires
//             old(self).nodes@.contains_key(id),
//             old(self)@.wf(),
//         ensures
//             self@ =~= old(self)@.revoke(id),
//         // decreases
//         //     old(self).to_cdt().height(id),
//     {
//         let children = self.nodes.get(&id).unwrap().child.clone();
//         assert(children@ =~= self@.childs_seq(id));
//         assert(children@.no_duplicates()) by{
//             assert(self@.nodes.contains_key(id))
//         }

//         let ghost prev = *self;

//         assert forall |j:int| 0 <= j < children@.len() implies
//             #[trigger]self@.nodes.contains_key(children@[j]) by
//         {
//             assert(self@.contains(id));
//         }

//         assert forall |j:int| 0 <= j < children@.len() implies
//             #[trigger]self@.is_parent_of(id, children@[j]) by
//         {}

//         assert forall |j:int, k:int| 0 <= j < k < children@.len() implies
//             !#[trigger]self@.has_path(children@[j], children@[k]) by
//         {
//             broadcast use AbsTree::lemma_parent_to_path;
//             self@.lemma_path_contradict(id, children@[j], children@[k])
//         }

//         for i in 0..children.len()
//             invariant
//                 //I1
//                 self@ =~= children@.subrange(0, i as int).fold_left(
//                     prev@, |x:AbsTree<T>, j:usize| x.revoke_and_remove_self(j) 
//                 ),
//                 //I2
//                 self@.wf(),

//                 //I3 // implied by I4
//                 // forall |j:int| i <= j < children@.len() ==>
//                 //    #[trigger]self@.nodes.contains_key(children@[j]),

//                 //I4
//                 forall |j:int| i <= j < children@.len() ==>
//                    #[trigger]self@.is_parent_of(id, children@[j]),
 
//                 //I5
//                 forall |j:int, k:int| i <= j < k < children@.len() ==>
//                    !#[trigger]self@.has_path(children@[j], children@[k]),


//                 //I6
//                 // self@.nodes[id].child =~= children@.subrange(i as int, children@.len() as int),

//                 // children@ =~= self.
//         {
//             let ghost t0 = *self;
//             let child = children[i];
//             assert(self.nodes@.contains_key(child)) by {
//                 assert(self@.is_parent_of(id, child));
//                 assert(self@.nodes.contains_key(child));
//                 assert(self@.nodes.dom() =~= self.nodes@.dom());
//             }

//             self.revoke(child);
//             let ghost t1 = *self; ////

//             proof{
//                 assert(self@.is_parent_of(id, child)) by {
//                     assert(t0@.contains(child));
//                     assert(!t0@.has_path(child, child));
//                     t0@.lemma_revoke_par(child, id, child);
//                 };
//                 t0@.lemma_revoke_wf(child)
//             }
//             self.remove_one_edge(id, child);
//             assert(self@ =~= t1@.remove_one_edge(id, child));
//             assert(self@.contains(id));
//             assert(self@.contains(child));

//             let ghost t2 = *self;//
//             self.nodes.remove(&child);

//             assert(self@.nodes =~= t2@.nodes.remove(child));

//             //I1
//             proof{
//                 assert(self@ =~= t1@.remove_node(child)) by {
//                     t1@.lemma_000(id, child);
//                 }
//                 assert(self@ =~= t0@.revoke_and_remove_self(child));
//                 assert(t0@ =~= 
//                     children@.subrange(0, i as int).fold_left(
//                         prev@, |x:AbsTree<T>, j:usize| x.revoke_and_remove_self(j) 
//                     )
//                 );
//                 assert(
//                     children@.subrange(0, i as int + 1).drop_last() =~=
//                     children@.subrange(0, i as int)
//                 );
//             }

//             //I2
//             proof {
//                 t0@.lemma_revoke_and_remove_self_wf(child);
//             }

//             //I3
//             // proof{
//             //     assert forall |j:int| i + 1 <= j < children@.len() implies 
//             //        #[trigger]self@.nodes.contains_key(children@[j]) by
//             //     {
//             //     }
//             // }

//             //I4
//             proof{
//                 assert forall |j:int| i + 1 <= j < children@.len() implies
//                    #[trigger]self@.is_parent_of(id, children@[j]) by
//                 {
//                     assert(!t0@.has_path(child, children@[j]));
//                     t0@.lemma_revoke_and_remove_self_par(child, id, children@[j]);
//                 }
//             }

//             //I5
//             proof{
//                 assert forall |j:int, k:int| i + 1 <= j < k < children@.len() implies
//                    !#[trigger]self@.has_path(children@[j], children@[k]) by
//                 {
//                     broadcast use AbsTree::lemma_parent_to_path;
//                     assert(children@[j] != children@[k]) by{
//                         assert(children@.no_duplicates());
//                     }
//                     self@.lemma_path_contradict(id, children@[j], children@[k])
//                 }
//             }
//         }


//         proof{
//             assert(children@.subrange(0, children@.len() as int) =~= children@);
//             assert(
//                 self@ =~= children@.fold_left(
//                     prev@, |x:AbsTree<T>, j:usize| x.revoke_and_remove_self(j) 
//                 )
//             );
//             old(self)@.lemma_childs_revoke(id);
//         }

//     }


// }
