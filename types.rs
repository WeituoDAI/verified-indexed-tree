use vstd::prelude::*;
use std::collections::HashMap;


verus!{

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
pub struct NodeAbs<T>{
    pub id : usize,
    pub child : Seq<usize>,
    pub val : T,
}

#[verifier::ext_equal]
pub struct AbsTree<T>{
    pub nodes : Map<usize, NodeAbs<T>>,
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

impl<T> Node<T>{
    pub open spec fn view(&self) -> NodeAbs<T>{
        NodeAbs{
            id : self.id,
            val : self.val,
            child : self.child@,
        }
    }
}

}//verus!