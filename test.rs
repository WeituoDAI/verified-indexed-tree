use crate::types::*;
use std::collections::HashMap;

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