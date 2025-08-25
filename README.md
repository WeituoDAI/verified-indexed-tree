# verified-indexed-tree

## Overview

In this project, we define indexed tree data structure, and make the formal verification with the tool Verus.


This project contains:

- `types.rs` defines the data structure.
- `spec.rs` proves the correctness of the tree operation.
- `exec.rs` defines the executable function `revoke`.
- `set.rs` `fold.rs` contain general lemmas used in the proof.

The main motivation and the main result of this project is to prove the correctness of the "revoke" tree operation (a recursive function that aims to remove all descendants of a node in the tree). It is not an easy work as I initially thought. It is possible to port the proof to other cases that involves tree-like data structure (like the derived Drop operation in tree)



## Verus

https://github.com/verus-lang/verus?tab=readme-ov-file



## Verification

Install the Verus (check Verus official site)

Modify the path of "Verifier" in Makefile and run the verifier by command line.
