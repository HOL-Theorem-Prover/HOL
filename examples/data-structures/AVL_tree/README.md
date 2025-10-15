# Formal Verification of AVL Trees in HOL4

This project formalizes and verifies the properties of AVL trees within the HOL4 theorem prover, ensuring that balance and logarithmic depth are maintained after insertions and deletions. AVL trees maintain their balance through rotations, which ensures that the height grows logarithmically with the number of nodes.

The minimum number of nodes in an AVL tree of a given height corresponds to a modified Fibonacci sequence, illustrating the tree's balance efficiency. This connection is leveraged in our formalization, as the Fibonacci relation provides a lower bound on the number of nodes for a given height, supporting proofs that AVL trees are nearly optimal in height growth. 

Key definitions and theorems were adapted from *Basic Concepts in Data Structures* by Shmuel Tomi Klein and further properties by theorem statements in the Isabelle/HOL library.
