# Generic Graphs

There are many mostly orthogonal variables that can be tweaked to generate different flavours of graph.

('a,'b,'c,'d,'e,'f,'g) graph

   'a   type of nodes
   'b   directed (itself2bool(:β)) or not 
          (use `:undirectedG` or `:directedG`)
   'c   edge-cst (see below)
   'd   type of labels on edges (use `:unit` for "no label")
   'e   finiteness of nodes (use `:finiteG` or `:INF_OK`)
   'f   type of labels on nodes (use `:unit` for "no label")
   'g   self-loops OK or not (use `:SL_OK` for yes; and `:noSL` for no)

## Edge Constraint Choice

This is the most complicated parameter:

   - no constraints on size of edge set: type with cardinality > 2
   - type with cardinality = 2 (e.g., :bool) edges between two nodes are
     finite
   - type with cardinality = 1 (e.g., :one) only one edge possible between
     nodes

## Flavours of graph

(α,β,γ,δ,ε,’f) udgraph (general undirected graph) has

    α  : type of nodes
    β  : edge “constraint”
    γ  : edge label
    δ  : node finiteness constraint
    ε  : node label
    ζ  : self-loops permitted?

(α,β,γ) fdirgraph

   (directed graph with finitely many nodes, and finitely many edges
    between nodes)

    α  : type of nodes
    β  : node label
    γ  : edge label

α fsgraph 

   "finite simple graph": 
     - ‘inherits from’ udulgraph
     - finite unlabelled nodes, 
     - no self-loops
     - max one, undirected, unlabelled edge between nodes
     
    α : type of nodes  
    (maybe just make this num and remove polymorphism?)
           
