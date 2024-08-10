# Generic Graphs

There are many mostly orthogonal variables that can be tweaked to generate different flavours of graph.

('a,'b,'c,'d,'e,'f,'g,'h) graph

   'a   type of nodes (actually nodes are 'a + num)
   'b   directed (itself2bool(:β)) or not 
          (use `:undirectedG` or `:directedG`)
   'c   edge-cst (see below)
   'd   type of labels on edges (use `:unit` for "no label")
   'e   hyper-graph or not (use `:hyperG` or `:unhyperG`)
   'f   finiteness of nodes (use `:finiteG` or `:INF_OK`)
   'g   type of labels on nodes (use `:unit` for "no label")
   'h   self-loops OK or not (use `:SL_OK` for yes; and `:noSL` for no)

A hyper-graph is one where edges are from/to sets of nodes instead of
single nodes. A self-looping edge in an undirected hyper-graph is one
where the set of nodes is a singleton (which is the same as the
handling for normal, non-hyper graphs). In a directed hyper-graph, a
self-loop is one where the same node occurs both in the from set and
the to-set.

## Types of Nodes

The type of nodes in an `:(α,...) graph` are `:'a + num`. This
guarantees that there are always at least countably many values in the
universe of the node type.

## Types of Edges

There are two types of edge `:(α,'l) diredge` and `:(α,’l) undiredge` with constructors

    directed : (α+num) set -> (α+num) set -> 'l -> 
               (α,'l) diredge
    undirected : (α+num) set -> 'l -> (α,'l) undiredge

The sets under the `directed` constructor support hyper-edges.
Similary, if the set under the `undirected` constructor is of size >
2, this is also a hyper-edge. Then, all graphs are built from `:(α,'l)
core_edge`, with declaration

    (α,'l) core_edge = cDE (α,'l) diredge | cUDE (α,'l) undiredge

## Edge Constraint Choice

This is the most complicated parameter, encoding four possibilities,
that constrain the members of the bag/multiset of edges that are
inside the graph. Below, a “position” is a possible place in the graph
where an edge might occur. For example, a non-hyper, non self-looping,
undirected graph has positions that are two-element sets of nodes. A
directed, possibly self-looping, hyper-graph has positions that are
pairs of non-empty sets of nodes.

   - `ONE_EDGE`: there is only one edge for any possible position
   - `ONE_EDGE_PERLABEL`: there is only one edge per position-label combination
   - `FINITE_EDGE`: there are only finitely many edges for any possible position.
   - `UNC_EDGES`: there are no constraints on the number of edges (except there can only be finitely many copies of the same edge).

## Flavours of graph

(α,β,γ,δ,ε,’f) udgraph (general undirected (non-hyper) graph) has

    α  : type of nodes
    β  : edge “constraint”
    γ  : edge label
    δ  : node finiteness constraint
    ε  : node label
    ζ  : self-loops permitted?

(α,β,γ) fdirgraph

   (directed un-hyper graph with finitely many nodes, and finitely many edges
    between nodes, with self-loops permitted)

    α  : type of nodes
    β  : node label
    γ  : edge label

fsgraph

   "finite simple graph": 
     - ‘inherits from’ udulgraph
     - finite unlabelled nodes, 
     - no self-loops
     - max one, undirected, unlabelled edge between nodes
     
 nodes are natural numbers

## Functions Over Graphs

    nodes : (α, ...) graph -> (α + num) set
    edgebag : (α, 'dirp, 'ec, 'el, 'hp, 'nfp, 'nl, 'slp) graph ->
              (α,'el) core_edge bag
    edges : (α, directedG, 'ec, 'el, 'hp, 'nfp, 'nl, 'slp) ->
            (α,'el) diredge set
    udedges : (α, undirectedG, 'ec, 'el, 'hp, 'nfp, 'nl, 'slp) ->
              (α,'el) undiredge set

