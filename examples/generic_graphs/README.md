# Generic Graphs

There are many mostly orthogonal variables that can be tweaked to generate different flavours of graph. The standard naming scheme uses type variables with names ending in 'p' to indicate boolean choices

(α,'dp,'ec,'el,'hp,'nfp,'nl,'slp) graph

   α     type of nodes (actually nodes are 'a + num)
   'dp   directed (itself2bool(:β)) or not
           (use `:undirectedG` or `:directedG`)
   'ec   edge-constraint (see below)
   'el   type of labels on edges (use `:unit` for "no label")
   'hp    hyper-graph or not (use `:hyperG` or `:unhyperG`)
   'nfp  finiteness of nodes (use `:finiteG` or `:INF_OK`)
   'nl   type of labels on nodes (use `:unit` for "no label")
   'slp  self-loops OK or not (use `:SL_OK` for yes; and `:noSL` for no)

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
2, this is also a hyper-edge. All graphs are built from `:(α,'l)
core_edge`, with declaration

    (α,'l) core_edge = cDE (α,'l) diredge
                     | cUDE (α,'l) undiredge

## Edge Constraint Choice

This is the most complicated parameter, currently encoding four
possibilities, that constrain the members of the bag/multiset of edges
that are inside the graph. Below, a “position” is a possible place in
the graph where an edge might occur. For example, a non-hyper, non
self-looping, undirected graph has positions that are two-element sets
of nodes. A directed, possibly self-looping, hyper-graph has positions
that are pairs of non-empty sets of nodes.

   - `ONE_EDGE`: there is only one edge for any possible position
   - `ONE_EDGE_PERLABEL`: there is only one edge per position-label combination
   - `FINITE_EDGE`: there are only finitely many edges for any possible position.
   - `UNC_EDGES`: there are no constraints on the number of edges (except there can only be finitely many copies of the same edge).

Note that `ONE_EDGE_PERLABEL` allows for infinitely many edges for a given position if there are infinitely many values in the `:'el` (edge-label) type.

## Some Graph Flavours

The following type abbreviations instantiate type variables to generate a set of what we imagine will be standard graph types of interest.

-   `:(α,'ec,'el,'nfp,'nl,’slp) udgraph`

    General undirected (non-hyper) graphs. This sets `:'dp` to `:undirectedG` and `:'hp` to `:unhyperG`.

    The remaining six parameters are (as before):

    α    : type of nodes
    'ec  : edge “constraint”
    'el  : edge label
    'nfp : node finiteness constraint
    'el  : node label
    'slp : self-loops permitted?

-   `:(α,'nfp,'slp)udulgraph`

    Undirected, unlabelled graphs.
    Sets the label types to `:unit` and requires `ONE_EDGE` for every position.

-   `:(α,'nl,'el) fdirgraph`

    Directed, un-hyper graph with finitely many nodes, and finitely many
    edges between nodes, with self-loops permitted.

    α   : type of nodes
    'nl : node label
    'el : edge label

    This type is modelled by the concrete (“implementable”) `gfg` type.
    (Every fdirgraph has a corresponding, well-formed `gfg` value.)

-   `:fsgraph`

    "finite simple graph":
     - ‘inherits from’ udulgraph
     - finite unlabelled nodes,
     - no self-loops
     - max one, undirected, unlabelled edge between nodes

    Nodes are `:unit + num` (the α used elsewhere is instantiated with `:unit`)

## Functions Over Graphs

### Getting information out of graphs:

    nodes : (α, ...) graph -> (α + num) set
    edgebag : (α, 'dp, 'ec, 'el, 'hp, 'nfp, 'nl, 'slp) graph ->
              (α,'el) core_edge bag
    edges : (α, directedG, 'ec, 'el, 'hp, 'nfp, 'nl, 'slp) ->
            (α,'el) diredge set
    udedges : (α, undirectedG,'ec,'el,'hp,'nfp,'nl,'slp) ->
              (α,'el) undiredge set
    nlabelfun : (α,'dp,'ec,'el,'hp,'nfp,'nl,'slp) graph ->
                α + num -> 'nl
    adjacent : (α,...)graph -> 'a + num -> 'a + num -> bool
    connected : (α,...) graph
    order : (α,'dp,'ec,'el,'hp,finiteG,'nl,'slp) graph -> num

### Building graphs (for finite builds)

    emptyG : (α,...) graph
    addNode : α + num -> 'nl ->
              (α,'dp,'ec,'el,'hp,'nfp,'nl,'slp) graph ->
              (α,'dp,'ec,'el,'hp,'nfp,'nl,'slp) graph
    addEdge : α + num -> α + num -> 'el ->
              (α,directedG,'ec,'el,'hp,'nfp,'nl,'slp) graph ->
              (α,directedG,'ec,'el,'hp,'nfp,'nl,'slp) graph
    addUDEdge : (α + num) set -> 'el ->
          (α,undirectedG,'ec,'el,'hp,'nfp,'nl,'slp) graph ->
          (α,undirectedG,'ec,'el,'hp,'nfp,'nl,'slp) graph
    nrelabel : α + num -> 'nl ->
               (α,'dp,'ec,'el,'hp,'nfp,'nl,'slp) graph ->
               (α,'dp,'ec,'el,'hp,'nfp,'nl,'slp) graph

Adding edges also adds the mentioned nodes if they are not already
present in the graph. If an edge is a self-loop and this is not
permitted by the `:'slp` variable, the operation does nothing (is the
identity function). Similarly, the set of nodes used to designate an edge in `addUDEdge` is purged of edges that are invalid for the graph (empty sets; sets that are too big).

### Building graphs (infinite options)

    addEdges : (α, 'el) direedge set ->
               (α,directedG,'ec,'el,'hp,'nfp,'nl,'slp) graph ->
               (α,directedG,'ec,'el,'hp,'nfp,'nl,'slp) graph

Again, the nodes involved get added as well. If the graph is supposed
to have finitely many nodes (`:'nfp`), but the incident nodes of the
input edges are infinite, the function returns the input graph
unchanged. Malformed edges (e.g., those with empty sets in source or
target position) are dropped. If `:'ec` maps to ONE_EDGE, then old
edges are replaced by incoming edges (as long as the input set of
edges only has one such for any given "position").

    projectG : (α + num) set ->
               (α,’dp,'ec,'el,'hp,'nfp,'nl,'slp) graph ->
               (α,’dp,'ec,'el,'hp,'nfp,'nl,'slp) graph

Projection restricts the nodes of the input graph to be those that also occur in the input set.
