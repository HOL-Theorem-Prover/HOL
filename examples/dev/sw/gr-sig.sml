(*
 *  gr.sig  --  definition of graph interfaces
 *
 *  COPYRIGHT (c) 1997 by Martin Erwig.  See COPYRIGHT file for details.
 *)

(* 
   Hierarchy of Interfaces/Signatures for Directed Graphs


             GRAPH_NODE       GRAPH_EXCEPTIONS
               |                |
               |                |
     [UNLAB]_GRAPH_TYPES        |
               |                |
               |                |
               `-------.--------
                       |
                       |
             [UNLAB]_GRAPH = [UNLAB]_STATIC_GRAPH
                       |
                       |
     [UNLAB]_BOUNDED_GRAPH

*)



(* shared definitions *)

signature GRAPH_NODE =
sig
  type node = int
end


signature GRAPH_EXCEPTIONS =
sig
  exception Node
  exception Edge
  exception NotImplemented
end



(* labeled graphs *)

signature GRAPH_TYPES =
sig
  include GRAPH_NODE
  type ('a,'b) graph
  type 'b out             = ('b * node) list
  type ('a,'b) adj        = 'a * 'b out
  type ('a,'b) context    = 'b out * node * 'a * 'b out
  type ('a,'b) decomp     = ('a,'b) context * ('a,'b) graph
  type ('a,'b) fwd_decomp = ('a,'b) adj * ('a,'b) graph
end


signature GRAPH =
sig
  include GRAPH_EXCEPTIONS
  include GRAPH_TYPES

  val empty       : ('a,'b) graph
  val embed       : ('a,'b) context * ('a,'b) graph -> ('a,'b) graph
  val match       : node * ('a,'b) graph -> ('a,'b) decomp
  val matchFwd    : node * ('a,'b) graph -> ('a,'b) fwd_decomp
  val matchAny    : ('a,'b) graph -> ('a,'b) decomp
  val matchAnyFwd : ('a,'b) graph -> ('a,'b) fwd_decomp
  (*
  val matchOrd    : node * ''b list * ''b list * ('a,''b) graph -> ('a,''b) decomp
  val matchOrdFwd : node * ''b list * ('a,''b) graph -> ('a,''b) fwd_decomp
  *)
  val context     : node * ('a,'b) graph -> ('a,'b) context
  val fwd         : node * ('a,'b) graph -> ('a,'b) adj
  val bwd         : node * ('a,'b) graph -> ('a,'b) adj
  val suc         : node * ('a,'b) graph -> node list
  val pred        : node * ('a,'b) graph -> node list
  val ufold       : (('a,'b) context * 'c -> 'c) -> 'c -> ('a,'b) graph -> 'c
  val gfold       : (('a,'b) context -> node list) -> ('a * 'c -> 'd) -> 
                    ('d * 'c -> 'c) -> 'c -> node list -> ('a,'b) graph -> 'c
  val nodes       : ('a,'b) graph -> node list
  val labNodes    : ('a,'b) graph -> (node * 'a) list
  val noNodes     : ('a,'b) graph -> int
  val isEmpty     : ('a,'b) graph -> bool
  val newNodes    : int -> ('a,'b) graph -> node list
  val mkgr        : 'a list * (node * node * 'b) list -> ('a,'b) graph
  val adj         : ('a,'b) graph -> (node * ('a,'b) adj) list
end



(* unlabeled graphs, i.e., without edge lebels *)

signature UNLAB_GRAPH_TYPES =
sig
  include GRAPH_NODE
  type 'a graph
  type 'a adj        = 'a * node list
  type 'a context    = node list * node * 'a * node list
  type 'a decomp     = 'a context * 'a graph
  type 'a fwd_decomp = 'a adj * 'a graph
end


signature UNLAB_GRAPH =
sig
  include UNLAB_GRAPH_TYPES
  include GRAPH_EXCEPTIONS

  val empty       : 'a graph
  val embed       : 'a context * 'a graph -> 'a graph
  val match       : node * 'a graph -> 'a decomp
  val matchFwd    : node * 'a graph -> 'a fwd_decomp
  val matchAny    : 'a graph -> 'a decomp
  val matchAnyFwd : 'a graph -> 'a fwd_decomp
  val context     : node * 'a graph -> 'a context
  val fwd         : node * 'a graph -> 'a adj
  val bwd         : node * 'a graph -> 'a adj
  val suc         : node * 'a graph -> node list
  val pred        : node * 'a graph -> node list
  val ufold       : ('a context * 'b -> 'b) -> 'b -> 'a graph -> 'b
  val gfold       : ('a context -> node list) -> ('a * 'b -> 'c) -> 
                    ('c * 'b -> 'b) -> 'b -> node list -> 'a graph -> 'b
  val nodes       : 'a graph -> node list
  val labNodes    : 'a graph -> (node * 'a) list
  val noNodes     : 'a graph -> int 
  val isEmpty     : 'a graph -> bool
  val newNodes    : int -> 'a graph -> node list
  val mkgr        : 'a list * (node * node) list -> 'a graph
  val adj         : 'a graph -> (node * 'a adj) list
end
