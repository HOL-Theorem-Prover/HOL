(*---------------------------------------------------------------------------
 * Simple implementation of directed graphs. More efficient ones are 
 * certainly possible, but speed hasn't so far been a problem in the 
 * application (representing the HOL theory graph).  Acyclicity is not 
 * enforced.
 *---------------------------------------------------------------------------*)

structure Graph :> Graph =
struct

open Exception Lib;
fun ERR function message =
    Exception.HOL_ERR{origin_structure = "Theory_graph",
		      origin_function = function,
		      message = message}

(*---------------------------------------------------------------------------
 * Define the type of graphs, parameterized by the required operations.
 *---------------------------------------------------------------------------*)
datatype 'a graph = GRAPH of {node_eq:'a -> 'a -> bool,
                              graph : ('a * 'a list) list}

fun empty eq = GRAPH{node_eq=eq, graph=[]};

fun map f (GRAPH{node_eq, graph}) =
  GRAPH{node_eq=node_eq,
        graph = List.map (fn (n,P) => (f n, List.map f P)) graph};


(* We make no effort to clean out duplicates *)
fun add p (GRAPH{node_eq, graph}) =
  GRAPH{node_eq=node_eq, graph = p::graph}

(*---------------------------------------------------------------------------
 * This doesn't transitively proceed to delete the parents of n from the 
 * graph. If desired, that can be programmed by the client.
 *---------------------------------------------------------------------------*)
fun del n (GRAPH{node_eq, graph}) =
  GRAPH{node_eq=node_eq, 
        graph = List.filter (fn (x,_) => not(node_eq x n)) graph}


fun first P (GRAPH{node_eq, graph}) =
  let fun assc ((p as (nde,_))::rst) = if (P nde) then p else assc rst
        | assc [] = raise ERR "first" "not found"
   in
     assc graph
   end;

fun assoc n (g as GRAPH{node_eq, ...}) = first (node_eq n) g;

fun isin n = Lib.can (assoc n);
fun parents_of n g = #2(assoc n g);

fun insert p f alist =
   let fun ins (a::rst) = if (p a) then f a::rst else a::ins rst
         | ins [] = raise ERR "insert" "not found"
   in  ins alist
   end;

(*---------------------------------------------------------------------------
 * Add a parent to a node. Duplicate parents are union'ed.
 *---------------------------------------------------------------------------*)
fun add_parent (n,newp) (GRAPH{node_eq,graph}) = 
  let fun same (node,_) = node_eq node n
      val union = op_union node_eq 
      fun addp(node,parents) = (node, union [newp] parents)
  in 
    GRAPH{node_eq=node_eq, graph = insert same addp graph}
  end


(*---------------------------------------------------------------------------
 * Computes ancestry of a list of nodes by a depth-first search. The two 
 * arguments to Anc are the "yet-to-see" list and the "seen" list. The
 * original list is included in the result.
 *---------------------------------------------------------------------------*)
fun ancestryl (g as GRAPH{node_eq,...}) L =
 let fun Anc P Q = 
      rev_itlist 
        (fn nde => fn A => if (op_mem node_eq nde A) then A
          else Anc (parents_of nde g handle HOL_ERR _ => []) (nde::A)) P Q
 in
     Anc L []
 end;
   

(*---------------------------------------------------------------------------
 * All nodes in the graph that aren't parents.
 *---------------------------------------------------------------------------*)
fun fringe (GRAPH{node_eq,graph}) =
  let val all_parents = List.map #2 graph
      fun is_parent y = Lib.exists (Lib.op_mem node_eq y) all_parents
  in 
     List.filter (not o is_parent) (List.map #1 graph)
  end;

end; (* Graph *)
