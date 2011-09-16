structure treeSyntax :> treeSyntax =
struct

(*
quietdec := true;
loadPath := (Globals.HOLDIR ^ "/examples/separationLogic/src") ::
            !loadPath;
show_assums := true;
*)

open HolKernel Parse boolLib finite_mapTheory
open treeTheory separationLogicSyntax;

(*
quietdec := false;
*)

fun tree_mk_const n =
   prim_mk_const {Name = n, Thy = "tree"}

val node_term = tree_mk_const "node";
val dest_node = strip_comb_2 node_term
val is_node = can dest_node

val leaf_term = tree_mk_const "leaf";
fun is_leaf t = same_const t leaf_term

end
