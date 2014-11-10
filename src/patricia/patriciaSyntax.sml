structure patriciaSyntax :> patriciaSyntax =
struct

open Abbrev HolKernel patriciaTheory;

val ERR = Feedback.mk_HOL_ERR "patriciaSyntax"

(* ------------------------------------------------------------------------- *)

fun mk_ptree_type pty =
  Type.mk_thy_type{Tyop="ptree", Thy="patricia", Args = [pty]};

fun dest_ptree_type ty =
  case total dest_thy_type ty
   of SOME {Tyop="ptree",Thy="patricia",Args=[pty]} => pty
    | _ => raise ERR "dest_ptree_type" "not an instance of 'a ptree";

val is_ptree_type = Lib.can dest_ptree_type;

fun mk_pat_const s = prim_mk_const{Name = s, Thy = "patricia"};

val empty_tm           = mk_pat_const "Empty";
val leaf_tm            = mk_pat_const "Leaf";
val branch_tm          = mk_pat_const "Branch";
val peek_tm            = mk_pat_const "PEEK";
val find_tm            = mk_pat_const "FIND";
val add_tm             = mk_pat_const "ADD";
val add_list_tm        = mk_pat_const "ADD_LIST";
val remove_tm          = mk_pat_const "REMOVE";
val traverse_tm        = mk_pat_const "TRAVERSE";
val keys_tm            = mk_pat_const "KEYS";
val transform_tm       = mk_pat_const "TRANSFORM";
val every_leaf_tm      = mk_pat_const "EVERY_LEAF";
val exists_leaf_tm     = mk_pat_const "EXISTS_LEAF";
val size_tm            = mk_pat_const "SIZE";
val depth_tm           = mk_pat_const "DEPTH";
val is_ptree_tm        = mk_pat_const "IS_PTREE";
val in_ptree_tm        = mk_pat_const "IN_PTREE";
val insert_ptree_tm    = mk_pat_const "INSERT_PTREE";
val branching_bit_tm   = mk_pat_const "BRANCHING_BIT";
val ptree_of_numset_tm = mk_pat_const "PTREE_OF_NUMSET";
val numset_of_ptree_tm = mk_pat_const "NUMSET_OF_PTREE";

fun mk_empty ty =
  inst[alpha |-> ty] empty_tm
  handle HOL_ERR _ => raise ERR "mk_empty" "";

fun mk_leaf(k,d) =
  list_mk_comb(inst[alpha |-> type_of d] leaf_tm,[k,d])
  handle HOL_ERR _ => raise ERR "mk_leaf" "";

fun mk_branch(p,m,l,r) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of l)] branch_tm,[p,m,l,r])
  handle HOL_ERR _ => raise ERR "mk_branch" "";

fun mk_peek(t,k) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] peek_tm,[t,k])
  handle HOL_ERR _ => raise ERR "mk_peek" "";

fun mk_find(t,k) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] find_tm,[t,k])
  handle HOL_ERR _ => raise ERR "mk_find" "";

fun mk_add(t,x) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] add_tm, [t,x])
  handle HOL_ERR _ => raise ERR "mk_add" "";

fun mk_add_list(t,l) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] add_list_tm,[t,l])
  handle HOL_ERR _ => raise ERR "mk_add_list" "";

fun mk_remove(t,k) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] remove_tm,[t,k])
  handle HOL_ERR _ => raise ERR "mk_remove" "";

fun mk_traverse t =
  mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] traverse_tm,t)
  handle HOL_ERR _ => raise ERR "mk_traverse" "";

fun mk_keys t =
  mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] keys_tm,t)
  handle HOL_ERR _ => raise ERR "mk_keys" "";

fun mk_transform(f,t) =
  let val (typb, typa) = dom_rng (type_of f) in
    list_mk_comb(inst[alpha |-> typa, beta |-> typb] transform_tm,[f,t])
  end handle HOL_ERR _ => raise ERR "mk_transform" "";

fun mk_every_leaf(p,t) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] every_leaf_tm,[p,t])
  handle HOL_ERR _ => raise ERR "mk_every_leaf" "";

fun mk_exists_leaf(p,t) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] exists_leaf_tm,[p,t])
  handle HOL_ERR _ => raise ERR "mk_exists_leaf" "";

fun mk_size t =
  mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] size_tm,t)
  handle HOL_ERR _ => raise ERR "mk_size" "";

fun mk_depth t =
  mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] depth_tm,t)
  handle HOL_ERR _ => raise ERR "mk_depth" "";

fun mk_is_ptree t =
  mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] is_ptree_tm,t)
  handle HOL_ERR _ => raise ERR "mk_is_ptree" "";

fun mk_in_ptree(k,t) =
  list_mk_comb(in_ptree_tm,[k,t])
  handle HOL_ERR _ => raise ERR "mk_in_ptree" "";

fun mk_insert_ptree(k,t) =
  list_mk_comb (insert_ptree_tm,[k,t])
  handle HOL_ERR _ => raise ERR "mk_insert_ptree" "";

fun mk_branching_bit(m,n) =
  list_mk_comb (branching_bit_tm,[m,n])
  handle HOL_ERR _ => raise ERR "mk_branching_bit" "";

fun mk_ptree_of_numset(t,s) =
  list_mk_comb
    (inst[alpha |-> dest_ptree_type (type_of t)] ptree_of_numset_tm,[t,s])
  handle HOL_ERR _ => raise ERR "mk_ptree_of_numset" "";

fun mk_numset_of_ptree s =
  mk_comb(numset_of_ptree_tm,s)
  handle HOL_ERR _ => raise ERR "mk_numset_of_ptree" "";

fun dest_quadop c e tm =
  case with_exn strip_comb tm e of
    (t,[t1,t2,t3,t4]) => if same_const t c then (t1,t2,t3,t4) else raise e
  | _ => raise e;

val dest_leaf         = dest_binop leaf_tm (ERR "dest_leaf" "");
val dest_branch       = dest_quadop branch_tm (ERR "dest_branch" "");
val dest_peek         = dest_binop peek_tm (ERR "dest_peek" "");
val dest_find         = dest_binop find_tm (ERR "dest_find" "");
val dest_add          = dest_binop add_tm (ERR "dest_add" "");
val dest_add_list     = dest_binop add_list_tm (ERR "dest_add_list" "");
val dest_remove       = dest_binop remove_tm (ERR "dest_remove" "");
val dest_traverse     = dest_monop traverse_tm (ERR "dest_traverse" "");
val dest_keys         = dest_monop keys_tm (ERR "dest_keys" "");
val dest_transform    = dest_binop transform_tm (ERR "dest_transform" "");
val dest_every_leaf   = dest_binop every_leaf_tm (ERR "dest_every_leaf" "");
val dest_exists_leaf  = dest_binop exists_leaf_tm (ERR "dest_exists_leaf" "");
val dest_size         = dest_monop size_tm (ERR "dest_size" "");
val dest_depth        = dest_monop depth_tm (ERR "dest_depth" "");
val dest_is_ptree     = dest_monop is_ptree_tm (ERR "dest_is_ptree" "");
val dest_in_ptree     = dest_binop in_ptree_tm (ERR "dest_in_ptree" "");
val dest_insert_ptree = dest_binop insert_ptree_tm (ERR "dest_insert_ptree" "");

val dest_branching_bit =
  dest_binop branching_bit_tm (ERR "dest_branching_bit" "");

val dest_ptree_of_numset =
   dest_binop ptree_of_numset_tm (ERR "dest_ptree_of_numset" "");

val dest_numset_of_ptree =
   dest_monop numset_of_ptree_tm (ERR "dest_numset_of_ptree" "");

val is_empty           = same_const empty_tm
val is_leaf            = can dest_leaf;
val is_branch          = can dest_branch;
val is_peek            = can dest_peek;
val is_find            = can dest_find;
val is_add             = can dest_add;
val is_add_list        = can dest_add_list;
val is_remove          = can dest_remove;
val is_traverse        = can dest_traverse;
val is_keys            = can dest_keys;
val is_transform       = can dest_transform;
val is_every_leaf      = can dest_every_leaf;
val is_exists_leaf     = can dest_exists_leaf;
val is_size            = can dest_size;
val is_depth           = can dest_depth;
val is_is_ptree        = can dest_is_ptree;
val is_in_ptree        = can dest_in_ptree;
val is_insert_ptree    = can dest_insert_ptree;
val is_branching_bit   = can dest_branching_bit;
val is_ptree_of_numset = can dest_ptree_of_numset;
val is_numset_of_ptree = can dest_numset_of_ptree;

end
