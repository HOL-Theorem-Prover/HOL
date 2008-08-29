structure patricia_castsSyntax :> patricia_castsSyntax =
struct

(* interactive use:
  app load ["pred_setSyntax", "wordsSyntax", "patriciaSyntax",
            "patricia_castsTheory"];
*)

open Abbrev HolKernel pred_setSyntax wordsSyntax patriciaSyntax
     patricia_castsTheory;

(* ------------------------------------------------------------------------- *)

fun mk_word_ptree_type (aty, bty) =
  Type.mk_thy_type{Tyop="word_ptree", Thy="patricia_casts", Args = [aty, bty]};

fun dest_word_ptree_type ty =
  case total dest_thy_type ty of
    SOME {Tyop="word_ptree",Thy="patricia_casts",Args=[aty, bty]} => (aty, bty)
  | _ => raise ERR "dest_word_ptree_type"
                   "not an instance of ('a,'b) word_ptree";

val is_word_ptree_type = Lib.can dest_word_ptree_type;

(* ......................................................................... *)

fun mk_pat_const s = prim_mk_const{Name = s, Thy = "patricia_casts"};

val the_ptree_tm        = mk_pat_const "THE_PTREE"
val some_ptree_tm       = mk_pat_const "SOME_PTREE"
val wordempty_tm        = mk_pat_const "WordEmpty";

val peekw_tm            = mk_pat_const "PEEKw"
val findw_tm            = mk_pat_const "FINDw"
val addw_tm             = mk_pat_const "ADDw"
val add_listw_tm        = mk_pat_const "ADD_LISTw"
val removew_tm          = mk_pat_const "REMOVEw"
val traversew_tm        = mk_pat_const "TRAVERSEw"
val keysw_tm            = mk_pat_const "KEYSw"
val transformw_tm       = mk_pat_const "TRANSFORMw"
val every_leafw_tm      = mk_pat_const "EVERY_LEAFw"
val exists_leafw_tm     = mk_pat_const "EXISTS_LEAFw"
val sizew_tm            = mk_pat_const "SIZEw"
val depthw_tm           = mk_pat_const "DEPTHw"
val in_ptreew_tm        = mk_pat_const "IN_PTREEw"
val insert_ptreew_tm    = mk_pat_const "INSERT_PTREEw"
val ptree_of_wordset_tm = mk_pat_const "PTREE_OF_WORDSET"
val wordset_of_ptree_tm = mk_pat_const "WORDSET_OF_PTREE";

(* ......................................................................... *)

val peeks_tm              = mk_pat_const "PEEKs"
val finds_tm              = mk_pat_const "FINDs"
val adds_tm               = mk_pat_const "ADDs"
val add_lists_tm          = mk_pat_const "ADD_LISTs"
val removes_tm            = mk_pat_const "REMOVEs"
val traverses_tm          = mk_pat_const "TRAVERSEs"
val keyss_tm              = mk_pat_const "KEYSs"
val in_ptrees_tm          = mk_pat_const "IN_PTREEs"
val insert_ptrees_tm      = mk_pat_const "INSERT_PTREEs"
val ptree_of_stringset_tm = mk_pat_const "PTREE_OF_STRINGSET"
val stringset_of_ptree_tm = mk_pat_const "STRINGSET_OF_PTREE";

(* ......................................................................... *)

fun mk_wordempty(aty, bty) =
  inst[alpha |-> aty, beta |-> bty] wordempty_tm
  handle HOL_ERR _ => raise ERR "mk_wordempty" "";

fun mk_the_ptree t =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  mk_comb(inst[alpha |-> tyb, beta |-> tya] the_ptree_tm,t)
end handle HOL_ERR _ => raise ERR "mk_the_ptree" "";

fun mk_some_ptree(ty,t) =
  mk_comb(inst[alpha |-> ty,
                beta |-> dest_ptree_type (type_of t)] some_ptree_tm,t)
  handle HOL_ERR _ => raise ERR "mk_some_ptree" "";

fun mk_peekw(t,k) =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  list_mk_comb(inst[alpha |-> tya, beta |-> tyb] peekw_tm,[t,k])
end handle HOL_ERR _ => raise ERR "mk_peekw" "";

fun mk_findw(t,k) =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  list_mk_comb(inst[alpha |-> tyb, beta |-> tya] findw_tm,[t,k])
end handle HOL_ERR _ => raise ERR "mk_findw" "";

fun mk_addw(t,x) =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  list_mk_comb(inst[alpha |-> tya, beta |-> tyb] addw_tm,[t,x])
end handle HOL_ERR _ => raise ERR "mk_addw" "";

fun mk_add_listw(t,l) =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  list_mk_comb(inst[alpha |-> tya, beta |-> tyb] add_listw_tm,[t,l])
end handle HOL_ERR _ => raise ERR "mk_add_listw" "";

fun mk_removew(t,k) =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  list_mk_comb(inst[alpha |-> tya, beta |-> tyb] removew_tm,[t,k])
end handle HOL_ERR _ => raise ERR "mk_removew" "";

fun mk_traversew t =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  mk_comb(inst[alpha |-> tya, beta |-> tyb] traversew_tm,t)
end handle HOL_ERR _ => raise ERR "mk_traversew" "";

fun mk_keysw t =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  mk_comb(inst[alpha |-> tya, beta |-> tyb] keysw_tm,t)
end handle HOL_ERR _ => raise ERR "mk_keysw" "";

fun mk_transformw(f,t) =
let val (typb, typa) = dom_rng (type_of f)
    val tyc = fst (dest_word_ptree_type (type_of t))
in
  list_mk_comb(inst[alpha |-> typa, beta |-> typb,
                    gamma |-> tyc] transformw_tm,[f,t])
end handle HOL_ERR _ => raise ERR "mk_transformw" "";

fun mk_every_leafw(p,t) =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  list_mk_comb(inst[alpha |-> tya, beta |-> tyb] every_leafw_tm,[p,t])
end handle HOL_ERR _ => raise ERR "mk_every_leafw" "";

fun mk_exists_leafw(p,t) =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  list_mk_comb(inst[alpha |-> tya, beta |-> tyb] exists_leafw_tm,[p,t])
end handle HOL_ERR _ => raise ERR "mk_exists_leafw" "";

fun mk_sizew t =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  mk_comb(inst[alpha |-> tya, beta |-> tyb] sizew_tm,t)
end handle HOL_ERR _ => raise ERR "mk_sizew" "";

fun mk_depthw t =
let val (tya,tyb) = dest_word_ptree_type (type_of t) in
  mk_comb(inst[alpha |-> tya, beta |-> tyb] depthw_tm,t)
end handle HOL_ERR _ => raise ERR "mk_depthw" "";

fun mk_in_ptreew(k,t) =
  list_mk_comb(inst[alpha |-> dest_word_type (type_of k)] in_ptreew_tm,[k,t])
  handle HOL_ERR _ => raise ERR "mk_in_ptreew" "";

fun mk_insert_ptreew(k,t) =
  list_mk_comb
    (inst[alpha |-> dest_word_type (type_of k)] insert_ptreew_tm,[k,t])
  handle HOL_ERR _ => raise ERR "mk_insert_ptreew" "";

fun mk_ptree_of_wordset s =
let val typ = dest_word_type (dest_set_type (type_of s)) in
  mk_comb(inst [alpha |-> typ] ptree_of_wordset_tm,s)
end handle HOL_ERR _ => raise ERR "mk_ptree_of_wordset" "";

fun mk_wordset_of_ptree t =
let val typ = fst (dest_word_ptree_type (type_of t)) in
  mk_comb(inst [alpha |-> typ] wordset_of_ptree_tm,t)
end handle HOL_ERR _ => raise ERR "mk_wordset_of_ptree" "";

(* ......................................................................... *)

fun mk_peeks(t,k) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] peeks_tm,[t,k])
  handle HOL_ERR _ => raise ERR "mk_peeks" "";

fun mk_finds(t,k) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] finds_tm,[t,k])
  handle HOL_ERR _ => raise ERR "mk_finds" "";

fun mk_adds(t,x) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] adds_tm, [t,x])
  handle HOL_ERR _ => raise ERR "mk_adds" "";

fun mk_add_lists(t,l) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] add_lists_tm,[t,l])
  handle HOL_ERR _ => raise ERR "mk_add_lists" "";

fun mk_removes(t,k) =
  list_mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] removes_tm,[t,k])
  handle HOL_ERR _ => raise ERR "mk_removes" "";

fun mk_traverses t =
  mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] traverses_tm,t)
  handle HOL_ERR _ => raise ERR "mk_traverses" "";

fun mk_keyss t =
  mk_comb(inst[alpha |-> dest_ptree_type (type_of t)] keyss_tm,t)
  handle HOL_ERR _ => raise ERR "mk_keyss" "";

fun mk_in_ptrees(k,t) =
  list_mk_comb(in_ptrees_tm,[k,t])
  handle HOL_ERR _ => raise ERR "mk_in_ptrees" "";

fun mk_insert_ptrees(k,t) =
  list_mk_comb (insert_ptrees_tm,[k,t])
  handle HOL_ERR _ => raise ERR "mk_insert_ptrees" "";

fun mk_ptree_of_stringset s =
  mk_comb(ptree_of_stringset_tm,s)
  handle HOL_ERR _ => raise ERR "mk_ptree_of_stringset" "";

fun mk_stringset_of_ptree s =
  mk_comb(stringset_of_ptree_tm,s)
  handle HOL_ERR _ => raise ERR "mk_stringset_of_ptree" "";

(* ......................................................................... *)

val dest_the_ptree     = dest_monop the_ptree_tm (ERR "dest_the_ptree" "")
val dest_some_ptree    = dest_monop some_ptree_tm (ERR "dest_some_ptree" "")
val dest_wordempty     = dest_monop wordempty_tm (ERR "dest_wordempty" "")
val dest_peekw         = dest_binop peekw_tm (ERR "dest_peekw" "")
val dest_findw         = dest_binop findw_tm (ERR "dest_findw" "")
val dest_addw          = dest_binop addw_tm (ERR "dest_addw" "")
val dest_add_listw     = dest_binop add_listw_tm (ERR "dest_add_listw" "")
val dest_removew       = dest_binop removew_tm (ERR "dest_removew" "")
val dest_traversew     = dest_monop traversew_tm (ERR "dest_traversew" "")
val dest_keysw         = dest_monop keysw_tm (ERR "dest_keysw" "")
val dest_transformw    = dest_binop transformw_tm (ERR "dest_transformw" "")
val dest_every_leafw   = dest_binop every_leafw_tm (ERR "dest_every_leafw" "")
val dest_exists_leafw  = dest_binop exists_leafw_tm (ERR "dest_exists_leafw" "")
val dest_sizew         = dest_monop sizew_tm (ERR "dest_sizew" "")
val dest_depthw        = dest_monop depthw_tm (ERR "dest_depthw" "")
val dest_in_ptreew     = dest_binop in_ptreew_tm (ERR "dest_in_ptreew" "")
val dest_insert_ptreew = dest_binop insert_ptreew_tm
                           (ERR "dest_insert_ptreew" "");

val dest_ptree_of_wordset =
   dest_monop ptree_of_wordset_tm (ERR "dest_ptree_of_numset" "");

val dest_wordset_of_ptree =
   dest_monop wordset_of_ptree_tm (ERR "dest_numset_of_ptree" "");

(* ......................................................................... *)

val dest_peeks         = dest_binop peeks_tm (ERR "dest_peeks" "")
val dest_finds         = dest_binop finds_tm (ERR "dest_finds" "")
val dest_adds          = dest_binop adds_tm (ERR "dest_adds" "")
val dest_add_lists     = dest_binop add_lists_tm (ERR "dest_add_lists" "")
val dest_removes       = dest_binop removes_tm (ERR "dest_removes" "")
val dest_traverses     = dest_monop traverses_tm (ERR "dest_traverses" "")
val dest_keyss         = dest_monop keyss_tm (ERR "dest_keyss" "")
val dest_in_ptrees     = dest_binop in_ptrees_tm (ERR "dest_in_ptrees" "")
val dest_insert_ptrees = dest_binop insert_ptrees_tm
                           (ERR "dest_insert_ptrees" "");

val dest_ptree_of_stringset =
   dest_monop ptree_of_stringset_tm (ERR "dest_ptree_of_numset" "");

val dest_stringset_of_ptree =
   dest_monop stringset_of_ptree_tm (ERR "dest_numset_of_ptree" "");

(* ......................................................................... *)

val is_the_ptree        = can dest_the_ptree
val is_some_ptree       = can dest_some_ptree
val is_wordempty        = can dest_wordempty
val is_peekw            = can dest_peekw
val is_findw            = can dest_findw
val is_addw             = can dest_addw
val is_add_listw        = can dest_add_listw
val is_removew          = can dest_removew
val is_traversew        = can dest_traversew
val is_keysw            = can dest_keysw
val is_transformw       = can dest_transformw
val is_every_leafw      = can dest_every_leafw
val is_exists_leafw     = can dest_exists_leafw
val is_sizew            = can dest_sizew
val is_depthw           = can dest_depthw
val is_in_ptreew        = can dest_in_ptreew
val is_insert_ptreew    = can dest_insert_ptreew
val is_ptree_of_wordset = can dest_ptree_of_wordset
val is_wordset_of_ptree = can dest_wordset_of_ptree;

(* ......................................................................... *)

val is_peeks            = can dest_peeks
val is_finds            = can dest_finds
val is_adds             = can dest_adds
val is_add_lists        = can dest_add_lists
val is_removes          = can dest_removes
val is_traverses        = can dest_traverses
val is_keyss            = can dest_keyss
val is_in_ptrees        = can dest_in_ptrees
val is_insert_ptrees    = can dest_insert_ptrees
val is_ptree_of_stringset = can dest_ptree_of_stringset
val is_stringset_of_ptree = can dest_stringset_of_ptree;

end
