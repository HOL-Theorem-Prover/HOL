(* ========================================================================  *)
(* FILE          : mlFeature.sml                                             *)
(* DESCRIPTION   : Features for machine learning on terms                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure mlFeature :> mlFeature =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "tttFeature"
 
(* -------------------------------------------------------------------------
   Constants, variables and types
   ------------------------------------------------------------------------- *)

fun string_of_const tm =
  let val {Thy,Name,Ty} = dest_thy_const tm in Name ^ "." ^ Thy ^ ".c" end

fun constfea_of tm =
  map string_of_const (mk_term_set (find_terms is_const tm))

fun string_of_var tm = fst (dest_var tm) ^ ".v"

fun varfea_of tm =
  map string_of_var (mk_term_set (find_terms is_var tm))
      
fun zeroed_type ty =
  if is_vartype ty then "T" else
  let
    val {Args,Thy,Tyop} = dest_thy_type ty
    val s = Tyop ^ "." ^ Thy ^ ".t"
  in
    if null Args 
    then s 
    else "(" ^ s ^ String.concatWith " " (map zeroed_type Args) ^ ")"
  end

fun typefea_of tm =
  let val l = find_terms (fn x => is_const x orelse is_var x) tm in
    map zeroed_type (mk_fast_set Type.compare (map type_of l))
  end

(* -------------------------------------------------------------------------
   Subterms
   ------------------------------------------------------------------------- *)

fun atoms_of tm =
  if is_eq tm andalso type_of (lhs tm) = bool 
    then atoms_of (lhs tm) @ atoms_of (rhs tm)
  else if is_conj tm orelse is_disj tm orelse is_imp_only tm 
    then atoms_of (lhand tm) @ atoms_of (rand tm)
  else if is_neg tm    then atoms_of (rand tm)
  else if is_forall tm then atoms_of (snd (dest_forall tm))
  else if is_exists tm then atoms_of (snd (dest_exists tm))
  else [tm]

fun zeroed_term tm =
  if is_var tm then "A"
  else if is_const tm then string_of_const tm
  else if is_comb tm then
    "(" ^ zeroed_term (rator tm) ^ " " ^ zeroed_term (rand tm) ^ ")"
  else if is_abs tm then
    let val (v,t) = dest_abs tm in
      "(Abs " ^ zeroed_term t ^ ")"
    end
  else raise ERR "zeroed_term" ""

fun subtermfea_of tm =
  let 
    val atoml = atoms_of tm
    val subterml = List.concat (map (find_terms (fn _ => true)) atoml) 
  in
    map zeroed_term (mk_term_set subterml)
  end

(* -------------------------------------------------------------------------
   All features
   ------------------------------------------------------------------------- *)

fun fea_of_term tm =
  if term_size tm > 2000 
  then constfea_of tm 
  else subtermfea_of tm @ constfea_of tm @ varfea_of tm @ typefea_of tm

fun fea_of_goal (asl,w) =
  let
    val asl_sl1 = List.concat (map fea_of_term asl)
    val asl_sl2 = map (fn x => x ^ ".h") asl_sl1
    val w_sl   = map (fn x => x ^ ".w") (fea_of_term w)
  in
    mk_string_set (w_sl @ asl_sl2)
  end

(* -------------------------------------------------------------------------
   Hashing features
   ------------------------------------------------------------------------- *)

fun feahash_of_term tm =
  mk_fast_set Int.compare (map hash_string (fea_of_term tm))

fun feahash_of_goal g = 
  mk_fast_set Int.compare (map hash_string (fea_of_goal g))

(* ------------------------------------------------------------------------
   TFIDF: weight of symbols (power of 6 comes from the neareset neighbor 
   distance)
   ------------------------------------------------------------------------ *)

fun weight_tfidf symsl =
  let
    val syms      = List.concat symsl
    val dict      = count_dict (dempty Int.compare) syms
    val n         = length symsl
    fun f (fea,freq) =
      Math.pow (Math.ln (Real.fromInt n) - Math.ln (Real.fromInt freq), 6.0)
  in
    Redblackmap.map f dict
  end

fun learn_tfidf feavl = weight_tfidf (map snd feavl)




end (* struct *)
