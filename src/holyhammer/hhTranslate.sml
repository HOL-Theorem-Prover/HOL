(* ========================================================================== *)
(* FILE          : hhTranslate.sml                                            *)
(* DESCRIPTION   : HOL to FOL translations                                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(*                     Cezary Kaliszyk, University of Innsbruck               *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure hhTranslate :> hhTranslate =
struct

open HolKernel boolLib tttTools

fun must_pred tm =
  is_forall tm orelse is_exists tm orelse is_conj tm orelse is_disj tm orelse
  is_imp tm orelse is_eq tm orelse is_neg tm

(*----------------------------------------------------------------------------
   FOF Checks
 -----------------------------------------------------------------------------*)

(* Lambda *)
fun contains_lambda tm = 
  if is_var tm orelse is_const tm then false
  else if is_forall tm then
    let val (vl,bod) = strip_forall tm in contains_lambda bod end
  else if is_exists tm then
    let val (vl,bod) = strip_exists tm in contains_lambda bod end
  else if is_comb tm then 
    let val (rator,rand) = dest_comb tm in
      contains_lambda rator orelse contains_lambda rand
    end
  else if is_abs tm then true
  else raise ERR "contains_lambda" ""

(* Prop *)
local
  val (atoml: term list ref) = ref []
  fun atoms tm =
    (
    if is_var tm orelse is_const tm then atoml := tm :: (!atoml)
    else if is_eq tm then
      if type_of (lhs tm) = bool
      then (atoms (lhs tm); atoms (rhs tm))
      else atoml := tm :: (!atoml)
    else if is_conj tm orelse is_disj tm orelse is_imp_only tm then
      (atoms (lhand tm); atoms (rand tm))
    else if is_neg tm      then atoms  (rand tm)
    else if is_forall tm   then binder (dest_forall tm)
    else if is_exists tm   then binder (dest_exists tm)
    else if is_abs tm      then atoml := tm :: (!atoml)
    else if is_comb tm     then atoml := tm :: (!atoml)
    else raise ERR "atoms" ""
    )
  and binder (_,tm) = atoms tm
in 
  fun atoms_of_term tm = (atoml := []; atoms tm; !atoml)
end    
    
fun contains_exall tm =
  if is_var tm orelse is_const tm then false
  else if is_forall tm orelse is_exists tm then true
  else if is_comb tm then 
    let val (rator,rand) = dest_comb tm in
      contains_exall rator orelse contains_exall rand
    end
  else if is_abs tm then 
    let val (v,bod) = dest_abs tm in contains_exall bod end
  else raise ERR "contains_exall" ""

(* Arity *)
local
  val adict = ref (dempty String.compare)
  fun update_adict rator randl =
    let 
      val name = (* tptp_of_constvar (length randl) rator *)
                 term_to_string rator
      val oldl = dfind name (!adict) handle NotFound => []
    in
      adict := dadd name (length randl :: oldl) (!adict)
    end
  fun collect_arity_aux tm =
    if is_var tm orelse is_const tm then ()
    else if is_comb tm then
      let val (rator,randl) = strip_comb tm in
        update_adict rator randl;
        app collect_arity_aux randl
      end
    else if is_abs tm then 
      let val (v,bod) = dest_abs tm in
        update_adict v [];
        collect_arity_aux bod 
      end
    else raise ERR "collect_arity_aux" ""
in
  fun collect_arity tm = 
    let fun f (_,l) = mk_fast_set Int.compare l in
      adict := dempty String.compare; 
      collect_arity_aux tm; 
      Redblackmap.map f (!adict)
    end
end  

fun has_fofarity tm =
  let 
    val adict = collect_arity tm 
    fun f (_,l) = (length l = 1)
    val adict' = Redblackmap.map f adict
  in
    all I (map snd (dlist adict'))
  end

(* Test *) 
fun classify thm =
  let 
    val tm = concl (GEN_ALL (DISCH_ALL thm)) 
    val b1 = not (contains_lambda tm)
    val b2 = not (exists I (map contains_exall (atoms_of_term tm)))
    val b3 = b1 andalso has_fofarity tm
  in
    (b1,b2,b3)
  end

(*----------------------------------------------------------------------------
  Removing predicates arguments.
  ----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------
  Eliminates lambdas. 
  Assumes variables have been renamed a priori to avoid capture.
  ----------------------------------------------------------------------------*)

val bi = ref 0
val fi = ref 0

fun close_term tm = list_mk_forall (free_vars_lr tm, tm)

fun ATOM_CONV conv tm =
  if is_forall tm orelse is_exists tm 
    then QUANT_CONV (ATOM_CONV conv) tm 
  else if is_conj tm orelse is_disj tm orelse is_imp_only tm orelse is_eq tm
    then BINOP_CONV (ATOM_CONV conv) tm else
  if is_neg tm 
    then RAND_CONV (ATOM_CONV conv) tm 
  else conv tm

fun BOOL_LIFT_CONV tm =
  let 
    val subtm = find_term must_pred tm handle _ => raise UNCHANGED
    val fvl = free_vars_lr subtm
    val v = mk_var("b" ^ int_to_string (!bi),
                   type_of (list_mk_abs (fvl,subtm)))
    val _ = incr bi
    val rep = list_mk_comb (v,fvl)
    val eq = close_term (mk_eq (subtm,rep))
    val thm = ASSUME eq
  in
    REWRITE_CONV [thm] tm
  end
  
fun LAMBDA_LIFT_CONV tm =
  let 
    val subtm = find_term is_abs tm handle _ => raise UNCHANGED
    val fvl = free_vars_lr subtm
    val v = mk_var("f" ^ int_to_string (!fi),
                   type_of (list_mk_abs (fvl,subtm)))
    val _ = incr fi 
    val rep = list_mk_comb (v,fvl)                        
    val thm = ASSUME (mk_eq (subtm,rep))
  in
    REWRITE_CONV [thm] tm
  end


(*----------------------------------------------------------------------------
  val term1 = ``!y. P f (!x.y x):bool``;
  val term1 = ``P f (!x.y x):bool``;
  val term2 = ``P f (\x.y x):bool``;
  val term1 = ``!y. P f (!x.y (!z. z y)):bool``;
  val [asl] = hyp (REPEATC (ATOM_CONV BOOL_LIFT_CONV) term1);
  REPEATC (ATOM_CONV BOOL_LIFT_CONV) asl;
  val term = ``(!y. y (∀z. z y)) <=> T``;
  ATOM_CONV BOOL_LIFT_CONV term;
  ----------------------------------------------------------------------------*)

end
