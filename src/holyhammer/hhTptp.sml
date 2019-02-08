(* ========================================================================= *)
(* FILE          : hhTptp.sml                                                *)
(* DESCRIPTION   : TPTP writer for essentially first-order HOL formulas      *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhTptp :> hhTptp =
struct

open HolKernel boolLib aiLib hhTranslate

(* -------------------------------------------------------------------------
   Writer shortcuts
   ------------------------------------------------------------------------- *)

fun os oc s = TextIO.output (oc,s)

fun oiter_aux oc sep f l = case l of
    []     => ()
  | [a]    => f oc a
  | a :: m => (f oc a; os oc sep; oiter_aux oc sep f m)

fun oiter oc sep f l = oiter_aux oc sep f l

(* -------------------------------------------------------------------------
   Escaping constants, variables and theorems
   ------------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "hhTptp"

(* Variables are escaped at the begining of the translation
   by rename_bvarl. There is no need to escape them again here. *)
fun tptp_of_var arity v =
  fst (dest_var v) ^ "_" ^ int_to_string arity

fun tptp_of_const arity c =
  let val {Name, Thy, Ty} = dest_thy_const c in
    escape ("c" ^ int_to_string arity ^ "." ^ Thy ^ "." ^ Name)
  end

fun tptp_of_constvar arity tm =
  if is_const tm then tptp_of_const arity tm
  else if is_var tm then tptp_of_var arity tm
  else raise raise ERR "tptp_of_constvar" ""

fun tptp_of_vartype ty = "A" ^ (escape (dest_vartype ty))

fun tptp_of_tyop ty =
  let val {Args, Thy, Tyop} = dest_thy_type ty in
    escape ("ty" ^ "." ^ Thy ^ "." ^ Tyop)
  end

fun tptp_of_thm (name,tm) =
  if can (split_string "Theory.") name
  then escape ("thm." ^ name)
  else escape ("reserved." ^ name)

(* -------------------------------------------------------------------------
   FOF writer
   ------------------------------------------------------------------------- *)

fun write_type oc ty =
  if is_vartype ty then os oc (tptp_of_vartype ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = tptp_of_tyop ty
    in
      os oc tyops;
      if null Args then ()
      else (os oc "("; oiter oc "," write_type Args; os oc ")")
    end

fun write_term oc tm =
  let val (rator,argl) = strip_comb tm in
    os oc "s("; write_type oc (type_of tm); os oc ",";
    os oc (tptp_of_constvar (length argl) rator);
    if null argl then ()
    else (os oc "("; oiter oc "," write_term argl; os oc ")");
    os oc ")"
  end

fun write_pred oc tm =
  if is_forall tm then write_quant oc "!" (strip_forall tm)
  else if is_exists tm then write_quant oc "?" (strip_exists tm)
  else if is_conj tm then write_binop oc "&" (dest_conj tm)
  else if is_disj tm then write_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then write_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "~ ("; write_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r (* optimization *)
      then write_binop oc "<=>" (l,r)
      else (write_term oc l; os oc " = "; write_term oc r)
    end
  else (os oc "p("; write_term oc tm; os oc ")")
and write_binop oc s (l,r) =
  (os oc "("; write_pred oc l; os oc (" " ^ s ^ " "); 
   write_pred oc r; os oc ")")
and write_quant oc s (vl,bod) =
  (os oc s; os oc "[";
   oiter oc ", " (fn x => (fn v => os x (tptp_of_var 0 v))) vl;
   os oc "]: "; write_pred oc bod)

fun type_vars_in_term tm =
  type_varsl (map type_of (find_terms is_const tm @ all_vars tm))

fun write_formula oc tm =
  let val tvl = type_vars_in_term tm in
    if null tvl then ()
    else (os oc "!["; oiter oc "," write_type tvl; os oc "]: ");
    write_pred oc tm
  end

fun write_ax oc (name,tm) =
  (os oc ("fof(" ^ tptp_of_thm (name,tm) ^ ",axiom,");
   write_formula oc tm; os oc ").\n")

fun write_cj oc (name,cj) =
  (os oc "fof(" ^ name ^ ",conjecture,"; write_formula oc cj; os oc ").\n")

fun write_tptp_file file axl cj =
  let val oc = TextIO.openOut file in
    (app (write_ax oc) axl; write_cj oc ("conjecture",cj))
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt);    
    TextIO.closeOut oc
  end

fun write_tptp dir axl cj =
  let
    val _ = mkDir_err dir
    fun f x = remove_file (dir ^ "/" ^ x)
    val _ = app f ["status","out","error","out1"]
  in
    write_tptp_file (dir ^ "/atp_in") axl cj
  end


end (* struct *)
