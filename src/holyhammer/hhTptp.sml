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
   Escaping constants , variables and theorems
   ------------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "hhTptp"

val readable_flag = ref false (* used for debugging *)

fun tptp_of_var arity v = 
  if not (!readable_flag) 
  then 
    if arity = 0 
    then fst (dest_var v)
    else fst (dest_var v) ^ "_" ^ int_to_string arity
  else fst (dest_var v)

fun tptp_of_const arity c = 
  let val {Name, Thy, Ty} = dest_thy_const c in
    if not (!readable_flag) 
    then escape 
      ("c" ^ (if arity = 0 then "" else int_to_string arity) ^ 
       "." ^ Thy ^ "." ^ Name)
    else Name
  end

fun tptp_of_constvar arity tm = 
  if is_const tm then tptp_of_const arity tm
  else if is_var tm then tptp_of_var arity tm
  else raise raise ERR "tptp_of_constvar" (term_to_string tm)

fun tptp_of_vartype ty = 
  if not (!readable_flag) 
  then ("A" ^ (escape (dest_vartype ty)))
  else dest_vartype ty

fun tptp_of_tyop ty = 
  let 
    val {Args, Thy, Tyop} = dest_thy_type ty 
  in   
    if not (!readable_flag) 
    then escape ("ty" ^ "." ^ Thy ^ "." ^ Tyop)
    else Tyop
  end

fun tptp_of_thm (name,tm) = 
  if not (!readable_flag) 
  then 
    if can (split_string "Theory.") name 
    then escape ("thm." ^ name) 
    else escape ("reserved." ^ name)
  else name

(* -------------------------------------------------------------------------
   writer shortcuts
   ------------------------------------------------------------------------- *)

fun os oc s = TextIO.output (oc,s)

fun oiter_aux oc sep f l = case l of
    []     => ()
  | [a]    => f oc a
  | a :: m => (f oc a; os oc sep; oiter_aux oc sep f m)

fun oiter oc sep f l = oiter_aux oc sep f l

(* -------------------------------------------------------------------------
   FOF writer
   ------------------------------------------------------------------------- *)

fun write_type oc ty =
  if is_vartype ty then os oc (tptp_of_vartype ty)
  else
    let 
      val {Args, Thy, Tyop} = dest_thy_type ty 
      val tyops = tptp_of_tyop ty
    in
      os oc tyops;
      if null Args then () 
      else (os oc "("; oiter oc "," write_type Args; os oc ")")
    end

fun write_term oc tm =
  let 
    val (rator,argl) = strip_comb tm 
  in
    os oc "s("; write_type oc (type_of tm); os oc ","; 
    os oc (tptp_of_constvar (length argl) rator);
    if null argl then ()
    else (os oc "("; oiter oc "," write_term argl; os oc ")");
    os oc ")"
  end

fun write_pred oc tm =
  if is_forall tm then
    let val (vl,bod) = strip_forall tm in
      os oc "![";
      oiter oc ", " (fn x => (fn v => os x (tptp_of_var 0 v))) vl;
      os oc "]: ";
      write_pred oc bod
    end
  else if is_exists tm then
    let val (vl,bod) = strip_exists tm in
      os oc "?["; 
      oiter oc ", " (fn x => (fn v => os x (tptp_of_var 0 v))) vl;
      os oc "]: ";
      write_pred oc bod
    end
  else if is_conj tm then 
    let val (l,r) = dest_conj tm in
      os oc "("; 
      write_pred oc l; os oc " & "; write_pred oc r; 
      os oc ")"
    end
  else if is_disj tm then 
    let val (l,r) = dest_disj tm in
      os oc "("; 
      write_pred oc l; os oc " | "; write_pred oc r; 
      os oc ")"
    end      
  else if is_imp_only tm then 
    let val (l,r) = dest_imp tm in
      os oc "("; 
      write_pred oc l; os oc " => "; write_pred oc r; 
      os oc ")"
    end 
  else if is_neg tm then
    (os oc "~ ("; write_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then 
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r 
      (* probably an optimization: I would replace it by type_of l = bool *)
      then
        (os oc "("; write_pred oc l; os oc " <=> "; write_pred oc r; os oc ")")
      else
        (write_term oc l; os oc " = "; write_term oc r)
    end
  else
    (os oc "p("; write_term oc tm; os oc ")");;

fun type_vars_in_term tm = 
  type_varsl (map type_of (find_terms is_const tm @ all_vars tm))

fun write_formula oc tm =
  let val tvl = type_vars_in_term tm in
    if null tvl then ()
    else (os oc "!["; oiter oc "," write_type tvl; os oc "]: ");
    write_pred oc tm
  end

fun write_ax oc (name,tm) =
  (
  if !readable_flag then os oc "% " else ();
  os oc ("fof(" ^ tptp_of_thm (name,tm) ^ ", axiom, ");
  write_formula oc tm;
  os oc ").\n"
  )

fun write_cj oc cj =
  (
  if !readable_flag then os oc "% " else ();
  os oc "fof(conjecture, conjecture, ";
  write_formula oc cj;
  os oc ").\n"
  )

(* Warning:
  Use list_mk_forall and rename_bvarl before using this function to guarantee
  that all variables have different names 
*)

fun write_tptp dir axl cj =
  let
    val _ = mkDir_err dir
    val _ = remove_file (dir ^ "/status")
    val _ = remove_file (dir ^ "/out")
    val _ = remove_file (dir ^ "/error")
    val _ = remove_file (dir ^ "/out1")
    val oc = TextIO.openOut (dir ^ "/atp_in")
  in
    ((readable_flag := false; app (write_ax oc) axl; write_cj oc cj)
    handle Interrupt => ());
    TextIO.closeOut oc
  end


end (* struct *)
