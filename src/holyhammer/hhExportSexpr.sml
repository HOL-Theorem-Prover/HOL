(* ========================================================================= *)
(* FILE          : hhExportSexpr.sml                                         *)
(* DESCRIPTION   : Export HOL4 theories/problems to S-expression format      *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportSexpr :> hhExportSexpr =
struct

open HolKernel boolLib aiLib hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportSexpr"

(* -------------------------------------------------------------------------
   Preparing and analysing the formula
   ------------------------------------------------------------------------- *)

fun th1_prep_tm tm = rename_bvarl escape (list_mk_forall (free_vars_lr tm, tm))
fun th1_prep_thm thm = th1_prep_tm (concl (DISCH_ALL thm))

(* ------------------------------------------------------------------------
   TH1 names
   ------------------------------------------------------------------------ *)

fun th1_var v = fst (dest_var v)
fun th1b_const (thy,name) = escape ("c." ^ thy ^ "." ^ name)
fun th1_const c =
  let val {Name,Thy,Ty} = dest_thy_const c in th1b_const (Thy,Name) end
fun th1_vartype ty = "A" ^ (escape (dest_vartype ty))
fun th1b_tyop (thy,tyop) = escape ("ty." ^ thy ^ "." ^ tyop)
fun th1_tyop ty =
  let val {Args,Thy,Tyop} = dest_thy_type ty in th1b_tyop (Thy,Tyop) end
fun th1b_thm (thy,name) = escape ("thm" ^ "." ^ thy ^ "." ^ name)

(* -------------------------------------------------------------------------
   S-expression names
   ------------------------------------------------------------------------- *)

fun double_quote s = "\"" ^ s ^ "\""
val sexpr_var = double_quote o th1_var
val sexpr_const = double_quote o th1_const
val sexpr_vartype = double_quote o th1_vartype
val sexpr_tyop = double_quote o th1_tyop

val sexprb_const = double_quote o th1b_const
val sexprb_tyop = double_quote o th1b_tyop
val sexprb_thm = double_quote o th1b_thm

(* -------------------------------------------------------------------------
   terms
   ------------------------------------------------------------------------- *)

fun sexpr_type oc ty =
  if is_vartype ty then os oc (sexpr_vartype ty) else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if null Args
      then os oc (sexpr_tyop ty)
      else (os oc "("; os oc (sexpr_tyop ty);
            os oc " "; oiter oc " " sexpr_type Args; os oc ")")
    end

fun sexpr_term oc tm =
  if is_var tm then os oc (sexpr_var tm)
  else if is_const tm then
    let
      val {Thy, Name, Ty} = dest_thy_const tm
      val mgty = type_of (prim_mk_const {Thy = Thy, Name = Name})
      val subst = full_match_type mgty Ty
      val resl = map #residue subst
    in
      if null resl
      then os oc (sexpr_const tm)
      else (os oc "("; os oc (sexpr_const tm); os oc " ";
            oiter oc " " sexpr_type resl; os oc ")")
    end
  else if is_comb tm then
    let val (rator,argl) = strip_comb tm in
      os oc "("; sexpr_term oc rator;
      os oc " "; oiter oc " " sexpr_term argl; os oc ")"
    end
  else if is_abs tm then
    let val (bvar,body) = dest_abs tm in
      os oc "("; os oc "lambda"; os oc " ";
      os oc (sexpr_var bvar); os oc " ";
      sexpr_type oc (type_of bvar); os oc " ";
      sexpr_term oc body; os oc ")"
    end
  else raise ERR "sexpr_term" ""

(* -------------------------------------------------------------------------
   Quantify over polymorphic variables
   ------------------------------------------------------------------------- *)

fun sexpr_tyquant_type oc ty =
  let val tvl = dict_sort Type.compare (type_vars ty) in
    if null tvl then sexpr_type oc ty else
      (
      os oc "(forall_tyvarl_type ";
      os oc "("; oiter oc " " sexpr_type tvl; os oc ")"; os oc " ";
      sexpr_type oc ty; os oc ")"
      )
  end

fun sexpr_tyquant_term oc tm =
  let
    val tyl = map type_of (find_terms is_const tm @ all_vars tm)
    val tvl = dict_sort Type.compare (type_varsl tyl)
  in
    if null tvl then sexpr_term oc tm else
      (
      os oc "("; os oc "forall_tyvarl_term"; os oc " ";
      os oc "("; oiter oc " " sexpr_type tvl; os oc ")"; os oc " ";
      sexpr_term oc tm; os oc ")"
      )
  end

(* -------------------------------------------------------------------------
   Definitions
   ------------------------------------------------------------------------- *)

fun sexpr_tydef oc thy (tyop,arity) =
  (
  os oc "(type_definition ";
  os oc (sexprb_tyop (thy,tyop)); os oc " ";
  os oc (int_to_string arity); osn oc ")"
  )

fun sexpr_constdef oc (thy,name) =
  let val ty = type_of (prim_mk_const {Thy = thy, Name = name}) in
    os oc "(constant_definition"; os oc " ";
    os oc (sexprb_const (thy,name)); os oc " ";
    sexpr_tyquant_type oc ty; osn oc ")"
  end

fun sexpr_thmdef oc thy ((name,thm),role) =
  let val tm = th1_prep_thm thm in
    os oc "("; os oc role; os oc " ";
    os oc (sexprb_thm (thy,name)); os oc " ";
    sexpr_tyquant_term oc tm; osn oc ")"
  end

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

val sexpr_dir = hh_dir ^ "/export_sexpr"

fun sexpr_export thyl =
  let
    val file = sexpr_dir ^ "/theory_order.info"
    val fl = (sexpr_tydef, sexpr_constdef, sexpr_thmdef, sexprb_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err sexpr_dir;
    app (write_thy fl sexpr_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

end (* struct *)
