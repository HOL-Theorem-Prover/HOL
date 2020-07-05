(* ===================================================================== *)
(* FILE          : hhExportSexpr.sml                                     *)
(* DESCRIPTION   : Export HOL4 theories in a s-expression format         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2018                                                  *)
(* ===================================================================== *)

structure hhExportSexpr :> hhExportSexpr =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate holyHammer

val ERR = mk_HOL_ERR "hhExportSexpr"

(* -------------------------------------------------------------------------
   Tools
   ------------------------------------------------------------------------- *)

fun endline_to_space x = case x of #"\n" => #" " | a => a

fun rm_endline x = implode (map endline_to_space (explode x))

fun type_vars_in_term tm =
  type_varsl (map type_of (find_terms is_const tm @ all_vars tm))

(* -------------------------------------------------------------------------
   Writer shortcuts
   ------------------------------------------------------------------------- *)

fun os oc s = TextIO.output (oc,s)

fun osn oc s = TextIO.output (oc,s ^ "\n")

fun oiter_aux oc sep f l = case l of
    []     => ()
  | [a]    => f oc a
  | a :: m => (f oc a; os oc sep; oiter_aux oc sep f m)

fun oiter oc sep f l = oiter_aux oc sep f l

(* -------------------------------------------------------------------------
   Preparing and analysing the formula
   ------------------------------------------------------------------------- *)

fun prep_tm tm = rename_bvarl escape (list_mk_forall (free_vars_lr tm, tm))

fun full_match_type t1 t2 =
  let
    val (sub1,al) = raw_match_type t1 t2 ([],[])
    fun id_sub a = {redex = a, residue = a}
    val sub2 = map id_sub al
    fun cmp (a,b) = Type.compare (#redex a, #redex b)
  in
    dict_sort cmp (sub1 @ sub2)
  end

fun typearg_of_const tm =
  let
    val {Thy, Name, Ty} = dest_thy_const tm
    val mgty = type_of (prim_mk_const {Thy = Thy, Name = Name})
    val subst = full_match_type mgty Ty
  in
    map #residue subst
  end

(* -------------------------------------------------------------------------
   thf escaping : variables escaped by prep_tm
   ------------------------------------------------------------------------- *)

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
   S-expression escaping
   Double quotes needed because lisp is not case senstive.
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
   S-expressions terms
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
   S-expressions definitions
   ------------------------------------------------------------------------- *)

fun sexpr_tydef oc thy (tyop,arity) =
  (
  os oc "(type_definition ";
  os oc (sexprb_tyop (thy,tyop)); os oc " ";
  os oc (int_to_string arity); os oc ")\n"
  )

fun sexpr_tyquant_type oc ty =
  let val tvl = dict_sort Type.compare (type_vars ty) in
    if null tvl
    then sexpr_type oc ty
    else
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
    if null tvl
    then sexpr_term oc tm
    else
      (
      os oc "("; os oc "forall_tyvarl_term"; os oc " ";
      os oc "("; oiter oc " " sexpr_type tvl; os oc ")"; os oc " ";
      sexpr_term oc tm; os oc ")"
      )
  end

(* most general type expected *)
fun sexpr_constdef oc thy (name,ty) =
  (
  osn oc ("; c." ^ thy ^ "." ^ name ^ ": " ^ rm_endline (type_to_string ty));
  os oc "("; os oc "constant_definition"; os oc " ";
  os oc (sexprb_const (thy,name)); os oc " ";
  sexpr_tyquant_type oc ty; os oc ")\n"
  )

fun sexpr_thmdef oc thy ((name,thm),role) =
  let val tm = prep_tm (concl (DISCH_ALL thm)) in
    osn oc ("# " ^ thy ^ "." ^ name ^ ": " ^ rm_endline (term_to_string tm));
    os oc "("; os oc role; os oc " ";
    os oc (sexprb_thm (thy,name)); os oc " ";
    sexpr_tyquant_term oc tm; os oc ")\n"
  end

(* -------------------------------------------------------------------------
   Exporting theories using one of the format defined above.
   ------------------------------------------------------------------------- *)

val hh_dir = HOLDIR ^ "/src/holyhammer"
val sexpr_dir = hh_dir ^ "/export_sexpr"

(* -------------------------------------------------------------------------
   Standard export
   ------------------------------------------------------------------------- *)

fun write_dep ocdep fb_thm thy ((name,thm),role) =
  (
  osn ocdep (fb_thm (thy,name));
  (if role = "conjecture" then
    let
      val (b,depl1) = intactdep_of_thm thm
      val depl2 = map (split_string "Theory.") depl1
      val depl3 = map fb_thm depl2
    in
      osn ocdep role;
      osn ocdep (if b then  "intact" else "broken");
      oiter ocdep " " os depl3; os ocdep "\n"
    end
  else osn ocdep role;
  osn ocdep "")
  )

fun write_thy (f_tydef,f_constdef,f_thmdef,fb_thm) export_dir thy =
  let
    val _ = print (thy ^ " ")
    val filedep = export_dir ^ "/" ^ thy ^ ".dep"
    val file = export_dir ^ "/" ^ thy ^ ".pb"
    val oc = TextIO.openOut file
    val ocdep = TextIO.openOut filedep
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (f_tydef oc thy) (#types t)
      val _ = app (f_constdef oc thy) (#consts t)
      val cjl = map (fn x => (x,"conjecture")) (DB.theorems thy)
      val axl = map (fn x => (x,"axiom")) (DB.axioms thy @ DB.definitions thy)
      fun cmp (((_,th1),_),((_,th2),_)) =
        Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
      val thml = dict_sort cmp (cjl @ axl)
    in
      app (write_dep ocdep fb_thm thy) thml;
      app (f_thmdef oc thy) thml;
      app TextIO.closeOut [oc,ocdep]
    end
    handle Interrupt => (app TextIO.closeOut [oc,ocdep]; raise Interrupt)
  end

(* -------------------------------------------------------------------------
   Export functions
   ------------------------------------------------------------------------- *)

fun add_ancestry thy = thy :: ancestry thy
fun sorted_ancestry thyl =
  sort_thyl (mk_string_set (List.concat (map add_ancestry thyl)))

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

(*
load "hhExportSexpr"; open hhExportSexpr;
load "tttUnfold"; tttUnfold.load_sigobj ();
val thyl = ancestry (current_theory ());
sexport_export thyl;
*)

end (* struct *)



