(* ===================================================================== *)
(* FILE          : hhExport.sml                                          *)
(* DESCRIPTION   : Export HOL4 theories in a s-expression format         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2018                                                  *)
(* ===================================================================== *)

structure hhExport :> hhExport =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate holyHammer

val ERR = mk_HOL_ERR "hhExport"

(* -------------------------------------------------------------------------
   Writer shortcuts
   ------------------------------------------------------------------------- *)

fun os oc s = TextIO.output (oc,s)

fun oiter_aux oc sep f l = case l of
    []     => ()
  | [a]    => f oc a
  | a :: m => (f oc a; os oc sep; oiter_aux oc sep f m)

fun oiter oc sep f l = oiter_aux oc sep f l

fun double_quote s = "\"" ^ s ^ "\""

(* -------------------------------------------------------------------------
   S-expression escaping
   ------------------------------------------------------------------------- *)

(* "V" is used as prefix in rename_bvarl *)
fun sexpr_prep_tm tm =
  rename_bvarl escape (list_mk_forall (free_vars_lr tm, tm))

(* variables are already escaped by sexpr_prep_tm *)
fun sexpr_of_var v = double_quote (fst (dest_var v))

fun sexpr_of_const c =
  let val {Name, Thy, Ty} = dest_thy_const c in
    double_quote (escape ("c." ^ Thy ^ "." ^ Name))
  end

fun sexpr_of_vartype ty =
  double_quote ("A" ^ (escape (dest_vartype ty)))

fun sexpr_of_tyop ty =
  let val {Args, Thy, Tyop} = dest_thy_type ty in
    double_quote (escape ("ty" ^ "." ^ Thy ^ "." ^ Tyop))
  end

fun sexpr_of_thm (thy,name) =
   double_quote (escape ("thm" ^ "." ^ thy ^ "." ^ name))

(* -------------------------------------------------------------------------
   Terms
   ------------------------------------------------------------------------- *)

fun sexpr_write_type oc ty =
  if is_vartype ty then os oc (sexpr_of_vartype ty) else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if null Args
      then os oc (sexpr_of_tyop ty)
      else (os oc "("; os oc (sexpr_of_tyop ty);
            os oc " "; oiter oc " " sexpr_write_type Args; os oc ")")
    end

fun full_match_type t1 t2 =
  let
    val (sub1,al) = raw_match_type t1 t2 ([],[])
    fun id_sub a = {redex = a, residue = a}
    val sub2 = map id_sub al
    fun cmp (a,b) = Type.compare (#redex a, #redex b)
  in
    dict_sort cmp (sub1 @ sub2)
  end

fun sexpr_write_term oc tm =
  if is_var tm then os oc (sexpr_of_var tm)
  else if is_const tm then
    let
      val {Thy, Name, Ty} = dest_thy_const tm
      val mgty = type_of (prim_mk_const {Thy = Thy, Name = Name})
      val subst = full_match_type mgty Ty
      val resl = map #residue subst
    in
      if null resl
      then os oc (sexpr_of_const tm)
      else (os oc "("; os oc (sexpr_of_const tm); os oc " ";
            oiter oc " " sexpr_write_type resl; os oc ")")
    end
  else if is_comb tm then
    let val (rator,argl) = strip_comb tm in
      os oc "("; sexpr_write_term oc rator;
      os oc " "; oiter oc " " sexpr_write_term argl; os oc ")"
    end
  else if is_abs tm then
    let val (bvar,body) = dest_abs tm in
      os oc "("; os oc "lambda"; os oc " ";
      os oc (sexpr_of_var bvar); os oc " ";
      sexpr_write_type oc (type_of bvar); os oc " ";
      sexpr_write_term oc body; os oc ")"
    end
  else raise ERR "sexpr_write_term" ""

(* -------------------------------------------------------------------------
   Definitions (types,terms,theorems)
   ------------------------------------------------------------------------- *)

fun sexpr_tydef oc thy (tyop,arity) =
  (
  os oc "("; os oc "type_definition"; os oc " ";
  os oc (double_quote (escape ("ty" ^ "." ^ thy ^ "." ^ tyop))); os oc " ";
  os oc (int_to_string arity); os oc ")\n"
  )

fun sexpr_tyquant_type oc ty =
  let val tvl = dict_sort Type.compare (type_vars ty) in
    if null tvl
    then sexpr_write_type oc ty
    else
      (
      os oc "("; os oc "forall_tyvarl_type"; os oc " ";
      os oc "("; oiter oc " " sexpr_write_type tvl; os oc ")"; os oc " ";
      sexpr_write_type oc ty; os oc ")"
      )
  end

fun sexpr_tyquant_term oc tm =
  let
    val tyl = map type_of (find_terms is_const tm @ all_vars tm)
    val tvl = dict_sort Type.compare (type_varsl tyl)
  in
    if null tvl
    then sexpr_write_term oc tm
    else
      (
      os oc "("; os oc "forall_tyvarl_term"; os oc " ";
      os oc "("; oiter oc " " sexpr_write_type tvl; os oc ")"; os oc " ";
      sexpr_write_term oc tm; os oc ")"
      )
  end

fun endline_to_space x = case x of #"\n" => #" " | a => a

fun rm_endline x = implode (map endline_to_space (explode x))

(* most general type expected *)
fun sexpr_constdef oc thy (name,ty) =
  (
  os oc "; "; os oc ("c." ^ thy ^ "." ^ name); os oc "\n";
  os oc "; ";
  os oc (rm_endline (type_to_string ty));
  os oc "\n";
  os oc "("; os oc "constant_definition"; os oc " ";
  os oc (double_quote (escape ("c." ^ thy ^ "." ^ name))); os oc " ";
  sexpr_tyquant_type oc ty; os oc ")\n"
  )

fun write_dep ocdep thy ((name,thm),role) =
  (
  os ocdep (sexpr_of_thm (thy,name) ^ "\n");
  (if role = "conjecture" then
    let
      val (b,depl1) = intactdep_of_thm thm
      val depl2 = map (split_string "Theory.") depl1
      val depl3 = map sexpr_of_thm depl2
    in
      os ocdep (role ^ "\n");
      os ocdep (if b then  "intact\n" else "broken\n");
      oiter ocdep " " os depl3;
      os ocdep "\n"
    end
  else os ocdep (role ^ "\n"));
  os ocdep "\n"
  )

fun sexpr_write_thm oc ocdep thy ((name,thm),role) =
  let val tm = concl (DISCH_ALL thm) in
    write_dep ocdep thy ((name,thm),role);
    os oc "; "; os oc (thy ^ "." ^ name); os oc "\n";
    os oc "; ";
    os oc (rm_endline (term_to_string tm));
    os oc "\n";
    os oc "("; os oc role; os oc " ";
    os oc (sexpr_of_thm (thy,name)); os oc " ";
    sexpr_tyquant_term oc (sexpr_prep_tm tm); os oc ")\n"
  end

(* -------------------------------------------------------------------------
   Theories
   ------------------------------------------------------------------------- *)

val casc_sexpr_dir = HOLDIR ^ "/src/holyhammer/casc_sexpr"

fun sexpr_write_thy thy =
  let
    val _ = mkDir_err casc_sexpr_dir
    val filedep = casc_sexpr_dir ^ "/" ^ thy ^ ".dep"
    val file = casc_sexpr_dir ^ "/" ^ thy
    val oc = TextIO.openOut file
    val ocdep = TextIO.openOut filedep
    val THEORY(_,t) = dest_theory thy
    val _ = app (sexpr_tydef oc thy) (#types t)
    val _ = app (sexpr_constdef oc thy) (#consts t)
    val axl = map (fn x => (x,"conjecture")) (DB.theorems thy)
    val defl = map (fn x => (x,"axiom")) (DB.axioms thy @ DB.definitions thy)
    fun cmp (((_,th1),_),((_,th2),_)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
    val thml = dict_sort cmp (axl @ defl)
  in
    app (sexpr_write_thm oc ocdep thy) thml
    handle Interrupt => (TextIO.closeOut oc; TextIO.closeOut ocdep;
                         raise Interrupt);
    TextIO.closeOut oc; TextIO.closeOut ocdep
  end

fun sexpr_write_thy_ancestry thy =
  app sexpr_write_thy (sort_thyl (thy :: ancestry thy))

fun sexpr_write_thyl_ancestry thyl =
  app sexpr_write_thy (sort_thyl thyl)

fun write_thy_ancestry_order thy =
  let
    val _ = mkDir_err casc_sexpr_dir
    val file = casc_sexpr_dir ^ "/theory_order"
  in
    writel file [String.concatWith " " (sort_thyl (thy :: ancestry thy))]
  end

fun write_thyl_ancestry_order thyl =
  let
    val _ = mkDir_err casc_sexpr_dir
    val file = casc_sexpr_dir ^ "/theory_order"
  in
    writel file [String.concatWith " " (sort_thyl thyl)]
  end

(* -------------------------------------------------------------------------
   FOF export
   ------------------------------------------------------------------------- *)

val fof_export_dir = HOLDIR ^ "/src/holyhammer/fof_export"
val fof_targets_file = fof_export_dir ^ "/fof_targets"
val fof_problems_dir = fof_export_dir ^ "/fof_problems"
val fof_chainy_dir = fof_export_dir ^ "/fof_chainy"

fun fof_export_pb (file,(premises,cj)) =
  (
  append_endline fof_targets_file file;
  translate_write_file file (premises,cj)
  )

fun fof_export_thy thy =
  let
    val _ = mkDir_err fof_export_dir
    val _ = mkDir_err fof_problems_dir
    val thml = DB.theorems thy
    val pbl1 = map_snd (fn x => (intactdep_of_thm x, x)) thml
    val pbl2 = filter (fn (_,x) => fst (fst x)) pbl1
    val pbl3 = map_snd (fn (a,b) => (snd a, list_mk_imp (dest_thm b))) pbl2
    val pbl4 =
      map_fst (fn x => fof_problems_dir ^ "/" ^ sexpr_of_thm (thy,x)) pbl3
  in
    app fof_export_pb pbl4
  end
(*
fun fof_export_statement_thy thy =
  let
    val _ = mkDir_err fof_export_dir
    val _ = mkDir_err fof_problems_dir
    val thml = DB.thms thy
    fun cmp ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
    val pbl1 = map_snd (fn x => ([], x)) thml
    val pbl3 = map_snd (fn (a,b) => (a, list_mk_imp (dest_thm b))) pbl1
    val pbl4 = map_fst (fn x => fof_problems_dir ^ "/" ^ sexpr_of_thm (thy,x)) pbl3
  in
    app fof_export_pb pbl4
  end
*)

end (* struct *)

(* Example

  load "hhExport"; open hhTranslate hhExport;

  (* fof export *)
  val _ = complete_flag := true;
  app fof_export_thy thyl;

  (* sexpr export *)
  load "tttUnfold"; open tttUnfold; load_sigobj ();
  val thyl = ancestry "scratch";
  sexpr_write_thyl_ancestry thyl;
  write_thyl_ancestry_order thyl;

*)

