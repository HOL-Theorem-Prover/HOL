(* ========================================================================= *)
(* FILE          : hhExportFof.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportFof :> hhExportFof =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportFof"
type thmid = string * string
val type_flag = ref true
val p_flag = ref true
val name_flag = ref true
val fofpar = "fof("
fun nameplain_cv (cv,_:int) =
  if is_const cv then fst (dest_const cv)
  else if is_var cv then fst (dest_var cv)
  else raise ERR "nameplain_cv" ""

(* -------------------------------------------------------------------------
   FOF type
   ------------------------------------------------------------------------- *)

fun fo_fun oc (s,f_arg,argl) =
  if null argl then os oc s else
  (os oc s; os oc "("; oiter oc "," f_arg argl; os oc ")")

fun fof_type oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop (Thy,Tyop)
    in
      fo_fun oc (tyops, fof_type, Args)
    end

(* -------------------------------------------------------------------------
   FOF quantifier
   ------------------------------------------------------------------------- *)

fun fof_vzero oc v =
  if !name_flag
  then os oc (namea_v (v,0))
  else os oc (nameplain_cv (v,0))

fun fof_quant_vl oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " fof_vzero vl; os oc "]: ")

fun fof_forall_tyvarl_tm oc tm =
  let
    val tvl = dict_sort Type.compare (type_vars_in_term tm)
    fun f oc x = os oc (name_vartype x)
  in
    if null tvl orelse not (!type_flag)
    then ()
    else (os oc "!["; oiter oc ", " f tvl; os oc "]: ")
  end

(* -------------------------------------------------------------------------
   FOF term
   ------------------------------------------------------------------------- *)

fun fof_term oc tm =
  let
    val namef = if !name_flag then namea_cv else nameplain_cv
    val (rator,argl) = strip_comb tm in
    if !type_flag then
      (os oc "s("; fof_type oc (type_of tm); os oc ",";
      fo_fun oc (namef (rator,length argl), fof_term, argl);
      os oc ")")
    else fo_fun oc (namef (rator,length argl), fof_term, argl)
  end

(* -------------------------------------------------------------------------
   FOF formula
   ------------------------------------------------------------------------- *)

fun fof_pred oc tm =
  if is_forall tm then fof_quant oc "!" (strip_forall tm)
  else if is_exists tm then fof_quant oc "?" (strip_exists tm)
  else if is_conj tm then fof_binop oc "&" (dest_conj tm)
  else if is_disj tm then fof_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then fof_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "~ ("; fof_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r
      then fof_binop oc "<=>" (l,r)
      else (os oc "("; fof_term oc l; os oc " = "; fof_term oc r; os oc ")")
    end
  else (if !p_flag
       then (os oc "p("; fof_term oc tm; os oc ")")
       else fof_term oc tm)
and fof_binop oc s (l,r) =
  (os oc "("; fof_pred oc l; os oc (" " ^ s ^ " ");
   fof_pred oc r; os oc ")")
and fof_quant oc s (vl,bod) =
  (fof_quant_vl oc s vl; fof_pred oc bod)

fun fof_formula oc tm = (fof_forall_tyvarl_tm oc tm; fof_pred oc tm)

(* -------------------------------------------------------------------------
   Term-level logical operators equations
   ------------------------------------------------------------------------- *)

fun fof_logicformula oc (thy,name) =
  let
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val vl = free_vars_lr tm
  in
    fof_forall_tyvarl_tm oc tm; fof_quant_vl oc "!" vl;
    os oc "(p("; fof_term oc tm ; os oc ") <=> "; fof_pred oc tm; os oc ")"
  end

fun fof_logicdef oc (thy,name) =
  (os oc (fofpar ^ escape ("reserved.logic." ^ name) ^ ",axiom,");
   fof_logicformula oc (thy,name); osn oc ").")

fun fof_quantdef oc (thy,name) =
  let
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val (tm,_) = translate_thm thm
  in
    os oc (fofpar ^ escape ("reserved.quant." ^ name) ^ ",axiom,");
    fof_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   FOF definitions
   ------------------------------------------------------------------------- *)

fun fof_thmdef role oc (thy,name) =
  let
    val thm = DB.fetch thy name
    val (statement,defl) = translate_thm thm
    val fofname = name_thm (thy,name)
    fun f i def =
      (
      os oc (fofpar ^ name_def i fofname ^ ",axiom,");
      fof_formula oc def; osn oc ")."
      )
  in
    ignore (mapi f defl);
    os oc (fofpar ^ fofname ^ "," ^ role ^ ",");
    fof_formula oc statement; osn oc ")."
  end

val app_p_cval =
  let val tml = map (fst o translate_thm o snd) (app_axioml @ p_axioml) in
    mk_fast_set tma_compare (List.concat (map collect_arity_noapp tml))
  end

val combin_cval =
  let val tml = map snd combin_axioml in
    mk_fast_set tma_compare (List.concat (map collect_arity_noapp tml))
  end

val cval_extra = boolop_cval @ combin_cval @ app_p_cval

(* -------------------------------------------------------------------------
   Higher-order theorems
   ------------------------------------------------------------------------- *)

val hocaster_extra = "extra-ho" (* fake theory for these theorems *)

fun fof_boolext oc =
  let val (v0,v1) = (mk_var ("V0",bool),mk_var ("V1",bool)) in
    fof_quant_vl oc "!" [v0,v1];
    os oc "(("; fof_pred oc v0; os oc " <=> "; fof_pred oc v1; os oc ")";
    os oc " => ";
    os oc "("; fof_term oc v0; os oc " = "; fof_term oc v1; os oc "))"
  end

fun fof_thmdef_boolext oc =
  let val fofname = escape "reserved.ho.boolext" in
    os oc (fofpar ^ fofname ^ ",axiom,"); fof_boolext oc; osn oc ")."
  end

fun fof_thmdef_caster oc (name,thm) =
  let
    val (statement,defl) = translate_thm thm
    val _ = if null defl then () else raise ERR "fof_thmdef_caster" ""
  in
    os oc (fofpar ^ escape ("reserved.ho." ^ name) ^ ",axiom,");
    fof_formula oc statement; osn oc ")."
  end

fun fof_thmdef_combin oc (name,tm) =
  (
  os oc (fofpar ^ escape ("reserved.ho." ^ name) ^ ",axiom,");
  fof_formula oc tm; osn oc ")."
  )

fun fof_thmdef_extra oc =
  (
  app (fof_thmdef_caster oc) app_axioml;
  fof_thmdef_boolext oc;
  app (fof_thmdef_caster oc) p_axioml;
  app (fof_thmdef_combin oc) combin_axioml;
  app (fof_logicdef oc) logic_l1;
  app (fof_quantdef oc) quant_l2
  )

(* -------------------------------------------------------------------------
   Arity equations
   ------------------------------------------------------------------------- *)

fun fof_arityeq oc (cv,a) =
  if a = 0 then () else
  let
    val fofname = name_arityeq (cv,a)
    val tm = mk_arity_eq (cv,a)
  in
    os oc (fofpar ^ fofname ^ ",axiom,"); fof_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Write problem
   ------------------------------------------------------------------------- *)

fun collect_tml thmidl =
  let fun f x =
    let val (formula,defl) = translate_thm (uncurry DB.fetch x) in
      mk_term_set (List.concat (map atoms (formula :: defl)))
    end
  in
    mk_term_set (List.concat (map f thmidl))
  end

fun fof_preambule oc tml =
  let
    val cval = mk_sameorder_set tma_compare
      (List.concat (cval_extra :: map collect_arity_noapp tml))
  in
    fof_thmdef_extra oc;
    app (fof_arityeq oc) cval
  end

fun fof_write_pb dir (thmid,(depthyl,depl)) =
  let
    val _ = mkDir_err dir
    val file  = dir ^ "/" ^ name_thm thmid ^ ".p"
    val oc  = TextIO.openOut file
    val tml = collect_tml (thmid :: depl)

  in
    (
    app (fn x => osn oc ("include('" ^ x ^ ".ax').")) depthyl;
    fof_preambule oc tml;
    app (fof_thmdef "axiom" oc) depl;
    fof_thmdef "conjecture" oc thmid;
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(*
load "hhExportFof"; open hhExportFof;
val thmid = ("arithmetic","ADD1");
val depl = valOf (hhExportLib.depo_of_thmid thmid);
val dir = HOLDIR ^ "/src/holyhammer/export_fof_test";
fof_write_pb dir (thmid,depl);
*)

(* -------------------------------------------------------------------------
   Bushy problems
   ------------------------------------------------------------------------- *)

fun write_thy_bushy dir thy =
  let val cjdepl = bushy_dep thy (DB.theorems thy) in
    print (thy ^ " "); app (fof_write_pb dir) cjdepl
  end

fun fof_export_bushy dir thyl =
  let val thyorder = sorted_ancestry thyl in
    mkDir_err dir; app (write_thy_bushy dir) thyorder
  end

(* -------------------------------------------------------------------------
   Chainy problems
   ------------------------------------------------------------------------- *)

fun fof_export_thy dir thy =
  let
    val _ = mkDir_err dir
    val file  = dir ^ "/" ^ thy ^ ".ax"
    val oc  = TextIO.openOut file
    val thmidl = thmidl_in_thy thy
    val tml = collect_tml thmidl
  in
    (
    fof_preambule oc tml;
    app (fof_thmdef "axiom" oc) thmidl;
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy dir thyorder thy =
  let val cjdepl = chainy_dep thyorder thy (DB.theorems thy) in
    print (thy ^ " "); app (fof_write_pb dir) cjdepl
  end

fun fof_export_chainy dir thyl =
  let val thyorder = sorted_ancestry thyl in
    mkDir_err dir;
    app (fof_export_thy (dir ^ "/theories")) thyorder;
    app (write_thy_chainy (dir ^ "/problems") thyorder) thyorder
  end

(* -------------------------------------------------------------------------
   Export standard library
   ------------------------------------------------------------------------- *)

(*
load "hhExportFof"; open hhExportFof;
load "tttUnfold"; tttUnfold.load_sigobj ();
val thyl = ancestry (current_theory ());
val bushydir = HOLDIR ^ "/src/holyhammer/fof_bushy";
fof_export_bushy bushydir thyl;
val chainydir = HOLDIR ^ "/src/holyhammer/fof_chainy";
fof_export_chainy chainydir thyl;
*)

(* -------------------------------------------------------------------------
   Interface to holyhammer
   ------------------------------------------------------------------------- *)

fun tml_of_pb (cj,namethml) =
  let
    val tml_cj = (op ::) (translate cj)
    val tmll_axl = map ((op ::) o translate_thm o snd) namethml
  in
    mk_term_set (tml_cj @ List.concat (tmll_axl))
  end

fun collect_arity_pb (cj,namethml) =
  let val tml = tml_of_pb (cj,namethml) in
    mk_fast_set tma_compare (List.concat (map collect_arity_noapp tml))
  end

fun fof_cjdef oc cj =
  let
    val (statement,defl) = translate cj
    val fofname = "conjecture"
    fun f i def =
      (os oc (fofpar ^ name_def i fofname ^ ",axiom,");
       fof_formula oc def; osn oc ").")
  in
    ignore (mapi f defl);
    os oc (fofpar ^ fofname ^ ",conjecture,");
    fof_formula oc statement; osn oc ")."
  end

fun fof_axdef oc (name,thm) =
  let
    val (statement,defl) = translate_thm thm
    val fofname = escape ("thm." ^ name)
    fun f i def =
      (os oc (fofpar ^ name_def i fofname  ^ ",axiom,");
       fof_formula oc def; osn oc ").")
  in
    ignore (mapi f defl);
    os oc (fofpar ^ fofname ^ ",axiom,");
    fof_formula oc statement; osn oc ")."
  end

fun fof_export_pb dir (cj,namethml) =
  let
    val file = dir ^ "/atp_in"
    val oc = TextIO.openOut file
    val cval = collect_arity_pb (cj,namethml)
  in
    (fof_thmdef_extra oc;
     app (fof_arityeq oc) (mk_sameorder_set tma_compare (cval_extra @ cval));
     app (fof_axdef oc) namethml;
     fof_cjdef oc cj;
     TextIO.closeOut oc)
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(* -------------------------------------------------------------------------
   This function is a work-in-progress.
   To be runned with all flag off to export a problem that is already
   in first-order format with TPTP capitalization
   Exporting a problem stated as goal.
   Free variables should start with lowercase.
   ------------------------------------------------------------------------- *)

fun fof_export_goal file (axl,cj) =
  let
    val _ = if not (all (fn x => type_of x = bool) (cj :: axl))
            then raise ERR "fof_export_pbtm" "not of type bool"
            else ()
    fun f i k = (k,"axiom" ^ its i)
    val axlnamed = mapi f axl
    val oc = TextIO.openOut file
    fun fax (ax,fofname) =
      (os oc (fofpar ^ fofname ^ ",axiom,");
       fof_formula oc ax;
       osn oc ").")
  in
    app fax axlnamed;
    os oc (fofpar ^ "conjecture" ^ ",conjecture,");
    fof_formula oc cj;
    osn oc ").";
    TextIO.closeOut oc
  end

(*
load "holyHammer"; open holyhammer;
load "hhExportFof"; open hhExportFof;
load "mlThmData"; open mlThmData;
load "mlFeature"; open mlFeature;
val cj = ``1+1=2``;
val goal : goal = ([],cj);
val n = 32;
load "mlNearestNeighbor"; open mlNearestNeighbor;
val thmdata = create_thmdata ();
val premises = thmknn_wdep thmdata n (feahash_of_goal goal);
val namethml = thml_of_namel premises;
val hh_dir = HOLDIR ^ "/src/holyhammer";
fof_export_pb hh_dir (cj,namethml);
*)

end (* struct *)
