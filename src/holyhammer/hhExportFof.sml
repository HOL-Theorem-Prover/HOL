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

val fofpar = "fof("

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

fun fof_vzero oc v = os oc (namea_v (v,0))

fun fof_quant_vl oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " fof_vzero vl; os oc "]: ")

fun fof_forall_tyvarl_tm oc tm =
  let
    val tvl = dict_sort Type.compare (type_vars_in_term tm)
    fun f oc x = os oc (name_vartype x)
  in
    if null tvl then () else (os oc "!["; oiter oc ", " f tvl; os oc "]: ")
  end

fun fof_forall_tyvarl_ty oc ty =
  let 
    val tvl = dict_sort Type.compare (type_vars ty) 
    fun f oc x = os oc (name_vartype x)
  in
    if null tvl then () else (os oc "!>["; oiter oc ", " f tvl; os oc "]: ")
  end

(* -------------------------------------------------------------------------
   FOF term
   ------------------------------------------------------------------------- *)

fun fof_term oc tm =
  let val (rator,argl) = strip_comb tm in
    os oc "s("; fof_type oc (type_of tm); os oc ",";
    os oc (namea_cv (rator,length argl));
    if null argl then ()
    else (os oc "("; oiter oc "," fof_term argl; os oc ")");
    os oc ")"
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
      else (fof_term oc l; os oc " = "; fof_term oc r)
    end
  else (os oc "p("; fof_term oc tm; os oc ")")
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
  (os oc (fofpar ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
   fof_logicformula oc (thy,name); osn oc ").")

fun fof_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val (tm,_) = fof_translate_thm thm
  in
    os oc (fofpar ^ escape ("quantdef." ^ name) ^ ",axiom,"); 
    fof_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   FOF definitions
   ------------------------------------------------------------------------- *)

fun fof_tyopdef oc _ = ()
fun fof_cvdef oc (tm,a) = ()

fun fof_thmdef role oc (thy,name) =
  let 
    val thm = DB.fetch thy name
    val (cj,defl) = fof_translate_thm thm
    val fofname = name_thm (thy,name)
    fun f i def = 
      (
      os oc (fofpar ^ escape ("def" ^ its i ^ ".") ^ fofname ^ ",axiom,");
      fof_formula oc def; osn oc ")."
      )
  in
    ignore (mapi f defl);
    os oc (fofpar ^ fofname ^ "," ^ role ^ ",");
    fof_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Do not print constant definitions
   ------------------------------------------------------------------------- *)

fun fof_cvdef_extra oc = () 
val tyopl_extra = []
val cval_extra = []

(* -------------------------------------------------------------------------
   Higher-order theorems
   ------------------------------------------------------------------------- *)

val hocaster_extra = "extra-ho" (* fake theory for these theorems *)

fun fof_boolext oc = 
  let val vl = map mk_var [("V0",bool),("V1",bool)] in
    fof_quant_vl oc "!" vl;
    os oc "((p(V0_2E0) <=> p(V1_2E0)) => (V0_2E0 = V1_2E0))"
  end

fun fof_thmdef_boolext oc =
  let val fofname = name_thm (hocaster_extra,"boolext") in
    os oc (fofpar ^ fofname ^ ",axiom,"); fof_boolext oc; osn oc ")."
  end

fun fof_thmdef_caster oc (name,thm) =
  let 
    val (cj,defl) = fof_translate_thm thm
    val _ = if null defl then () else raise ERR "fof_thmdef_caster" ""
  in
    os oc (fofpar ^ name_thm (hocaster_extra,name) ^ ",axiom,");
    fof_formula oc cj; osn oc ")."
  end

fun fof_thmdef_combin oc (name,tm) =
  let val fofname = name_thm (hocaster_extra,name) in
    os oc (fofpar ^ fofname ^ ",axiom,"); fof_formula oc tm; osn oc ")."
  end

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
    val fofname = "arityeq" ^ its a ^ escape "." ^ namea_cv (cv,a) 
    val tm = mk_arity_eq (cv,a)
  in
    os oc (fofpar ^ fofname ^ ",axiom,"); fof_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

val fof_bushy_dir = hh_dir ^ "/export_fof_bushy"
fun fof_export_bushy thyl =
  let 
    val thyorder = sorted_ancestry thyl 
    val dir = (mkDir_err fof_bushy_dir; fof_bushy_dir)
    fun f thy =
      write_thy_bushy dir fof_translate_thm uniq_cvdef_mgc 
       (tyopl_extra,cval_extra)
       (fof_tyopdef, fof_cvdef_extra, fof_cvdef, 
        fof_thmdef_extra, fof_arityeq, fof_thmdef)
      thy
  in
    mkDir_err dir; app f thyorder
  end

val fof_chainy_dir = hh_dir ^ "/export_fof_chainy"
fun fof_export_chainy thyl =
  let 
    val thyorder = sorted_ancestry thyl 
    val dir = (mkDir_err fof_chainy_dir; fof_chainy_dir)
    fun f thy =
      write_thy_chainy dir thyorder fof_translate_thm uniq_cvdef_mgc
        (tyopl_extra,cval_extra)
        (fof_tyopdef, fof_cvdef_extra, fof_cvdef, 
         fof_thmdef_extra, fof_arityeq, fof_thmdef)
      thy
  in
    mkDir_err dir; app f thyorder
  end

(* load "hhExportFof"; open hhExportFof; fof_export_bushy ["arithmetic"]; *)

end (* struct *)
