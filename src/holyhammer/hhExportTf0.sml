(* ========================================================================= *)
(* FILE          : hhExportTf0.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTf0 :> hhExportTf0 =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportTf0"

val tffpar = "tff("

(* -------------------------------------------------------------------------
   Polyworld (deep embedding) and Monoworld (shallow embeddding)
   Todo: first do everything in polyworld.
   ------------------------------------------------------------------------- *)

val (utype,dtype,dutype) = ("u","d","du")
val polyw_typel = [utype,dtype,dutype]

(* -------------------------------------------------------------------------
   TF0 domains
   ------------------------------------------------------------------------- *)

fun fo_fun oc (s,f_arg,argl) = 
  if null argl then os oc s else 
  (os oc s; os oc "("; oiter oc "," f_arg argl; os oc ")")

fun tf0_domain oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop (Thy,Tyop)
    in
      fo_fun oc (tyops, tf0_domain, Args)
    end

(* -------------------------------------------------------------------------
   TF0 quantifier
   ------------------------------------------------------------------------- *)

fun tf0_vzero oc v = os oc (namea_v (v,0) ^ ":" ^ utype)

fun tf0_quant_vl oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " tf0_vzero vl; os oc "]: ")

fun tf0_forall_tyvarl_tm oc tm =
  let
    val tvl = dict_sort Type.compare (type_vars_in_term tm)
    fun f oc x = os oc (name_vartype x ^ ":" ^ dtype)
  in
    if null tvl then () else (os oc "!["; oiter oc ", " f tvl; os oc "]: ")
  end

(* -------------------------------------------------------------------------
   TF0 term
   ------------------------------------------------------------------------- *)

(* todo: add i here later *)
fun tf0_term oc tm =
  let val (rator,argl) = strip_comb tm in
    os oc "s("; tf0_domain oc (type_of tm); os oc ",";
    fo_fun oc (namea_cv (rator,length argl), tf0_term, argl);
    os oc ")"
  end

(* -------------------------------------------------------------------------
   TF0 formula
   ------------------------------------------------------------------------- *)

fun tf0_pred oc tm =
  if is_forall tm then tf0_quant oc "!" (strip_forall tm)
  else if is_exists tm then tf0_quant oc "?" (strip_exists tm)
  else if is_conj tm then tf0_binop oc "&" (dest_conj tm)
  else if is_disj tm then tf0_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then tf0_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "~ ("; tf0_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r
      then tf0_binop oc "<=>" (l,r)
      else (os oc "("; tf0_term oc l; os oc " = "; tf0_term oc r; os oc ")")
    end
  else (os oc "p("; tf0_term oc tm; os oc ")")
and tf0_binop oc s (l,r) =
  (os oc "("; tf0_pred oc l; os oc (" " ^ s ^ " "); 
   tf0_pred oc r; os oc ")")
and tf0_quant oc s (vl,bod) =
  (tf0_quant_vl oc s vl; tf0_pred oc bod)

fun tf0_formula oc tm = (tf0_forall_tyvarl_tm oc tm; tf0_pred oc tm)

(* -------------------------------------------------------------------------
   Term-level logical operators equations
   ------------------------------------------------------------------------- *)

fun tf0_logicformula oc (thy,name) = 
  let 
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val vl = free_vars_lr tm 
  in
    tf0_forall_tyvarl_tm oc tm; tf0_quant_vl oc "!" vl;
    os oc "(p("; tf0_term oc tm ; os oc ") <=> "; tf0_pred oc tm; os oc ")"
  end

fun tf0_logicdef oc (thy,name) =
  (os oc (tffpar ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
   tf0_logicformula oc (thy,name); osn oc ").")

fun tf0_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val (tm,_) = fof_translate_thm thm
  in
    os oc (tffpar ^ escape ("quantdef." ^ name) ^ ",axiom,"); 
    tf0_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   TF0 definitions
   ------------------------------------------------------------------------- *)

(* Types *)
fun tf0_tyopdef_polyw oc tf0name =
  osn oc (tffpar ^ tf0name ^ ",type," ^ tf0name ^ ":" ^ ttype ^ ").")

fun tf0_tyopdef oc ((thy,tyop),arity) = ()

(* Constants *)
fun tf0_polyw_cvty a =
  if a <= 0 then utype 
  else if a = 1 then dutype ^ " > " ^ utype 
  else 
    "(" ^ String.concatWith " * " (List.tabulate (a,fn _ => dutype)) ^ ")"
    ^ " > " ^ utype

fun tf0_polyw_cvdef_named oc (tf0name,a) =
  (os oc (tffpar ^ tf0name ^ ",type," ^ tf0name ^ ":");
   os oc (tf0_polyw_cvty a); osn oc ").")

fun tf0_polyw_cvdef oc (tm,a) =
  tf0_polyw_cvdef_named oc (namea_cv (tm,a), a) 

(* Theorems *)
fun tf0_thmdef role oc (thy,name) =
  let 
    val thm = DB.fetch thy name
    val (cj,defl) = fof_translate_thm thm
    val tf0name = name_thm (thy,name)
    fun f i def = 
      (
      os oc (tffpar ^ escape ("def" ^ its i ^ ".") ^ tf0name ^ ",axiom,");
      tf0_formula oc def; osn oc ")."
      )
  in
    ignore (mapi f defl);
    os oc (tffpar ^ tf0name ^ "," ^ role ^ ",");
    tf0_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Higher-order constants + sort function
   ------------------------------------------------------------------------- *)

fun tf0_cdef_app oc = 
  let
    val a = 2
    val tf0name = namea_v (mk_var ("app",bool),a) (* bool is dummy type *)
  in
    tf0_polyw_cvdef_named oc (tf0name,a)
  end

fun tf0_cdef_p oc =
  let val tf0name = "p" in
    os oc (tffpar ^ tf0name ^ ",type," ^ tf0name ^ ":");
    os oc (dutype ^ " > $o"); osn oc ")."
  end

fun tf0_cdef_s oc =
  let val tf0name = "s" in
    os oc (tffpar ^ tf0name ^ ",type," ^ tf0name ^ ":");
    os oc ("(" ^ dtype ^ " * " ^ utype ^ ") > " ^ dutype); osn oc ")."
  end 

fun tf0_cvdef_extra oc =
  (app (tf0_tyopdef_polyw oc) polyw_typel; (* hack: exporting types here *)
   tf0_cdef_s oc; tf0_cdef_app oc; tf0_cdef_p oc) 

(* -------------------------------------------------------------------------
   Higher-order theorems
   ------------------------------------------------------------------------- *)

val hocaster_extra = "extra-ho" (* fake theory for these theorems *)

fun tf0_boolext oc = 
  let val (v0,v1) = (mk_var ("V0",bool),mk_var ("V1",bool)) in
    tf0_quant_vl oc "!" [v0,v1];
    os oc "(("; tf0_pred oc v0; os oc " <=> "; tf0_pred oc v1; os oc ")";
    os oc " => ";
    os oc "("; tf0_term oc v0; os oc " = "; tf0_term oc v1; os oc "))"
  end

fun tf0_thmdef_boolext oc =
  let val tf0name = name_thm (hocaster_extra,"boolext") in
    os oc (tffpar ^ tf0name ^ ",axiom,"); tf0_boolext oc; osn oc ")."
  end

fun tf0_thmdef_caster oc (name,thm) =
  let 
    val (cj,defl) = fof_translate_thm thm
    val _ = if null defl then () else raise ERR "tf0_thmdef_caster" ""
  in
    os oc (tffpar ^ name_thm (hocaster_extra,name) ^ ",axiom,");
    tf0_formula oc cj; osn oc ")."
  end

fun tf0_thmdef_combin oc (name,tm) =
  let val tf0name = name_thm (hocaster_extra,name) in
    os oc (tffpar ^ tf0name ^ ",axiom,"); tf0_formula oc tm; osn oc ")."
  end

fun tf0_thmdef_extra oc = 
  (
  app (tf0_thmdef_caster oc) app_axioml;
  tf0_thmdef_boolext oc;
  app (tf0_thmdef_caster oc) p_axioml;
  app (tf0_thmdef_combin oc) combin_axioml;
  app (tf0_logicdef oc) logic_l1;
  app (tf0_quantdef oc) quant_l2
  )

(* todo: declare types as constants in domains *)

val tyopl_extra = []

val app_p_cval =
  let val tml = map (fst o fof_translate_thm o snd) (app_axioml @ p_axioml) in
    mk_fast_set tma_compare (List.concat (map collect_arity tml)) 
  end

val combin_cval = 
  let val tml = map snd combin_axioml in
    mk_fast_set tma_compare (List.concat (map collect_arity tml)) 
  end

val cval_extra = add_zeroarity (boolop_cval @ combin_cval @ app_p_cval)

(* -------------------------------------------------------------------------
   Arity equations
   ------------------------------------------------------------------------- *)

fun tf0_arityeq oc (cv,a) = 
  if a = 0 then () else
  let 
    val tf0name = "arityeq" ^ its a ^ escape "." ^ namea_cv (cv,a) 
    val tm = mk_arity_eq (cv,a)
  in
    os oc (tffpar ^ tf0name ^ ",axiom,"); tf0_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

val tf0_bushy_dir = hh_dir ^ "/export_tf0_bushy"
fun tf0_export_bushy thyl =
  let 
    val thyorder = sorted_ancestry thyl 
    val dir = (mkDir_err tf0_bushy_dir; tf0_bushy_dir)
    fun f thy =
      write_thy_bushy dir tff_translate_thm uniq_cvdef_mgc 
       (tyopl_extra,cval_extra)
       (tf0_tyopdef, tf0_cvdef_extra, tf0_polyw_cvdef, 
        tf0_thmdef_extra, tf0_arityeq, tf0_thmdef)
      thy
  in
    mkDir_err dir; app f thyorder
  end

val tf0_chainy_dir = hh_dir ^ "/export_tf0_chainy"
fun tf0_export_chainy thyl =
  let 
    val thyorder = sorted_ancestry thyl 
    val dir = (mkDir_err tf0_chainy_dir; tf0_chainy_dir)
    fun f thy =
      write_thy_chainy dir thyorder tff_translate_thm uniq_cvdef_mgc
        (tyopl_extra,cval_extra)
        (tf0_tyopdef, tf0_cvdef_extra, tf0_polyw_cvdef, 
         tf0_thmdef_extra, tf0_arityeq, tf0_thmdef)
      thy
  in
    mkDir_err dir; app f thyorder
  end

(* load "hhExportTf0"; open hhExportTf0; tf0_export_bushy ["arithmetic"]; *)

end (* struct *)
