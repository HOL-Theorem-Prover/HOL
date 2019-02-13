(* ========================================================================= *)
(* FILE          : hhExportTh0.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTh0 :> hhExportTh0 =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportTh0"

val thfpar = "thf("

(* -------------------------------------------------------------------------
   Polyworld (deep embedding) and Monoworld (shallow embeddding)
   Todo: first do everything in polyworld.
   ------------------------------------------------------------------------- *)

val (utype,dtype,dutype) = ("u","d","du")
val polyw_typel = [utype,dtype,dutype]

(* -------------------------------------------------------------------------
   TH0 domains
   ------------------------------------------------------------------------- *)

fun ho_fun oc (s,f_arg,argl) = 
  if null argl then os oc s else 
  (os oc "("; os oc s; os oc " @ "; oiter oc " @ " f_arg argl; os oc ")")

fun th0_domain oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop (Thy,Tyop)
    in
      ho_fun oc (tyops, th0_domain, Args)
    end

(* -------------------------------------------------------------------------
   TH0 quantifier
   ------------------------------------------------------------------------- *)

fun th0_vzero oc v = os oc (namea_v (v,0) ^ ":" ^ utype)

fun th0_quant_vl oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " th0_vzero vl; os oc "]: ")

fun th0_forall_tyvarl_tm oc tm =
  let
    val tvl = dict_sort Type.compare (type_vars_in_term tm)
    fun f oc x = os oc (name_vartype x ^ ":" ^ dtype)
  in
    if null tvl then () else (os oc "!["; oiter oc ", " f tvl; os oc "]: ")
  end

(* -------------------------------------------------------------------------
   TH0 term
   ------------------------------------------------------------------------- *)

(* todo: add i here later *)
fun th0_term oc tm =
  let val (rator,argl) = strip_comb tm in
    os oc "(";
    os oc "s @ "; th0_domain oc (type_of tm); os oc " @ ";
    ho_fun oc (namea_cv (rator,length argl), th0_term, argl);
    os oc ")"
  end

(* -------------------------------------------------------------------------
   TH0 formula
   ------------------------------------------------------------------------- *)

fun th0_pred oc tm =
  if is_forall tm then th0_quant oc "!" (strip_forall tm)
  else if is_exists tm then th0_quant oc "?" (strip_exists tm)
  else if is_conj tm then th0_binop oc "&" (dest_conj tm)
  else if is_disj tm then th0_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then th0_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "(~ "; th0_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r
      then th0_binop oc "<=>" (l,r)
      else (os oc "("; th0_term oc l; os oc " = "; th0_term oc r; os oc ")")
    end
  else (os oc "(p @ "; th0_term oc tm; os oc ")")
and th0_binop oc s (l,r) =
  (os oc "("; th0_pred oc l; os oc (" " ^ s ^ " "); 
   th0_pred oc r; os oc ")")
and th0_quant oc s (vl,bod) =
  (th0_quant_vl oc s vl; th0_pred oc bod)

fun th0_formula oc tm = (th0_forall_tyvarl_tm oc tm; th0_pred oc tm)

(* -------------------------------------------------------------------------
   Term-level logical operators equations
   ------------------------------------------------------------------------- *)

fun th0_logicformula oc (thy,name) = 
  let 
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val vl = free_vars_lr tm 
  in
    th0_forall_tyvarl_tm oc tm; th0_quant_vl oc "!" vl;
    os oc "((p @"; th0_term oc tm ; os oc ") <=> "; th0_pred oc tm; os oc ")"
  end

fun th0_logicdef oc (thy,name) =
  (os oc (thfpar ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
   th0_logicformula oc (thy,name); osn oc ").")

fun th0_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val (tm,_) = fof_translate_thm thm
  in
    os oc (thfpar ^ escape ("quantdef." ^ name) ^ ",axiom,"); 
    th0_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   TH0 definitions
   ------------------------------------------------------------------------- *)

(* Types *)
fun th0_tyopdef_polyw oc th0name =
  osn oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":" ^ ttype ^ ").")

fun th0_polyw_tyopty a =
  if a = 0 then dtype else
  "(" ^ String.concatWith " > " (List.tabulate (a+1, fn _ => dtype)) ^ ")"

fun th0_tyopdef oc ((thy,tyop),a) = 
  let val th0name = name_tyop (thy,tyop) in
    (os oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":");
     os oc (th0_polyw_tyopty a); osn oc ").")
  end

(* Constants *)
fun th0_polyw_cvty a =
  if a <= 0 then utype else 
    "(" ^ String.concatWith " > " (List.tabulate (a,fn _ => dutype)) ^ 
    " > " ^ utype ^ ")"

fun th0_polyw_cvdef_named oc (th0name,a) =
  (os oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":");
   os oc (th0_polyw_cvty a); osn oc ").")

fun th0_polyw_cvdef oc (tm,a) =
  th0_polyw_cvdef_named oc (namea_cv (tm,a), a) 

(* Theorems *)
fun th0_thmdef role oc (thy,name) =
  let 
    val thm = DB.fetch thy name
    val (cj,defl) = fof_translate_thm thm
    val th0name = name_thm (thy,name)
    fun f i def = 
      (
      os oc (thfpar ^ escape ("def" ^ its i ^ ".") ^ th0name ^ ",axiom,");
      th0_formula oc def; osn oc ")."
      )
  in
    ignore (mapi f defl);
    os oc (thfpar ^ th0name ^ "," ^ role ^ ",");
    th0_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Higher-order constants + sort function
   ------------------------------------------------------------------------- *)

fun th0_tyopdef_extra oc = app (th0_tyopdef_polyw oc) polyw_typel;

fun th0_cdef_app oc = 
  let
    val a = 2
    val th0name = namea_v (mk_var ("app",bool),a) (* bool is dummy type *)
  in
    th0_polyw_cvdef_named oc (th0name,a)
  end

fun th0_cdef_p oc =
  let val th0name = "p" in
    os oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":");
    os oc ("(" ^ dutype ^ " > $o)"); osn oc ")."
  end

fun th0_cdef_s oc =
  let val th0name = "s" in
    os oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":");
    os oc ("(" ^ dtype ^ " > " ^ utype ^ " > " ^ dutype ^ ")"); osn oc ")."
  end

fun th0_cvdef_extra oc =
  (th0_cdef_s oc; th0_cdef_app oc; th0_cdef_p oc) 

(* -------------------------------------------------------------------------
   Higher-order theorems
   ------------------------------------------------------------------------- *)

val hocaster_extra = "extra-ho" (* fake theory for these theorems *)

fun th0_boolext oc = 
  let val (v0,v1) = (mk_var ("V0",bool),mk_var ("V1",bool)) in
    th0_quant_vl oc "!" [v0,v1];
    os oc "(("; th0_pred oc v0; os oc " <=> "; th0_pred oc v1; os oc ")";
    os oc " => ";
    os oc "("; th0_term oc v0; os oc " = "; th0_term oc v1; os oc "))"
  end

fun th0_thmdef_boolext oc =
  let val th0name = name_thm (hocaster_extra,"boolext") in
    os oc (thfpar ^ th0name ^ ",axiom,"); th0_boolext oc; osn oc ")."
  end

fun th0_thmdef_caster oc (name,thm) =
  let 
    val (cj,defl) = fof_translate_thm thm
    val _ = if null defl then () else raise ERR "th0_thmdef_caster" ""
  in
    os oc (thfpar ^ name_thm (hocaster_extra,name) ^ ",axiom,");
    th0_formula oc cj; osn oc ")."
  end

fun th0_thmdef_combin oc (name,tm) =
  let val th0name = name_thm (hocaster_extra,name) in
    os oc (thfpar ^ th0name ^ ",axiom,"); th0_formula oc tm; osn oc ")."
  end

fun th0_thmdef_extra oc = 
  (
  app (th0_thmdef_caster oc) app_axioml;
  th0_thmdef_boolext oc;
  app (th0_thmdef_caster oc) p_axioml;
  app (th0_thmdef_combin oc) combin_axioml;
  app (th0_logicdef oc) logic_l1;
  app (th0_quantdef oc) quant_l2
  )

(* todo: declare types as constants in domains *)

val tyopl_extra = tyopl_of_tyl [``:bool -> bool``]

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

fun th0_arityeq oc (cv,a) = 
  if a = 0 then () else
  let 
    val th0name = "arityeq" ^ its a ^ escape "." ^ namea_cv (cv,a) 
    val tm = mk_arity_eq (cv,a)
  in
    os oc (thfpar ^ th0name ^ ",axiom,"); th0_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

val th0_bushy_dir = hh_dir ^ "/export_th0_bushy"
fun th0_export_bushy thyl =
  let 
    val thyorder = sorted_ancestry thyl 
    val dir = th0_bushy_dir
    fun f thy =
      write_thy_bushy dir fof_translate_thm uniq_cvdef_mgc 
       (tyopl_extra,cval_extra)
       (th0_tyopdef_extra, th0_tyopdef, th0_cvdef_extra, th0_polyw_cvdef, 
        th0_thmdef_extra, th0_arityeq, th0_thmdef)
      thy
  in
    mkDir_err dir; app f thyorder
  end

val th0_chainy_dir = hh_dir ^ "/export_th0_chainy"
fun th0_export_chainy thyl =
  let 
    val thyorder = sorted_ancestry thyl 
    val dir = th0_chainy_dir
    fun f thy =
      write_thy_chainy dir thyorder fof_translate_thm uniq_cvdef_mgc
        (tyopl_extra,cval_extra)
        (th0_tyopdef_extra, th0_tyopdef, th0_cvdef_extra, th0_polyw_cvdef, 
         th0_thmdef_extra, th0_arityeq, th0_thmdef)
      thy
  in
    mkDir_err dir; app f thyorder
  end

(* load "hhExportTh0"; open hhExportTh0; th0_export_bushy ["bool"]; *)

end (* struct *)
