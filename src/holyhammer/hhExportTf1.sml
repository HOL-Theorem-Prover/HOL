(* ========================================================================= *)
(* FILE          : hhExportTf1.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTf1 :> hhExportTf1 =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportTf1"

val tffpar = "tff("

(* -------------------------------------------------------------------------
   TF1 type
   ------------------------------------------------------------------------- *)

fun fo_fun oc (s,f_arg,argl) = 
  if null argl then os oc s else 
  (os oc s; os oc "("; oiter oc "," f_arg argl; os oc ")")

fun tf1_utype oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let 
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop (Thy,Tyop)
    in
      fo_fun oc (tyops, tf1_utype, Args)
    end

fun tf1_type oc (ty,a) = case strip_funty_n a ty of
    [] => raise ERR "tf1_type" ""
  | [imty] => tf1_utype oc imty
  | [uty,imty] => 
    (os oc "("; tf1_utype oc uty; os oc " > "; tf1_utype oc imty;
     os oc ")")
  | l =>
    (os oc "(("; 
     oiter oc " * " tf1_utype (butlast l); os oc ") > "; 
     tf1_utype oc (last l); os oc ")")

(* -------------------------------------------------------------------------
   TF1 quantifier
   ------------------------------------------------------------------------- *)

fun tf1_vty oc v = (os oc (namea_v (v,0) ^ ":"); tf1_utype oc (type_of v))

fun tf1_quant_vl oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " tf1_vty vl; os oc "]: ")

fun tf1_forall_tyvarl_tm oc tm =
  let
    val tvl = dict_sort Type.compare (type_vars_in_term tm)
    fun f oc x = os oc (name_vartype x ^ ":" ^ ttype)
  in
    if null tvl then () else (os oc "!["; oiter oc ", " f tvl; os oc "]: ")
  end

fun tf1_forall_tyvarl_ty oc ty =
  let 
    val tvl = dict_sort Type.compare (type_vars ty) 
    fun f oc x = os oc (name_vartype x ^ ":" ^ ttype)
  in
    if null tvl then () else (os oc "!>["; oiter oc ", " f tvl; os oc "]: ")
  end

(* -------------------------------------------------------------------------
    TF1 term
   ------------------------------------------------------------------------- *)

fun tf1_fun oc (s,f_tyarg,f_arg,tyargl,argl) =
  if null tyargl andalso null argl then os oc s 
  else if null tyargl then 
    (os oc s; os oc "("; oiter oc "," f_arg argl; os oc ")")
  else if null argl then
    (os oc s; os oc "("; oiter oc "," f_tyarg tyargl; os oc ")")
  else
    (
    os oc s; os oc "(";
    oiter oc "," f_tyarg tyargl; os oc ",";
    oiter oc "," f_arg argl; os oc ")"
    )

fun tf1_term oc tm =
  if is_tptp_bv tm then os oc (namea_v (tm,0)) else
  let 
    val (rator,argl) = strip_comb tm
      handle _ => raise ERR "tf1_term" "abstraction"
    val arity = length argl
    val tyargl = 
      if is_app rator then typearg_of_app rator
      else if is_tptp_fv rator then typearg_of_fv rator
      else typearg_of_c rator
    val cvs = namea_cv (rator,arity)
  in
    tf1_fun oc (cvs, tf1_utype, tf1_term, tyargl, argl) 
  end

(* -------------------------------------------------------------------------
    TF1 formula
   ------------------------------------------------------------------------- *)

fun tf1_pred oc tm =
  if is_forall tm then tf1_quant oc "!" (strip_forall tm)
  else if is_exists tm then tf1_quant oc "?" (strip_exists tm)
  else if is_conj tm then tf1_binop oc "&" (dest_conj tm)
  else if is_disj tm then tf1_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then tf1_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "(~ "; tf1_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r
      then tf1_binop oc "<=>" (l,r)
      else (os oc "("; tf1_term oc l; os oc " = ";  
            tf1_term oc r; os oc ")")
    end
  else (os oc "p("; tf1_term oc tm; os oc ")")
and tf1_binop oc s (l,r) =
  (os oc "("; tf1_pred oc l; os oc (" " ^ s ^ " "); tf1_pred oc r; os oc ")")
and tf1_quant oc s (vl,bod) = 
  (tf1_quant_vl oc s vl; tf1_pred oc bod)

fun tf1_formula oc tm = (tf1_forall_tyvarl_tm oc tm; tf1_pred oc tm)

(* -------------------------------------------------------------------------
   Term-level logical operators equations
   ------------------------------------------------------------------------- *)

fun tf1_logicformula oc (thy,name) = 
  let 
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val vl = free_vars_lr tm 
  in
    tf1_forall_tyvarl_tm oc tm; tf1_quant_vl oc "!" vl;
    os oc "(p("; tf1_term oc tm ; os oc ") <=> "; tf1_pred oc tm; os oc ")"
  end

fun tf1_logicdef oc (thy,name) =
  (os oc (tffpar ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
   tf1_logicformula oc (thy,name); osn oc ").")

fun tf1_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val (tm,_) = tff_translate_thm thm
  in
    os oc (tffpar ^ escape ("quantdef." ^ name) ^ ",axiom,"); 
    tf1_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
    TF1 definitions
   ------------------------------------------------------------------------- *)

fun tf1_ttype arity =
  if arity = 0 then ttype else
  if arity = 1 then String.concatWith " > " [ttype,ttype] else
  "(" ^ String.concatWith " * " (List.tabulate (arity, fn _ => ttype)) ^ ")"
  ^ " > " ^ ttype 

fun tf1_tyopdef oc ((thy,tyop),arity) =
  let val tf1name = name_tyop (thy,tyop) in
    os oc (tffpar ^ tf1name ^ ",type," ^ tf1name ^ ":");
    os oc (tf1_ttype arity); osn oc ")."
  end

fun tf1_cvdef oc (tm,a) =
  let val (tf1name,ty) = (namea_cv (tm,a), type_of tm) in
    os oc (tffpar ^ tf1name ^ ",type," ^ tf1name ^ ":");
    tf1_forall_tyvarl_ty oc ty; tf1_type oc (ty,a); osn oc ")."
  end

fun tf1_thmdef role oc (thy,name) =
  let 
    val thm = DB.fetch thy name
    val (cj,defl) = tff_translate_thm thm
    val tf1name = name_thm (thy,name)
    fun f i def = 
      (
      os oc (tffpar ^ escape ("def" ^ its i ^ ".") ^ tf1name ^ ",axiom,");
      tf1_formula oc def; osn oc ")."
      )
  in
    ignore (mapi f defl);
    os oc (tffpar ^ tf1name ^ "," ^ role ^ ",");
    tf1_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Higher-order constants
   ------------------------------------------------------------------------- *)

fun tf1_cdef_app oc = 
  let
    val ty = type_of (prim_mk_const {Thy = "bool", Name = "LET"})
    val tf1name = namea_v (mk_var ("app",bool),2) (* bool is dummy type *)
  in
    os oc (tffpar ^ tf1name ^ ",type," ^ tf1name ^ ":");
    tf1_forall_tyvarl_ty oc ty; tf1_type oc (ty,2); osn oc ")."
  end

fun tf1_cdef_p oc = 
  let val tf1name = "p" in
    os oc (tffpar ^ tf1name ^ ",type," ^ tf1name ^ ":");
    tf1_utype oc bool; os oc " > $o"; osn oc ")."
  end

fun tf1_cvdef_extra oc = (tf1_cdef_app oc; tf1_cdef_p oc) 

(* -------------------------------------------------------------------------
   Higher-order theorems
   ------------------------------------------------------------------------- *)

val hocaster_extra = "extra-ho" (* fake theory for these theorems *)

fun tf1_boolext oc = 
  let val (v0,v1) = (mk_var ("V0",bool),mk_var ("V1",bool)) in
    tf1_quant_vl oc "!" [v0,v1];
    os oc "(("; tf1_pred oc v0; oc os " <=> "; tf1_pred oc v1; os oc ")";
    os oc " => ";
    os oc "("; tf1_term oc v0; oc os " = "; tf1_term oc v1; os oc "))"
  end

fun tf1_thmdef_boolext oc =
  let val tf1name = name_thm (hocaster_extra,"boolext") in
    os oc (tffpar ^ tf1name ^ ",axiom,"); tf1_boolext oc; osn oc ")."
  end

fun tf1_thmdef_caster oc (name,thm) =
  let 
    val (cj,defl) = tff_translate_thm thm
    val _ = if null defl then () else raise ERR "tf1_thmdef_caster" ""
  in
    os oc (tffpar ^ name_thm (hocaster_extra,name) ^ ",axiom,");
    tf1_formula oc cj; osn oc ")."
  end

fun tf1_thmdef_combin oc (name,tm) =
  let val tf1name = name_thm (hocaster_extra,name) in
    os oc (tffpar ^ tf1name ^ ",axiom,"); tf1_formula oc tm; osn oc ")."
  end

fun tf1_thmdef_extra oc = 
  (
  app (tf1_thmdef_caster oc) app_axioml;
  tf1_thmdef_boolext oc;
  app (tf1_thmdef_caster oc) p_axioml;
  app (tf1_thmdef_combin oc) combin_axioml;
  app (tf1_logicdef oc) logic_l1;
  app (tf1_quantdef oc) quant_l2
  )

val tyopl_extra = tyopl_of_tyl [``:bool -> bool``]

val app_p_cval =
  let val tml = map (fst o tff_translate_thm o snd) (app_axioml @ p_axioml) in
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

fun tf1_arityeq oc (cv,a) = 
  if a = 0 then () else
  let 
    val tf1name = "arityeq" ^ its a ^ escape "." ^ namea_cv (cv,a) 
    val tm = mk_arity_eq (cv,a)
  in
    os oc (tffpar ^ tf1name ^ ",axiom,"); tf1_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

fun tf1_tyopdef_extra oc = ()

val tf1_bushy_dir = hh_dir ^ "/export_tf1_bushy"
fun tf1_export_bushy thyl =
  let 
    val thyorder = sorted_ancestry thyl 
    val dir = tf1_bushy_dir
    fun f thy =
      write_thy_bushy dir tff_translate_thm uniq_cvdef_mgc 
       (tyopl_extra,cval_extra)
       (tf1_tyopdef_extra, tf1_tyopdef, tf1_cvdef_extra, tf1_cvdef, 
        tf1_thmdef_extra, tf1_arityeq, tf1_thmdef)
      thy
  in
    mkDir_err dir; app f thyorder
  end

val tf1_chainy_dir = hh_dir ^ "/export_tf1_chainy"
fun tf1_export_chainy thyl =
  let 
    val thyorder = sorted_ancestry thyl 
    val dir = tf1_chainy_dir
    fun f thy =
      write_thy_chainy dir thyorder tff_translate_thm uniq_cvdef_mgc
        (tyopl_extra,cval_extra)
        (tf1_tyopdef_extra, tf1_tyopdef, tf1_cvdef_extra, tf1_cvdef, 
         tf1_thmdef_extra, tf1_arityeq, tf1_thmdef)
      thy
  in
    mkDir_err dir; app f thyorder
  end

(* load "hhExportTf1"; open hhExportTf1; tf1_export_chainy ["arithmetic"]; *)

end (* struct *)
