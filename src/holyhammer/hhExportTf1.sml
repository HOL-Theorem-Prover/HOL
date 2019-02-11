(* ========================================================================= *)
(* FILE          : hhExportTf1.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTf1 :> hhExportTf1 =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportTf1"

val tffpar = "tff("
fun tf1_prep_thm thm = 
  let val tml = translate_tm (concl (DISCH_ALL thm)) in
    (hd tml, rev (tl tml))
  end

(* -------------------------------------------------------------------------
   TF1 types,terms,formulas
   ------------------------------------------------------------------------- *)

fun fo_fun oc (s,f_arg,argl) = 
  if null argl then os oc s else 
  (os oc s; os oc "("; oiter oc "," f_arg argl; os oc ")")

fun tf1_fun oc (s,f_tyarg,f_arg,tyargl,argl) =
  if null argl then raise ERR "tf1_fun" "" else
  (
  os oc s; os oc "(";
  oiter oc "," f_tyarg tyargl;
  if null tyargl then () else os oc ",";
  oiter oc "," f_arg argl; os oc ")"
  )

fun tf1_utype oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let 
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop (Thy,Tyop)
    in
      fo_fun oc (tyops, tf1_utype, Args)
    end

fun tf1_type arity oc ty = case strip_funty_n arity ty of
    [] => raise ERR "tf1_type" ""
  | [imty] => tf1_utype oc imty
  | [imty,uty] => 
    (os oc "("; tf1_utype oc uty; os oc " > "; tf1_utype oc imty;
     os oc ")")
  | l =>
    (os oc "(("; 
     oiter oc " * " tf1_utype (butlast l); os oc ") > "; 
     tf1_utype oc (last l); os oc ")")

fun tf1_vty oc v =  
  let val (_,ty) = dest_var v in 
    os oc (namea_v 0 v ^ ":"); tf1_utype oc ty 
  end

fun maxarity_of c = 
  let
    val (thy,name) = cid_of c
    val genc = prim_mk_const {Thy = thy, Name = name}
    val ty = type_of genc
  in
    length (snd (strip_funty ty))
  end

fun tf1_term oc tm =
  if is_var tm then os oc (namea_v 0 tm)
  else if is_const tm then os oc (namea_c 0 tm)
  else if is_comb tm then
    let 
      val (rator_aux,argl_aux) = strip_comb tm 
      val newtm =
        if is_const rator_aux andalso maxarity_of rator_aux < length argl_aux
        then (rhs o concl o APP_CONV_AUX) tm
        else tm
      val (rator,argl) = strip_comb newtm
      val arity = length argl
      val tyargl = 
        if is_var rator then  
          if fst (dest_var rator) = "app" 
          then typearg_of_appvar rator
          else typearg_of_var rator
        else typearg_of_const rator
      val cvs = namea_cv arity rator
    in
      

      tf1_fun oc (cvs, tf1_utype, tf1_term, tyargl,argl) 
    end
  else raise ERR "tf1_term" "abstraction"

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
  (os oc "("; tf1_pred oc l; os oc (" " ^ s ^ " "); 
   tf1_pred oc r; os oc ")")
and tf1_quant oc s (vl,bod) =
  (os oc s; os oc "["; oiter oc ", " tf1_vty vl;
   os oc "]: "; tf1_pred oc bod)

fun tf1_formula oc tm =
  let 
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith ", " tvls
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    tf1_pred oc tm
  end

(* -------------------------------------------------------------------------
   Logical operators equations with term level counterpart.
   ------------------------------------------------------------------------- *)

fun tf1_logicformula oc (thy,name) = 
  let 
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith ", " tvls
    val vl = free_vars_lr tm 
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    os oc "!["; oiter oc ", " tf1_vty vl; os oc "]: ";
    os oc "("; tf1_term oc tm ; os oc " <=> "; tf1_pred oc tm; os oc ")"
  end

fun tf1_logicdef oc (thy,name) =
  (
  os oc (tffpar ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
  tf1_logicformula oc (thy,name); osn oc ")."
  )

fun tf1_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val (tm,_) = tf1_prep_thm thm
  in
    os oc (tffpar ^ escape ("quantdef." ^ name) ^ ",axiom,"); 
    tf1_formula oc tm; osn oc ")."
  end

fun tf1_boolopdef oc (thy,name) = 
  let
    val l1 = map cid_of [``$/\``,``$\/``,``$~``,``$==>``,
      ``$= : 'a -> 'a -> bool``]
    val l2 = map cid_of [``$! : ('a -> bool) -> bool``,
      ``$? : ('a -> bool) -> bool``]
  in
    if mem (thy,name) l1 then tf1_logicdef oc (thy,name)
    else if mem (thy,name) l2 then tf1_quantdef oc (thy,name)
    else ()
  end

(* -------------------------------------------------------------------------
    TF1 definitions
   ------------------------------------------------------------------------- *)

fun tf1_ttype arity =
  if arity <= 1 then String.concatWith " > " [ttype,ttype] else
  "(" ^ String.concatWith " * " (List.tabulate (arity, fn _ => ttype)) ^ ")"
  ^ " > " ^ ttype 

fun tf1_tyopdef oc ((thy,tyop),arity) =
  let val tf1name = name_tyop (thy,tyop) in
    os oc (tffpar ^ tf1name ^ ",type," ^ tf1name ^ ":");
    os oc (tf1_ttype arity); osn oc ")."
  end

fun tf1_tyquant_type oc arity ty =
  let 
    val tvl = dict_sort Type.compare (type_vars ty) 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith "," tvls
  in
    if null tvl then () else os oc ("!>[" ^ s ^ "]: ");
    tf1_type arity oc ty
  end

fun tf1_vdef_arity oc (v,arity) =
  if fst (dest_var v) = "app" then () else 
  let 
    val tf1name = namea_v arity v 
    val ty = snd (dest_var v)
  in
    os oc (tffpar ^ tf1name ^ ",type," ^ tf1name ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ").";
    (
    if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq v arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc (tffpar ^ arity_prefix ^ tf1name ^ ",axiom,");
       tf1_formula oc eq; osn oc ").")
    end
    )
  end

fun tf1_vdef oc (v,al) =
  let fun f a = tf1_vdef_arity oc (v,a) in app f al end

fun tf1_cdef_arity oc thy arity c (name,ty) =
  let val tf1name = namea_cid arity (thy,name) in
    os oc (tffpar ^ tf1name ^ ",type," ^ tf1name ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ").";
    (if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq c arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc (tffpar ^ arity_prefix ^ tf1name ^ ",axiom,");
       tf1_formula oc eq; osn oc ").")
    end)
  end

fun tf1_cdef oc ((thy,name),al) =
  let
    val c = prim_mk_const {Thy = thy, Name = name}
    val ty = type_of c
    fun f a = tf1_cdef_arity oc thy a c (name,ty)
  in
    app f (List.tabulate (maxarity_of c + 1,I)); 
    tf1_boolopdef oc (thy,name)
  end
  handle _ => raise ERR "tf1_cdef" (name ^ String.concatWith " " (map its al))

fun tf1_thmdef role oc (thy,name) =
  let 
    val thm = DB.fetch thy name
    val (cj,defl) = tf1_prep_thm thm
    val v_al_list = collect_va (list_mk_conj (cj :: defl))
    val tf1name = name_thm (thy,name)
    fun f i def = 
      (
      os oc (tffpar ^ escape ("def" ^ its i ^ ".") ^ tf1name ^ ",axiom,");
      tf1_formula oc def; osn oc ")."
      )
  in
    app (tf1_vdef oc) v_al_list;
    ignore (mapi f defl);
    os oc (tffpar ^ tf1name ^ "," ^ role ^ ",");
    tf1_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Higher-order caster
   ------------------------------------------------------------------------- *)

val hocaster_extra = "hocaster-extra"

val notfalse = EQT_ELIM (last (CONJ_LIST 3 NOT_CLAUSES))

val pcaster_axioml =
  [("truth", TRUTH), ("notfalse", notfalse), ("bool_cases_ax", BOOL_CASES_AX)]

fun tf1_caster_thmdef oc (name,thm) =
  let 
    val (cj,defl) = tf1_prep_thm thm
    val _ = if null defl then () else raise ERR "tf1_caster_thmdef" ""
  in
    os oc (tffpar ^ name_thm (hocaster_extra,name) ^ ",axiom,");
    tf1_formula oc cj; osn oc ")."
  end

fun tf1_caster_app oc = 
  let
    val ty = type_of (prim_mk_const {Thy = "bool", Name = "LET"})
    val tf1name = namea_v 2 (mk_var ("app",bool)) (* bool is dummy type *)
  in
    os oc (tffpar ^ tf1name ^ ",type," ^ tf1name ^ ":");
    tf1_tyquant_type oc 2 ty; osn oc ").";
    tf1_caster_thmdef oc ("eq_ext", EQ_EXT)
  end

fun tf1_caster_p oc = 
  let val tf1name = "p" in
    os oc (tffpar ^ tf1name ^ ",type," ^ tf1name ^ ":");
    tf1_utype oc bool; os oc " > $o"; osn oc ").";
    app (tf1_caster_thmdef oc) pcaster_axioml
  end

fun tf1_combin_thmdef oc (name,tm) =
  let
    val v_al_list = collect_va tm
    val tf1name = name_thm (hocaster_extra,name)
  in
    app (tf1_vdef oc) v_al_list;
    os oc (tffpar ^ tf1name ^ ",axiom,");
    tf1_formula oc tm; osn oc ")."
  end

val combin_conv = 
  STRIP_QUANT_CONV (LHS_CONV APP_CONV_AUX THENC RHS_CONV APP_CONV_AUX)

val lhs_combin_conv = STRIP_QUANT_CONV (LHS_CONV APP_CONV_AUX)

fun mk_combin_thm thmname vname conv =
  let 
    val thm = DB.fetch "combin" thmname
    val tm0 = concl thm
    val oper = (fst o strip_comb o lhs o snd o strip_forall) tm0
    val tm1 = rename_bvarl escape tm0
    val tm2 = (rhs o concl o conv) tm1
    val sub = [{redex = oper, residue = mk_var (vname,type_of oper)}]
  in
    subst sub tm2
  end

val i_thm = mk_combin_thm "I_THM" "combin_i" lhs_combin_conv
val k_thm = mk_combin_thm "K_THM" "combin_k" lhs_combin_conv
val s_thm = mk_combin_thm "S_THM" "combin_s" combin_conv

fun write_hocaster_extra dir = 
  let
    val file = dir ^ "/" ^ hocaster_extra ^ ".ax"
    val oc = TextIO.openOut file
  in
    (
    tf1_caster_app oc; tf1_caster_p oc;
    app (tf1_combin_thmdef oc) 
      [("i_thm",i_thm),("k_thm",k_thm),("s_thm",s_thm)];
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

fun tf1_formulal_of_pb (thmid,depl) = 
  let fun f (a,b) = a :: b in
    mk_term_set (List.concat (
    map (f o tf1_prep_thm o fetch_thm) (thmid :: depl)))
  end

val tf1_bushy_dir = hh_dir ^ "/export_tf1_bushy"
fun tf1_export_bushy thyl =
  let 
    val thyl = sorted_ancestry thyl 
    val dir = tf1_bushy_dir
    val inl = ([],[hocaster_extra],[])
    fun f thy =
      write_thy_bushy dir inl
        (tf1_tyopdef,tf1_cdef,tf1_thmdef)
         tf1_formulal_of_pb thy
  in
    mkDir_err dir; write_hocaster_extra dir; app f thyl
  end

val tf1_chainy_dir = hh_dir ^ "/export_tf1_chainy"
fun tf1_export_chainy oldthyl =
  let 
    val thyl = sorted_ancestry oldthyl
    val dir = tf1_chainy_dir
    val inl = ([],[hocaster_extra],[])
    fun f thy = write_thy_chainy dir inl tf1_thmdef thyl thy 
  in
    mkDir_err dir;
    write_hocaster_extra dir;
    app (write_thytyopdef dir tf1_tyopdef) thyl;
    app (write_thycdef dir tf1_cdef) thyl;
    app (write_thyax dir tf1_thmdef) thyl;
    app f thyl
  end

(* load "hhExportTf1"; open hhExportTf1; tf1_export_bushy ["list"]; *)

end (* struct *)
