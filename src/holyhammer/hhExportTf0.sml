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
type thmid = string * string
val tffpar = "tff("

(* -------------------------------------------------------------------------
   TF0 types
   ------------------------------------------------------------------------- *)

fun tf0def_name_ttype oc tf0name =
  osn oc (tffpar ^ tf0name ^ ",type," ^ tf0name ^ ":" ^ ttype ^ ").")

fun tf0def_ttype_mono oc ty =
  let val tf0name = name_tyu_mono ty in
    tf0def_name_ttype oc tf0name
  end

val (utype,dtype,dutype) = ("u","d","du")
val sortl = [utype,dtype,dutype]

fun fo_fun oc (s,f_arg,argl) = 
  if null argl then os oc s else 
  (os oc s; os oc "("; oiter oc "," f_arg argl; os oc ")")

fun tf0_ty_poly oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop (Thy,Tyop)
    in
      fo_fun oc (tyops, tf0_ty_poly, Args)
    end

(* -------------------------------------------------------------------------
   TF0 quantifier
   ------------------------------------------------------------------------- *)

fun tf0_forall_tyvarl_tm oc tm =
  let
    val tvl = dict_sort Type.compare (type_vars_in_term tm)
    fun f oc x = os oc (name_vartype x ^ ":" ^ dtype)
  in
    if null tvl then () else (os oc "!["; oiter oc ", " f tvl; os oc "]: ")
  end

(* mono *)
fun tf0_quantv_mono oc v = 
  let val ty = type_of v in
    os oc (namea_v (v,0) ^ ":"); os oc (name_tyu_mono ty)
  end

fun tf0_quant_vl_mono oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " tf0_quantv_mono vl; os oc "]: ")

(* poly *)
fun tf0_quantv_poly oc v = 
  let val ty = type_of v in
    os oc (namea_v (v,0) ^ ":"); os oc utype
  end

fun tf0_quant_vl_poly oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " tf0_quantv_poly vl; os oc "]: ")

(* adaptive *)
fun tf0_quantv oc v = 
  let val ty = type_of v in
    os oc (namea_v (v,0) ^ ":"); 
    if polymorphic ty then os oc utype else os oc (name_tyu_mono ty)
  end

fun tf0_quant_vl oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " tf0_quantv vl; os oc "]: ")

(* -------------------------------------------------------------------------
   TF0 term
   ------------------------------------------------------------------------- *)

fun iname oc ty = os oc ("i_" ^ name_tyu_mono ty)
fun jname oc ty = os oc ("j_" ^ name_tyu_mono ty)

fun s_of oc (ty,f_tm) =
  (os oc "s("; tf0_ty_poly oc ty; os oc ","; f_tm oc; os oc ")")

fun tf0_term_poly oc tm =
  let 
    val (rator,argl) = strip_comb tm 
    fun f_tm oc = 
      fo_fun oc (namea_obj_poly (rator,length argl), tf0_iterm, argl)
  in  
    s_of oc (type_of tm,f_tm) 
  end
and tf0_term_mono oc tm =
  let val (rator,argl) = strip_comb tm in
    fo_fun oc (namea_obj_mono (rator,length argl), tf0_jterm, argl)
  end
and tf0_iterm oc tm =
  let 
    val (rator,argl) = strip_comb tm
    val ty = type_of tm
  in
    if polymorphic (type_of rator)
    then tf0_term_poly oc tm
    else 
      let fun f_tm oc = 
        (iname oc ty; os oc "("; tf0_term_mono oc tm; os oc ")")
      in
        s_of oc (ty,f_tm)
      end
  end
and tf0_jterm oc tm =
  let
    val (rator,argl) = strip_comb tm
    val ty = type_of tm
  in
    if polymorphic (type_of rator)
    then (jname oc ty; os oc "("; tf0_term_poly oc tm; os oc ")")
    else tf0_term_mono oc tm
  end


(* test term 
f 0 = f_poly (s(num,(i(0))))
load "hhExportTf0"; open hhExportTf0;
val tm =  ``(V + 0) + (zero (X:'a))``; 
tf0_term_mono TextIO.stdOut tm;
tf0_term_poly TextIO.stdOut tm;
*)

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
      else 
        if polymorphic (type_of l) 
        then 
          (os oc "("; tf0_iterm oc l; os oc " = "; tf0_iterm oc r; os oc ")")
        else
          (os oc "("; tf0_jterm oc l; os oc " = "; tf0_jterm oc r; os oc ")")
    end
  else (os oc "p("; tf0_jterm oc tm; os oc ")")
and tf0_binop oc s (l,r) =
  (os oc "("; tf0_pred oc l; os oc (" " ^ s ^ " "); 
   tf0_pred oc r; os oc ")")
and tf0_quant oc s (vl,bod) =
  (tf0_quant_vl oc s vl; tf0_pred oc bod)

fun tf0_formula oc tm = (tf0_forall_tyvarl_tm oc tm; tf0_pred oc tm)

(* test term 
load "hhExportTf0"; open hhExportTf0;
val tm = ``!V0 V1. (V0 + 0) + (zero (V1:'a)) = 0``; 
tf0_formula TextIO.stdOut tm;
tf0_term_poly TextIO.stdOut tm;
tf0_term TextIO.stdOut tm;
*)


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
    os oc "(p("; tf0_jterm oc tm ; os oc ") <=> "; tf0_pred oc tm; os oc ")"
  end

fun tf0_logicdef oc (thy,name) =
  (os oc (tffpar ^ escape ("reserved.logic." ^ name) ^ ",axiom,"); 
   tf0_logicformula oc (thy,name); osn oc ").")

fun tf0_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val (tm,_) = translate_thm thm
  in
    os oc (tffpar ^ escape ("reserved.quant." ^ name) ^ ",axiom,"); 
    tf0_formula oc tm; osn oc ")."
  end


(* -------------------------------------------------------------------------
   I-J axioms
   ------------------------------------------------------------------------- *)

fun tf0def_iname oc ty = 
  (
  os oc tffpar; iname oc ty; os oc ",type,"; iname oc ty; os oc ":";
  os oc (name_tyu_mono ty ^ " > u"); osn oc ")."
  )

fun tf0def_jname oc ty = 
  (
  os oc tffpar; jname oc ty; os oc ",type,"; jname oc ty; os oc ":";
  os oc ("du > " ^ name_tyu_mono ty); osn oc ")."
  )

(* for monomorphic types *)
fun ij_axiom oc ty =
  let 
    val v = mk_var ("V0",ty)
    val ty = type_of v 
    fun f_tm_lhs oc =
      (iname oc ty; os oc "("; jname oc ty; os oc "("; tf0_term_poly oc v;
       os oc "))")
  in
    tf0_quant_vl_poly oc "!" [v];
    os oc "("; 
    s_of oc (ty,f_tm_lhs); os oc " = "; tf0_term_poly oc v;
    os oc ")"
  end

fun tf0def_ij_axiom oc ty =
  (os oc (tffpar ^ escape "ij." ^ name_tyu_mono ty ^ ",axiom,");
   ij_axiom oc ty; osn oc ").")

(* 
  load "hhExportTf0"; open hhExportTf0; 
  ij_axiom TextIO.stdOut ``:num``;
*)

(* for monomorphic types *)
fun ji_axiom oc ty =
  let val v = mk_var ("V0",ty) in
    tf0_quant_vl oc "!" [v]; os oc "("; 
      jname oc ty; os oc "("; tf0_iterm oc v; os oc ")";
      os oc " = "; os oc (namea_obj_mono (v,0));
    os oc ")"
  end

fun tf0def_ji_axiom oc ty =
  (os oc (tffpar ^ escape "ji." ^ name_tyu_mono ty ^ ",axiom,");
   ji_axiom oc ty; osn oc ").")

(* 
  load "hhExportTf0"; open hhExportTf0; 
  ji_axiom TextIO.stdOut ``:num``;
*)


(* -------------------------------------------------------------------------
   TF0 definitions
   ------------------------------------------------------------------------- *)

(* Types *)
fun tf0_tyop_poly a =
  if a <= 0 then dtype 
  else if a = 1 then dtype ^ " > " ^ dtype 
  else 
    "(" ^ String.concatWith " * " (List.tabulate (a,fn _ => dtype)) ^ ")"
    ^ " > " ^ dtype

fun tf0def_tyop_poly oc ((thy,tyop),a) = 
  let val tf0name = name_tyop (thy,tyop) in
    (os oc (tffpar ^ tf0name ^ ",type," ^ tf0name ^ ":");
     os oc (tf0_tyop_poly a); osn oc ").")
  end

(* Constants *)
fun tf0_fun_sort a =
  if a <= 0 then utype 
  else if a = 1 then dutype ^ " > " ^ utype 
  else 
    "(" ^ String.concatWith " * " (List.tabulate (a,fn _ => dutype)) ^ ")"
    ^ " > " ^ utype

fun tf0def_objnamed_poly oc (name,a) =
  (os oc (tffpar ^ name ^ ",type," ^ name ^ ":");
   os oc (tf0_fun_sort a); osn oc ").")

fun tf0def_obj_poly oc (tm,a) =
  tf0def_objnamed_poly oc (namea_cv (tm,a), a) 

fun namea_ty_mono (ty,arity) = case strip_funty_n arity ty of
    [] => raise ERR "namea_ty_mono" ""
  | [a] => name_tyu_mono a
  | [a,b] => name_tyu_mono a ^ " > " ^ name_tyu_mono b
  | l => "(" ^ String.concatWith " * " (map name_tyu_mono (butlast l)) 
    ^ ") > " ^ name_tyu_mono (last l)

fun tf0def_objnamed_mono oc (name,ty,a) =
  (os oc (tffpar ^ name ^ ",type," ^ name ^ ":");
   os oc (namea_ty_mono (ty,a)); osn oc ").")

fun tf0def_obj_mono oc (tm,a) =
  tf0def_objnamed_mono oc (namea_obj_mono (tm,a), type_of tm, a)


(* Theorems *)
fun tf0def_thm role oc (thy,name) =
  let 
    val thm = DB.fetch thy name
    val (cj,defl) = translate_thm thm
    val tf0name = name_thm (thy,name)
    fun f i def = 
      (
      os oc (tffpar ^ name_def i tf0name ^ ",axiom,");
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
    tf0def_objnamed_poly oc (tf0name,a)
  end

fun tf0_cdef_p oc =
  let val tf0name = "p" in
    os oc (tffpar ^ tf0name ^ ",type," ^ tf0name ^ ":");
    os oc (name_tyu_mono bool ^ " > $o"); osn oc ")."
  end

fun tf0_cdef_s oc =
  let val tf0name = "s" in
    os oc (tffpar ^ tf0name ^ ",type," ^ tf0name ^ ":");
    os oc ("(" ^ dtype ^ " * " ^ utype ^ ") > " ^ dutype); osn oc ")."
  end 

fun tf0_cvdef_extra oc =
  (tf0_cdef_s oc; tf0_cdef_app oc; tf0_cdef_p oc) 

(* -------------------------------------------------------------------------
   Higher-order theorems
   ------------------------------------------------------------------------- *)

fun tf0_boolext oc = 
  let val (v0,v1) = (mk_var ("V0",bool),mk_var ("V1",bool)) in
    tf0_quant_vl oc "!" [v0,v1];
    os oc "(("; tf0_pred oc v0; os oc " <=> "; tf0_pred oc v1; os oc ")";
    os oc " => ";
    os oc "("; tf0_jterm oc v0; os oc " = "; tf0_jterm oc v1; os oc "))"
  end

fun tf0def_thm_boolext oc =
  let val tf0name = escape "reserved.ho.boolext" in
    os oc (tffpar ^ tf0name ^ ",axiom,"); tf0_boolext oc; osn oc ")."
  end

fun tf0def_thm_caster oc (name,thm) =
  let 
    val (cj,defl) = translate_thm thm
    val _ = if null defl then () else raise ERR "tf0def_thm_caster" ""
    val tf0name = escape ("reserved.ho." ^ name)
  in
    os oc (tffpar ^ tf0name ^ ",axiom,"); tf0_formula oc cj; osn oc ")."
  end

fun tf0def_thm_combin oc (name,tm) =
  let val tf0name = escape ("reserved.ho." ^ name) in
    os oc (tffpar ^ tf0name ^ ",axiom,"); tf0_formula oc tm; osn oc ")."
  end

fun tf0def_thm_extra oc = 
  (
  app (tf0def_thm_caster oc) app_axioml;
  tf0def_thm_boolext oc;
  app (tf0def_thm_caster oc) p_axioml;
  app (tf0def_thm_combin oc) combin_axioml;
  app (tf0_logicdef oc) logic_l1;
  app (tf0_quantdef oc) quant_l2
  )

(* polymorphic *)
val app_p_cval =
  let val tml = map (fst o translate_thm o snd) (app_axioml @ p_axioml) in
    mk_fast_set tma_compare (List.concat (map collect_arity_noapp tml)) 
  end

val combin_cval = 
  let val tml = map snd combin_axioml in
    mk_fast_set tma_compare (List.concat (map collect_arity_noapp tml)) 
  end

(* -------------------------------------------------------------------------
   Monomorphism equations (including app)
   ------------------------------------------------------------------------- *)

fun tf0_monoeq oc (cv,a) =
  let val (tm,vl) = apply_cva (cv,a) in
    tf0_quant_vl oc "!" vl;
    os oc "("; tf0_iterm oc tm; os oc " = "; tf0_term_poly oc tm; os oc ")"
  end

fun tf0def_monoeq oc (cv,a) =
  let val tf0name = escape "monoeq." ^ namea_obj_mono (cv,a) in
    os oc (tffpar ^ tf0name ^ ",axiom,"); tf0_monoeq oc (cv,a); osn oc ")."
  end

(* -------------------------------------------------------------------------
   Arity equations
   ------------------------------------------------------------------------- *)

fun tf0def_arityeq oc (cv,a) =
  if a = 0 then () else
  let 
    val tf0name = name_arityeq (cv,a)
    val tm = mk_arity_eq (cv,a)
  in
    os oc (tffpar ^ tf0name ^ ",axiom,"); tf0_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

fun has_tyarg (cv,_) = 
  let val tyargl = typearg_of_cvapp cv in not (null tyargl) end

(* atom *)
fun collect_atoml thmidl =
  let fun f x = 
    let val (formula,defl) = translate_thm (uncurry DB.fetch x) in 
      mk_term_set (List.concat (map atoms (formula :: defl)))
    end
  in
    mk_term_set (List.concat (map f thmidl))
  end

(* objects (operators) *)
fun all_obja_aux tm =
  let val (oper,argl) = strip_comb tm in 
    (oper,length argl) :: List.concat (map all_obja_aux argl)
  end

fun all_obja tm = mk_fast_set tma_compare (all_obja_aux tm)

fun all_obja_tml tml = 
  mk_fast_set tma_compare (List.concat (map all_obja tml))

(* constant *)
val cval_extra = boolop_cval @ combin_cval @ app_p_cval

fun prepare_arityeq tml =
 let
   val objal = all_obja_tml tml
   val cval = filter (fn (x,_) => is_tptp_fv x orelse is_const x) objal
   val cval_arityeq = mk_fast_set tma_compare (cval @ cval_extra)
   val tml_arityeq  = mk_term_set (map mk_arity_eq  
      (filter (fn x => snd x <> 0) cval_arityeq))
   val atoml_arityeq  = mk_term_set (List.concat (map atoms tml_arityeq)) 
 in
   (cval_arityeq, atoml_arityeq)
 end

fun prepare_cval_poly objal =
  let val l = filter (fn (x,_) => is_tptp_fv x orelse is_const x) objal in
    uniq_cvdef_mgc (mk_fast_set tma_compare (l @ cval_extra))
  end

fun prepare_cval_mono objal =
  let val l = 
    filter (fn (x,_) => is_tptp_fv x orelse is_const x orelse is_app x) objal
  in
    filter (not o polymorphic o type_of o fst) 
      (mk_fast_set tma_compare (l @ cval_extra))
  end

(* types *)
val tyopl_extra_poly = tyopset_of_tyl [``:bool -> bool``]

val tya_compare = cpl_compare Type.compare Int.compare

fun fo_subterms tm = 
  let val (oper,argl) = strip_comb tm in
    tm :: List.concat (map fo_subterms argl)
  end

fun fo_subterms_tml atoml =
  mk_term_set (List.concat (map fo_subterms atoml))

fun prepare_tyopl_poly subtml = 
  let val l = tyopset_of_tyl (map type_of subtml) in
    mk_fast_set ida_compare (tyopl_extra_poly @ l)
  end

fun prepare_tyul_mono subtml =
  let val tyl = mk_type_set (bool :: (map type_of subtml)) in
    filter (not o polymorphic) tyl
  end

(* -------------------------------------------------------------------------
   Write problem
   ------------------------------------------------------------------------- *)

fun tf0_preambule oc atoml1 =
  let
    val (cval_arityeq, atoml_arityeq) = prepare_arityeq atoml1
    val atoml2 = atoml_arityeq @ atoml1
    val objal = all_obja_tml atoml2
    val cval_poly = prepare_cval_poly objal
    val cval_mono = prepare_cval_mono objal
    val subtml = fo_subterms_tml atoml2
    val tyopl_poly = prepare_tyopl_poly subtml
    val tyul_mono = prepare_tyul_mono subtml
  in
    app (tf0def_name_ttype oc) sortl;
    app (tf0def_ttype_mono oc) tyul_mono;
    app (tf0def_tyop_poly oc) tyopl_poly;
    tf0_cvdef_extra oc;
    app (tf0def_obj_poly oc) cval_poly;
    app (tf0def_obj_mono oc) cval_mono;
    app (tf0def_iname oc) tyul_mono; 
    app (tf0def_jname oc) tyul_mono;
    tf0def_thm_extra oc;
    app (tf0def_ij_axiom oc) tyul_mono; 
    app (tf0def_ji_axiom oc) tyul_mono;
    app (tf0def_arityeq oc) cval_arityeq;
    app (tf0def_monoeq oc) (filter has_tyarg cval_mono)
  end

fun tf0_write_pb dir (thmid,(depthyl,depl)) =
  let 
    val _ = mkDir_err dir
    val file = dir ^ "/" ^ name_thm thmid ^ ".p"
    val oc  = TextIO.openOut file
    val atoml1 = collect_atoml (thmid :: depl)
  in
    (
    app (fn x => osn oc ("include('" ^ x ^ ".ax').")) depthyl;
    tf0_preambule oc atoml1;
    app (tf0def_thm "axiom" oc) depl; 
    tf0def_thm "conjecture" oc thmid;
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(* 
load "hhExportTf0"; open hhExportTf0; 
val thmid = ("arithmetic","ADD1");
val depl = valOf (hhExportLib.depo_of_thmid thmid);
val dir = HOLDIR ^ "/src/holyhammer/export_tf0_test";
tf0_write_pb dir (thmid,depl);
*)

(* -------------------------------------------------------------------------
   Bushy problems
   ------------------------------------------------------------------------- *)

fun write_thy_bushy dir thy =
  let val cjdepl = bushy_dep thy (DB.theorems thy) in
    print (thy ^ " "); app (tf0_write_pb dir) cjdepl
  end

fun tf0_export_bushy dir thyl =
  let val thyorder = sorted_ancestry thyl in
    mkDir_err dir; app (write_thy_bushy dir) thyorder
  end

(* -------------------------------------------------------------------------
   Chainy problems
   ------------------------------------------------------------------------- *)

fun tf0_export_thy dir thy =
  let
    val _ = mkDir_err dir
    val file  = dir ^ "/" ^ thy ^ ".ax"
    val oc  = TextIO.openOut file
    val thmidl = thmidl_in_thy thy
    val atoml = collect_atoml thmidl
  in
    (
    tf0_preambule oc atoml;
    app (tf0def_thm "axiom" oc) thmidl;
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy dir thyorder thy =
  let val cjdepl = chainy_dep thyorder thy (DB.theorems thy) in
    print (thy ^ " "); app (tf0_write_pb dir) cjdepl
  end

fun tf0_export_chainy dir thyl =
  let val thyorder = sorted_ancestry thyl in
    mkDir_err dir;
    app (tf0_export_thy (dir ^ "/theories")) thyorder;
    app (write_thy_chainy (dir ^ "/problems") thyorder) thyorder
  end

(* -------------------------------------------------------------------------
   Export standard library
   ------------------------------------------------------------------------- *)

(*
load "hhExportTf0"; open hhExportTf0; 
load "tttUnfold"; tttUnfold.load_sigobj ();
val thyl = ancestry (current_theory ());
val bushydir = HOLDIR ^ "/src/holyhammer/tf0_bushy";
tf0_export_bushy bushydir thyl; 
val chainydir = HOLDIR ^ "/src/holyhammer/tf0_chainy";
tf0_export_chainy chainydir thyl;
*)

end (* struct *)
