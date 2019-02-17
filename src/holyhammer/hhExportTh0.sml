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

fun name_obj_mono cv =
  if is_tptp_bv cv then name_v cv  
  else add_tyargltag (escape "mono." ^ name_cv cv) cv

(* -------------------------------------------------------------------------
   TF0 types
   ------------------------------------------------------------------------- *)

fun name_ty_mono ty = 
  if is_vartype ty then raise ERR "name_ty_mono" "" else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (ty1,ty2) = pair_of_list Args in
          "(" ^ name_ty_mono ty1 ^ " > " ^ name_ty_mono ty2 ^ ")"
        end
      else name_tyu_mono ty
    end

fun th0def_name_ttype oc th0name =
  osn oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":" ^ ttype ^ ").")

fun th0def_ttype_mono oc ty =
  let val th0name = name_tyu_mono ty in
    th0def_name_ttype oc th0name
  end

val (utype,dtype,dutype) = ("u","d","du")
val sortl = [utype,dtype,dutype]

fun ho_fun oc (s,f_arg,argl) = 
  if null argl then os oc s else 
  (os oc "("; os oc s; os oc " @ "; oiter oc " @ " f_arg argl; os oc ")")

fun th0_ty_poly oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop (Thy,Tyop)
    in
      ho_fun oc (tyops, th0_ty_poly, Args)
    end

(* -------------------------------------------------------------------------
   TF0 quantifier
   ------------------------------------------------------------------------- *)

fun th0_forall_tyvarl_tm oc tm =
  let
    val tvl = dict_sort Type.compare (type_vars_in_term tm)
    fun f oc x = os oc (name_vartype x ^ ":" ^ dtype)
  in
    if null tvl then () else (os oc "!["; oiter oc ", " f tvl; os oc "]: ")
  end

(* mono *)
fun th0_quantv_mono oc v = 
  let val ty = type_of v in
    os oc (name_v v ^ ":"); os oc (name_ty_mono ty)
  end

fun th0_quant_vl_mono oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " th0_quantv_mono vl; os oc "]: ")

(* poly *)
fun th0_quantv_poly oc v = 
  let val ty = type_of v in
    os oc (namea_v (v,0) ^ ":"); os oc utype
  end

fun th0_quant_vl_poly oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " th0_quantv_poly vl; os oc "]: ")

(* adaptive *)
fun th0_quantv oc v = 
  let val ty = type_of v in
    if polymorphic ty 
    then th0_quantv_poly oc v
    else th0_quantv_mono oc v
  end

fun th0_quant_vl oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " th0_quantv vl; os oc "]: ")

(* -------------------------------------------------------------------------
   TF0 term
   ------------------------------------------------------------------------- *)

fun iname oc ty = os oc ("i_" ^ name_tyu_mono ty)
fun jname oc ty = os oc ("j_" ^ name_tyu_mono ty)

fun s_of oc (ty,f_tm) =
  (os oc "(s @ "; th0_ty_poly oc ty; os oc " @ "; f_tm oc; os oc ")")

fun th0_term_poly oc tm =
  let 
    val (rator,argl) = strip_comb tm 
    fun f_tm oc = 
      ho_fun oc (namea_obj_poly (rator,length argl), th0_iterm, argl)
  in  
    s_of oc (type_of tm,f_tm) 
  end
and th0_term_mono oc tm =
  let val (rator,argl) = strip_comb tm in
    ho_fun oc (name_obj_mono rator, th0_jterm, argl)
  end
and th0_iterm oc tm =
  let 
    val (rator,argl) = strip_comb tm
    val ty = type_of tm
  in
    if polymorphic (type_of rator)
    then th0_term_poly oc tm
    else 
      let fun f_tm oc = 
        ho_fun oc ("i_" ^ name_tyu_mono ty,th0_term_mono,[tm])
      in
        s_of oc (ty,f_tm)
      end
  end
and th0_jterm oc tm =
  let
    val (rator,argl) = strip_comb tm
    val ty = type_of tm
  in
    if polymorphic (type_of rator)
    then ho_fun oc ("j_" ^ name_tyu_mono ty,th0_term_poly,[tm])
    else th0_term_mono oc tm
  end


(* test term 
f 0 = f_poly (s(num,(i(0))))
load "hhExportTh0"; open hhExportTh0;
val tm =  ``(V + 0) + (zero (X:'a))``; 
th0_term_mono TextIO.stdOut tm;
th0_term_poly TextIO.stdOut tm;
*)

(* -------------------------------------------------------------------------
   TF0 formula
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
      else 
        if polymorphic (type_of l) 
        then 
          (os oc "("; th0_iterm oc l; os oc " = "; th0_iterm oc r; os oc ")")
        else
          (os oc "("; th0_jterm oc l; os oc " = "; th0_jterm oc r; os oc ")")
    end
  else (os oc "(p @ "; th0_jterm oc tm; os oc ")")
and th0_binop oc s (l,r) =
  (os oc "("; th0_pred oc l; os oc (" " ^ s ^ " "); 
   th0_pred oc r; os oc ")")
and th0_quant oc s (vl,bod) =
  (th0_quant_vl oc s vl; th0_pred oc bod)

fun th0_formula oc tm = (th0_forall_tyvarl_tm oc tm; th0_pred oc tm)

(* test term 
load "hhExportTh0"; open hhExportTh0;
val tm = ``!V0 V1. (V0 + 0) + (zero (V1:'a)) = 0``; 
th0_formula TextIO.stdOut tm;
th0_term_poly TextIO.stdOut tm;
th0_term TextIO.stdOut tm;
*)


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
    os oc "((p @ "; th0_jterm oc tm ; os oc ") <=> "; th0_pred oc tm; os oc ")"
  end

fun th0_logicdef oc (thy,name) =
  (os oc (thfpar ^ escape ("reserved.logic." ^ name) ^ ",axiom,"); 
   th0_logicformula oc (thy,name); osn oc ").")

fun th0_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val (tm,_) = translate_thm thm
  in
    os oc (thfpar ^ escape ("reserved.quant." ^ name) ^ ",axiom,"); 
    th0_formula oc tm; osn oc ")."
  end


(* -------------------------------------------------------------------------
   I-J axioms
   ------------------------------------------------------------------------- *)

fun th0def_iname oc ty = 
  (
  os oc thfpar; iname oc ty; os oc ",type,"; iname oc ty; os oc ":";
  os oc (name_tyu_mono ty ^ " > u"); osn oc ")."
  )

fun th0def_jname oc ty = 
  (
  os oc thfpar; jname oc ty; os oc ",type,"; jname oc ty; os oc ":";
  os oc ("du > " ^ name_tyu_mono ty); osn oc ")."
  )

(* for monomorphic types *)
fun ij_axiom oc ty =
  let 
    val v = mk_var ("V0",ty)
    val ty = type_of v 
    fun f_tm_lhs oc =
      (os oc "("; iname oc ty; os oc " @ "; 
       os oc "("; jname oc ty; os oc " @ "; th0_term_poly oc v;
       os oc "))")
  in
    th0_quant_vl_poly oc "!" [v];
    os oc "("; 
    s_of oc (ty,f_tm_lhs); os oc " = "; th0_term_poly oc v;
    os oc ")"
  end

fun th0def_ij_axiom oc ty =
  (os oc (thfpar ^ escape "ij." ^ name_tyu_mono ty ^ ",axiom,");
   ij_axiom oc ty; osn oc ").")

(* 
  load "hhExportTh0"; open hhExportTh0; 
  ij_axiom TextIO.stdOut ``:num``;
*)

(* for monomorphic types *)
fun ji_axiom oc ty =
  let val v = mk_var ("V0",ty) in
    th0_quant_vl oc "!" [v]; os oc "("; 
      os oc "("; jname oc ty; os oc " @ "; th0_iterm oc v; os oc ")";
      os oc " = "; os oc (name_obj_mono v);
    os oc ")"
  end

fun th0def_ji_axiom oc ty =
  (os oc (thfpar ^ escape "ji." ^ name_tyu_mono ty ^ ",axiom,");
   ji_axiom oc ty; osn oc ").")

(* 
  load "hhExportTh0"; open hhExportTh0; 
  ji_axiom TextIO.stdOut ``:num``;
*)


(* -------------------------------------------------------------------------
   TF0 definitions
   ------------------------------------------------------------------------- *)

(* Types *)
fun th0_tyop_poly a = 
  String.concatWith " > " (List.tabulate (a + 1,fn _ => dtype))

fun th0def_tyop_poly oc ((thy,tyop),a) = 
  let val th0name = name_tyop (thy,tyop) in
    (os oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":");
     os oc (th0_tyop_poly a); osn oc ").")
  end

(* Constants *)
fun th0_fun_sort a =
  if a <= 0 then utype else
  String.concatWith " > " (List.tabulate (a,fn _ => dutype)) ^ " > " ^
  utype

fun th0def_objnamed_poly oc (name,a) =
  (os oc (thfpar ^ name ^ ",type," ^ name ^ ":");
   os oc (th0_fun_sort a); osn oc ").")

fun th0def_obj_poly oc (tm,a) =
  th0def_objnamed_poly oc (namea_cv (tm,a), a) 

fun th0def_objnamed_mono oc (name,ty) =
  (os oc (thfpar ^ name ^ ",type," ^ name ^ ":");
   os oc (name_ty_mono ty); osn oc ").")

fun th0def_obj_mono oc (tm,a) =
  th0def_objnamed_mono oc (name_obj_mono tm, type_of tm)


(* Theorems *)
fun th0def_thm role oc (thy,name) =
  let 
    val thm = DB.fetch thy name
    val (cj,defl) = translate_thm thm
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

fun th0_cdef_app oc = 
  let
    val a = 2
    val th0name = namea_v (mk_var ("app",bool),a) (* bool is dummy type *)
  in
    th0def_objnamed_poly oc (th0name,a)
  end

(* p is not necessary in higher-order: replace mono.bool by $o *)
fun th0_cdef_p oc =
  let val th0name = "p" in
    os oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":");
    os oc (name_tyu_mono bool ^ " > $o"); osn oc ")."
  end

fun th0_cdef_s oc =
  let val th0name = "s" in
    os oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":");
    os oc (dtype ^ " > " ^ utype ^ " > " ^ dutype); osn oc ")."
  end

fun th0_cvdef_extra oc =
  (th0_cdef_s oc; th0_cdef_app oc; th0_cdef_p oc) 


(* -------------------------------------------------------------------------
   Higher-order theorems
   ------------------------------------------------------------------------- *)

fun th0_boolext oc = 
  let val (v0,v1) = (mk_var ("V0",bool),mk_var ("V1",bool)) in
    th0_quant_vl oc "!" [v0,v1];
    os oc "(("; th0_pred oc v0; os oc " <=> "; th0_pred oc v1; os oc ")";
    os oc " => ";
    os oc "("; th0_jterm oc v0; os oc " = "; th0_jterm oc v1; os oc "))"
  end

fun th0def_thm_boolext oc =
  let val th0name = escape "reserved.ho.boolext" in
    os oc (thfpar ^ th0name ^ ",axiom,"); th0_boolext oc; osn oc ")."
  end

fun th0def_thm_caster oc (name,thm) =
  let 
    val (cj,defl) = translate_thm thm
    val _ = if null defl then () else raise ERR "th0def_thm_caster" ""
    val th0name = escape ("reserved.ho." ^ name)
  in
    os oc (thfpar ^ th0name ^ ",axiom,"); th0_formula oc cj; osn oc ")."
  end

fun th0def_thm_combin oc (name,tm) =
  let val th0name = escape ("reserved.ho." ^ name) in
    os oc (thfpar ^ th0name ^ ",axiom,"); th0_formula oc tm; osn oc ")."
  end

fun th0def_thm_extra oc = 
  (
  app (th0def_thm_caster oc) app_axioml;
  th0def_thm_boolext oc;
  app (th0def_thm_caster oc) p_axioml;
  app (th0def_thm_combin oc) combin_axioml;
  app (th0_logicdef oc) logic_l1;
  app (th0_quantdef oc) quant_l2
  )

(* todo: declare types as constants in domains *)

val tyopl_extra_poly = tyopset_of_tyl [``:bool -> bool``]

val app_p_cval =
  let val tml = map (fst o translate_thm o snd) (app_axioml @ p_axioml) in
    mk_fast_set tma_compare (List.concat (map collect_arity tml)) 
  end

val combin_cval = 
  let val tml = map snd combin_axioml in
    mk_fast_set tma_compare (List.concat (map collect_arity tml)) 
  end

val cval_extra = boolop_cval @ combin_cval @ app_p_cval


(* -------------------------------------------------------------------------
   Monomorphism equations (only for monomorphic constants)
   todo: should not forget app equations
   ------------------------------------------------------------------------- *)

fun th0_monoeq oc (cv,a) =
  let val (tm,vl) = apply_cva (cv,a) in
    th0_quant_vl oc "!" vl;
    os oc "("; th0_iterm oc tm; os oc " = "; th0_term_poly oc tm; os oc ")"
  end

fun th0def_monoeq oc (cv,a) =
  let val th0name = escape "monoeq." ^ namea_obj_mono (cv,a) in
    os oc (thfpar ^ th0name ^ ",axiom,"); th0_monoeq oc (cv,a); osn oc ")."
  end

(* 
  load "hhExportTh0"; open hhExportTh0; 
  th0_monoeq TextIO.stdOut (``I:num -> num``,1);

![V0_2E0:mono_2Etyop_2Enum_2Enum]: (mono_2Ef_2E1_2Emono_2EA_27a(V0_2E0) = s(A_27a,f_2E1(s(tyop_2Enum_2Enum,i_mono_2Etyop_2Enum_2Enum(V0_2E0)))))
*)

(* -------------------------------------------------------------------------
   Arity equations
   ------------------------------------------------------------------------- *)

fun th0def_arityeq oc (cv,a) =
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

val cval_extra = boolop_cval @ combin_cval @ app_p_cval 
fun all_obja_aux tm =
  let val (oper,argl) = strip_comb tm in 
    (oper,length argl) :: List.concat (map all_obja_aux argl)
  end

fun all_obja tm = mk_fast_set tma_compare (all_obja_aux tm)

fun fetch_thmid (a,b) = DB.fetch a b

fun has_tyarg (cv,_) = 
  let val tyargl = typearg_of_cvapp cv in not (null tyargl) end

fun collect_tyul ty = 
  if is_vartype ty then [ty] else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in
          collect_tyul tya @ collect_tyul tyb
        end
      else [ty]
    end

fun th0_write_pb dir (thmid,depl) =
  let 
    val _ = mkDir_err dir
    val file  = dir ^ "/" ^ name_thm thmid ^ ".p"
    val oc    = TextIO.openOut file
    val tml1  = map ((op ::) o translate_thm o fetch_thmid) (thmid :: depl)
    val tml2  = mk_term_set (List.concat (map atoms (List.concat tml1)))
    val objal = mk_fast_set tma_compare (List.concat (map all_obja tml2))
    val cval_poly1 = filter (fn (x,_) => is_tptp_fv x orelse is_const x) objal
    val cval_poly2 = uniq_cvdef_mgc 
      (mk_fast_set tma_compare (cval_poly1 @ cval_extra))
    val tml3  = mk_term_set (map mk_arity_eq 
      (filter (fn x => snd x <> 0) cval_poly2))
    val tml4  = mk_term_set (List.concat (map atoms tml3))
    val objal_aux = 
        mk_fast_set tma_compare (List.concat (map all_obja (tml2 @ tml4)))
    val tyal  = mk_fast_set (cpl_compare Type.compare Int.compare)
      (map_fst type_of objal_aux) 
    val tyal_mono = filter (not o polymorphic o fst) tyal
    val tyul_mono =
      mk_type_set (List.concat (
        map (fn (ty,a) => collect_tyul ty) tyal_mono))
    val tyopl_poly = tyopset_of_tyl (map fst tyal)
    val cval_poly1_aux = 
       filter (fn (x,_) => is_tptp_fv x orelse is_const x) objal_aux
    val cval_poly2_aux = uniq_cvdef_mgc 
      (mk_fast_set tma_compare (cval_poly1_aux @ cval_extra))
    val cval_mono1 = filter (fn (x,_) => is_tptp_fv x orelse is_const x
      orelse is_app x) objal_aux
    val cval_mono2 = 
      (* should not add the zero arity for app *)
      filter (not o polymorphic o type_of o fst) 
      (mk_fast_set tma_compare (cval_mono1 @ cval_extra))
  in
    (
    app (th0def_name_ttype oc) sortl;
    app (th0def_ttype_mono oc) tyul_mono;
    app (th0def_tyop_poly oc) 
      (mk_fast_set ida_compare (tyopl_extra_poly @ tyopl_poly));
    th0_cvdef_extra oc;
    app (th0def_obj_poly oc) cval_poly2_aux;
    app (th0def_obj_mono oc) (uniq_cvdef_arity cval_mono2);
    app (th0def_iname oc) tyul_mono;
    app (th0def_jname oc) tyul_mono;
    th0def_thm_extra oc;
    app (th0def_ij_axiom oc) tyul_mono;
    app (th0def_ji_axiom oc) tyul_mono;
    app (th0def_arityeq oc) cval_poly1_aux;
    app (th0def_monoeq oc) (filter has_tyarg cval_mono2);
    app (th0def_thm "axiom" oc) depl; 
    th0def_thm "conjecture" oc thmid;
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end


(* 
  load "hhExportTh0"; open hhExportTh0; 
  val thmid = ("arithmetic","ADD1");
  val depl = valOf (hhExportLib.depo_of_thmid thmid);
  val dir = HOLDIR ^ "/src/holyhammer/export_th0_test";
  th0_write_pb dir (thmid,depl);
*)

end (* struct *)
