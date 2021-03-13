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
fun foralls (vl,t) = case vl of 
    [] => t 
  | a :: m => mk_forall (a, foralls (m,t))
val list_mk_forall = foralls


val thfpar = "thf("
type thmid = string * string
fun is_monoapp (app,_) = is_app app andalso not (polymorphic (type_of app))

fun name_obj_mono cv =
  (if is_tptp_bv cv then name_v cv
  else add_tyargltag (escape "mono." ^ name_cv cv) cv)
  handle HOL_ERR _ => raise ERR "name_obj_mono" (term_to_string cv)

(* -------------------------------------------------------------------------
   TF0 types
   ------------------------------------------------------------------------- *)

fun name_tyu_mono_and_o ty =
  if ty = bool then "$o" else name_tyu_mono ty

fun name_ty_mono ty =
  if is_vartype ty then raise ERR "name_ty_mono" "" else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (ty1,ty2) = pair_of_list Args in
          "(" ^ name_ty_mono ty1 ^ " > " ^ name_ty_mono ty2 ^ ")"
        end
      else name_tyu_mono_and_o ty
    end

fun th0def_name_ttype oc th0name =
  osn oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":" ^ ttype ^ ").")

fun th0def_ttype_mono oc ty =
  if ty = bool then () else
  let val th0name = name_tyu_mono ty in
    th0def_name_ttype oc th0name
  end

val (utype,dtype,dutype) = ("u","d","du")
val sortl = [utype,dtype,dutype]

fun ho_fun oc (f_oper,f_arg,argl) =
  if null argl then f_oper oc else
  (os oc "("; f_oper oc; os oc " @ "; oiter oc " @ " f_arg argl; os oc ")")

fun th0_ty_poly oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop (Thy,Tyop)
    in
      ho_fun oc (fn oc_loc => os oc_loc tyops, th0_ty_poly, Args)
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
      ho_fun oc (
        fn oc_loc => os oc_loc (namea_obj_poly (rator,length argl)),
        th0_iterm, argl)
  in
    s_of oc (type_of tm,f_tm)
  end
and th0_term_mono oc tm =
  if is_var tm orelse is_const tm then os oc (name_obj_mono tm)
  else if is_abs tm then
    let val (vl,bod) = strip_abs tm in
      (os oc "("; th0_quant_vl oc "^" vl; th0_jterm oc bod; os oc ")")
    end
  else
  let val (rator,argl) = strip_comb tm in
    if is_monoapp (rator,length argl) then
      let val (fx,vx) = pair_of_list argl in
        os oc "("; th0_jterm oc fx; os oc " @ "; th0_jterm oc vx;
        os oc ")"
      end
    else ho_fun oc (fn oc_loc => th0_term_mono oc_loc rator, th0_jterm, argl)
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
        ho_fun oc (fn oc_loc => iname oc_loc ty,th0_term_mono,[tm])
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
    then ho_fun oc (fn oc_loc => jname oc_loc ty,th0_term_poly,[tm])
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
    (os oc "((~) @ "; th0_pred oc (dest_neg tm); os oc ")")
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
  else th0_jterm oc tm
and th0_binop oc s (l,r) =
  (os oc "("; th0_pred oc l; os oc (" " ^ s ^ " ");
   th0_pred oc r; os oc ")")
and th0_quant oc s (vl,bod) =
  (os oc "("; th0_quant_vl oc s vl; th0_pred oc bod; os oc ")")

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
    (th0_forall_tyvarl_tm oc tm; th0_quant_vl oc "!" vl;
     os oc "("; th0_jterm oc tm ; os oc " <=> "; th0_pred oc tm; os oc ")")
  end

fun th0_logicdef oc (thy,name) =
  (os oc (thfpar ^ escape ("reserved.logic." ^ name) ^ ",axiom,");
   th0_logicformula oc (thy,name); osn oc ").")

fun th0_quantdef oc (thy,name) =
  let
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val statement = translate_thm thm
  in
    os oc (thfpar ^ escape ("reserved.quant." ^ name) ^ ",axiom,");
    th0_formula oc statement; osn oc ")."
  end


(* -------------------------------------------------------------------------
   I-J axioms
   ------------------------------------------------------------------------- *)

fun th0def_iname oc ty =
  (
  os oc thfpar; iname oc ty; os oc ",type,"; iname oc ty; os oc ":";
  os oc (name_ty_mono ty ^ " > u"); osn oc ")."
  )

fun th0def_jname oc ty =
  (
  os oc thfpar; jname oc ty; os oc ",type,"; jname oc ty; os oc ":";
  os oc ("du > " ^ name_ty_mono ty); osn oc ")."
  )

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

fun th0def_obj_mono oc tm =
  th0def_objnamed_mono oc (name_obj_mono tm, type_of tm)

fun rw_conv conv tm = (rhs o concl o conv) tm

fun th0def_thm role oc (thy,name) =
  let
    val statement = translate_thm (DB.fetch thy name)
    val th0name = name_thm (thy,name)
  in
    os oc (thfpar ^ th0name ^ "," ^ role ^ ",");
    th0_formula oc statement; osn oc ")."
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

fun th0_cdef_s oc =
  let val th0name = "s" in
    os oc (thfpar ^ th0name ^ ",type," ^ th0name ^ ":");
    os oc (dtype ^ " > " ^ utype ^ " > " ^ dutype); osn oc ")."
  end

fun th0_cvdef_extra oc = (th0_cdef_s oc; th0_cdef_app oc)

(* -------------------------------------------------------------------------
   Higher-order theorems
   ------------------------------------------------------------------------- *)

fun th0def_thm_caster oc (name,thm) =
  let
    val statement = translate_thm thm
    val th0name = escape ("reserved.ho." ^ name)
  in
    os oc (thfpar ^ th0name ^ ",axiom,");
    th0_formula oc statement; osn oc ")."
  end

fun th0def_thm_combin oc (name,tm) =
  let val th0name = escape ("reserved.ho." ^ name) in
    os oc (thfpar ^ th0name ^ ",axiom,"); th0_formula oc tm; osn oc ")."
  end

fun th0def_thm_extra oc =
  (
  app (th0def_thm_caster oc) app_axioml;
  app (th0def_thm_combin oc) combin_axioml;
  app (th0_logicdef oc) logic_l1;
  app (th0_quantdef oc) quant_l2
  )

val app_p_cval =
  let val tml = map (translate_thm o snd) (app_axioml @ p_axioml) in
    mk_fast_set tma_compare (List.concat (map collect_arity_noapp tml))
  end

val combin_cval =
  let val tml = map snd combin_axioml in
    mk_fast_set tma_compare (List.concat (map collect_arity_noapp tml))
  end

(* -------------------------------------------------------------------------
   Monomorphism equations (only for monomorphic constants including app)
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
  ![V0_2E0:mono_2Etyop_2Enum_2Enum]: (mono_2Ef_2E1_2Emono_2EA_27a(V0_2E0) =
  s(A_27a,f_2E1(s(tyop_2Enum_2Enum,i_mono_2Etyop_2Enum_2Enum(V0_2E0)))))
*)

(* -------------------------------------------------------------------------
   Arity equations
   ------------------------------------------------------------------------- *)

fun th0def_arityeq oc (cv,a) =
  if a = 0 orelse not (polymorphic (type_of cv)) then () else
  let
    val th0name = name_arityeq (cv,a)
    val tm = mk_arity_eq (cv,a)
  in
    os oc (thfpar ^ th0name ^ ",axiom,"); th0_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Monomorphic app equations
   ------------------------------------------------------------------------- *)

fun th0def_monoapp oc (app,a) =
  if a <> 2 then raise ERR "th0def_monoapp" "" else
    let
      val th0name = escape "monoapp." ^ name_obj_mono app
      val (tm,l) = apply_cva (app,a)
      val (fv,xv) = pair_of_list l
      val formula = list_mk_forall ([fv,xv], mk_eq (tm,mk_comb (fv,xv)))
    in
      os oc (thfpar ^ th0name ^ ",axiom,"); th0_formula oc formula; osn oc ")."
    end

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

fun has_tyarg (cv,_) =
  let val tyargl = typearg_of_cvapp cv in not (null tyargl) end

(* atom *)
fun collect_atoml thmidl =
  let fun f x =
    let val statement = translate_thm (uncurry DB.fetch x) in
      mk_term_set (atoms statement)
    end
  in
    mk_term_set (List.concat (map f thmidl))
  end

(* objects *)
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
val tya_compare = cpl_compare Type.compare Int.compare

val tyopl_extra_poly = tyopset_of_tyl [``:bool -> bool``]

fun prepare_tyopl_poly tyal =
  let val l = tyopset_of_tyl (map fst tyal) in
    mk_fast_set ida_compare (tyopl_extra_poly @ l)
  end

(* different from tf0 *)
fun extract_ho_tyu ty =
  if is_vartype ty then raise ERR "extract_ho_tyu" "" else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (ty1,ty2) = pair_of_list Args in
          extract_ho_tyu ty1 @ extract_ho_tyu ty2
        end
      else [ty]
    end

fun fo_subterms tm =
  let val (oper,argl) = strip_comb tm in
    tm :: List.concat (map fo_subterms argl)
  end

fun fo_subterms_tml atoml =
  mk_term_set (List.concat (map fo_subterms atoml))

fun ho_subterms_tml atoml =
  mk_term_set (List.concat (map (find_terms (fn _ => true)) atoml))


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

fun prepare_tyul_mono_fo atoml =
  let
    val tml = fo_subterms_tml atoml
    val tyl = mk_type_set (bool :: (map type_of tml))
  in
    filter (not o polymorphic) tyl
  end

fun prepare_tyul_mono_ho atoml =
  let
    val tml = ho_subterms_tml atoml
    val tyl1 = mk_type_set (bool :: (map type_of tml))
    val tyl2 = filter (not o polymorphic) tyl1
  in
    mk_type_set (List.concat (map extract_ho_tyu tyl2))
  end

(* -------------------------------------------------------------------------
   Write problem
   ------------------------------------------------------------------------- *)

fun th0_preambule oc atoml1 =
  let
    val (cval_arityeq, atoml_arityeq) = prepare_arityeq atoml1
    val atoml2 = atoml_arityeq @ atoml1
    val objal = all_obja_tml atoml2
    val cval_poly = prepare_cval_poly objal
    val cval_mono = prepare_cval_mono objal
    val tyal = mk_fast_set tya_compare (map_fst type_of objal)
    val tyopl_poly = prepare_tyopl_poly (fo_subterms_tml atoml2)
    val tyul_mono_fo = prepare_tyul_mono_fo atoml2
    val tyul_mono_ho = prepare_tyul_mono_ho atoml2
  in
    app (th0def_name_ttype oc) sortl;
    app (th0def_ttype_mono oc) tyul_mono_ho;
    app (th0def_tyop_poly oc) tyopl_poly;
    th0_cvdef_extra oc;
    app (th0def_obj_poly oc) cval_poly;
    app (th0def_obj_mono oc) (uniq_cvdef_arity cval_mono);
    app (th0def_iname oc) tyul_mono_fo;
    app (th0def_jname oc) tyul_mono_fo;
    th0def_thm_extra oc;
    app (th0def_ij_axiom oc) tyul_mono_fo;
    app (th0def_ji_axiom oc) tyul_mono_fo;
    app (th0def_arityeq oc) cval_arityeq;
    app (th0def_monoeq oc) (filter has_tyarg cval_mono);
    app (th0def_monoapp oc) (filter is_monoapp cval_mono)
  end

fun th0_write_pb dir (thmid,(depthyl,depl)) =
  let
    val _ = mkDir_err dir
    val file = dir ^ "/" ^ name_thm thmid ^ ".p"
    val oc  = TextIO.openOut file
    val atoml1 = collect_atoml (thmid :: depl)
  in
    (
    app (fn x => osn oc ("include('" ^ x ^ ".ax').")) depthyl;
    th0_preambule oc atoml1;
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

(* -------------------------------------------------------------------------
   Bushy problems
   ------------------------------------------------------------------------- *)

fun write_thy_bushy dir thy =
  let val cjdepl = bushy_dep thy (DB.theorems thy) in
    print (thy ^ " "); app (th0_write_pb dir) cjdepl
  end

fun th0_export_bushy dir thyl =
  let val thyorder = sorted_ancestry thyl in
    mkDir_err dir; app (write_thy_bushy dir) thyorder
  end

(* -------------------------------------------------------------------------
   Chainy problems
   ------------------------------------------------------------------------- *)

fun th0_export_thy dir thy =
  let
    val _ = mkDir_err dir
    val file  = dir ^ "/" ^ thy ^ ".ax"
    val oc  = TextIO.openOut file
    val thmidl = thmidl_in_thy thy
    val atoml = collect_atoml thmidl
  in
    (
    th0_preambule oc atoml;
    app (th0def_thm "axiom" oc) thmidl;
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy dir thyorder thy =
  let val cjdepl = chainy_dep thyorder thy (DB.theorems thy) in
    print (thy ^ " "); app (th0_write_pb dir) cjdepl
  end

fun th0_export_chainy dir thyl =
  let val thyorder = sorted_ancestry thyl in
    mkDir_err dir;
    app (th0_export_thy (dir ^ "/theories")) thyorder;
    app (write_thy_chainy (dir ^ "/problems") thyorder) thyorder
  end


end (* struct *)
