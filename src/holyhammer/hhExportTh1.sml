(* ========================================================================= *)
(* FILE          : hhExportTh1.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTh1 :> hhExportTh1 =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportThf"
fun foralls (vl,t) = case vl of
    [] => t
  | a :: m => mk_forall (a, foralls (m,t))
val list_mk_forall = foralls

type thmid = string * string
val thfpar = "thf("

(* -------------------------------------------------------------------------
   Translation functions
   ------------------------------------------------------------------------- *)

fun th1_translate_tm tm =
  rename_bvarl escape (list_mk_forall (free_vars_lr tm, tm))
fun th1_translate_thm thm =
  (th1_translate_tm o concl o GEN_ALL  o DISCH_ALL) thm

(* -------------------------------------------------------------------------
   TH1 type
   ------------------------------------------------------------------------- *)

fun th1_type oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "bool" then os oc "$o"
      else if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in
          os oc "("; th1_type oc tya;
          os oc " > "; th1_type oc tyb; os oc ")"
        end
      else if null Args then os oc (name_tyop (Thy,Tyop))
      else (os oc "("; os oc (name_tyop (Thy,Tyop)); os oc " @ ";
            oiter oc " @ " th1_type Args; os oc ")")
    end

(* -------------------------------------------------------------------------
   TH1 quantifiers
   ------------------------------------------------------------------------- *)

fun th1_vty oc v = (os oc (name_v v ^ ":"); th1_type oc (type_of v))

fun th1_quant_vl oc s vl =
  if null vl then () else
  (os oc s; os oc "["; oiter oc ", " th1_vty vl; os oc "]: ")

fun th1_forall_tyvarl_tm oc tm =
  let
    val tvl = dict_sort Type.compare (type_vars_in_term tm)
    fun f oc x = os oc (name_vartype x ^ ":" ^ ttype)
  in
    if null tvl then () else (os oc "!["; oiter oc ", " f tvl; os oc "]: ")
  end

fun th1_forall_tyvarl_ty oc ty =
  let
    val tvl = dict_sort Type.compare (type_vars ty)
    fun f oc x = os oc (name_vartype x ^ ":" ^ ttype)
  in
    if null tvl then () else (os oc "!>["; oiter oc ", " f tvl; os oc "]: ")
  end

(* -------------------------------------------------------------------------
   TH1 term
   ------------------------------------------------------------------------- *)

fun th1_term oc tm =
  if is_tptp_bv tm then os oc (name_v tm)
  else if is_const tm then
    let val resl = typearg_of_c tm in
      if null resl
      then os oc (name_c tm)
      else (os oc "("; os oc (name_c tm); os oc " @ ";
            oiter oc " @ " th1_type resl; os oc ")")
    end
  else if is_comb tm then
    let val (rator,argl) = strip_comb tm in
      os oc "("; th1_term oc rator;
      os oc " @ "; oiter oc " @ " th1_term argl; os oc ")"
    end
  else if is_abs tm then
    let val (vl,bod) = strip_abs tm in
      os oc "(";
      os oc "^["; oiter oc ", " th1_vty vl; os oc "]: "; th1_term oc bod;
      os oc ")"
    end
  else raise ERR "th1_term" ""

(* -------------------------------------------------------------------------
   TH1 formula
   ------------------------------------------------------------------------- *)

fun th1_pred oc tm =
  if is_forall tm then th1_quant oc "!" (strip_forall tm)
  else if is_exists tm then th1_quant oc "?" (strip_exists tm)
  else if is_conj tm then th1_binop oc "&" (dest_conj tm)
  else if is_disj tm then th1_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then th1_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "((~) @ "; th1_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r
      then th1_binop oc "<=>" (l,r)
      else (os oc "("; th1_term oc l; os oc " = ";
            th1_term oc r; os oc ")")
    end
  else th1_term oc tm
and th1_binop oc s (l,r) =
  (os oc "("; th1_pred oc l; os oc (" " ^ s ^ " "); th1_pred oc r; os oc ")")
and th1_quant oc s (vl,bod) =
  (os oc "("; th1_quant_vl oc s vl; th1_pred oc bod; os oc ")")

fun th1_formula oc tm = (th1_forall_tyvarl_tm oc tm; th1_pred oc tm)

(* -------------------------------------------------------------------------
   Term-level logical operators equations
   ------------------------------------------------------------------------- *)

fun th1_logicformula oc (thy,name) =
  let
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val vl = free_vars_lr tm
  in
    th1_forall_tyvarl_tm oc tm; th1_quant_vl oc "!" vl;
    os oc "("; th1_term oc tm ; os oc " <=> "; th1_pred oc tm; os oc ")"
  end

fun th1_logicdef oc (thy,name) =
  (
  os oc (thfpar ^ escape ("logicdef." ^ name) ^ ",axiom,");
  th1_logicformula oc (thy,name); osn oc ")."
  )

fun th1_quantdef oc (thy,name) =
  let
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val statement = th1_translate_thm thm
  in
    os oc (thfpar ^ escape ("quantdef." ^ name) ^ ",axiom,");
    th1_formula oc statement; osn oc ")."
  end

(* -------------------------------------------------------------------------
   TH1 definitions
   ------------------------------------------------------------------------- *)

fun th1_ttype arity =
  String.concatWith " > " (List.tabulate (arity + 1, fn _ => ttype))

fun th1_tyopdef oc ((thy,tyop),arity) =
  let val th1name = name_tyop (thy,tyop) in
    os oc (thfpar ^ th1name ^ ",type," ^ th1name ^ ":");
    os oc (th1_ttype arity); osn oc ")."
  end

fun th1_cvdef oc c =
  let val (th1name,ty) = (name_c c, type_of c) in
    os oc (thfpar ^ th1name ^ ",type," ^ th1name ^ ":");
    th1_forall_tyvarl_ty oc ty; th1_type oc ty; osn oc ")."
  end

fun th1_thmdef role oc (thy,name) =
  let
    val thm = DB.fetch thy name
    val statement = th1_translate_thm thm
  in
    os oc (thfpar ^ (name_thm (thy,name)) ^ "," ^ role ^ ",");
    th1_formula oc statement; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Extra information
   ------------------------------------------------------------------------- *)

val tyopl_extra = tyopset_of_tyl [``:bool -> bool``]
val cval_extra = boolop_cval

fun th1_thmdef_extra oc =
  (app (th1_logicdef oc) logic_l1;
   app (th1_quantdef oc) quant_l2)

(* -------------------------------------------------------------------------
   Export problem
   ------------------------------------------------------------------------- *)

fun collect_tml thmidl =
  let fun f x = atoms (th1_translate_thm (uncurry DB.fetch x)) in
    mk_term_set (List.concat (map f thmidl))
  end

fun th1_preambule oc tml =
  let
    val cvl1 = mk_term_set (List.concat (map (find_terms is_const) tml))
    val cvl2 = map fst cval_extra
    val cvl3 = mk_term_set (map mgc_of (cvl1 @ cvl2))
    val tyopl =  mk_fast_set ida_compare
      (List.concat (tyopl_extra :: map collect_tyop tml))
  in
    app (th1_tyopdef oc) tyopl;
    app (th1_cvdef oc) cvl3;
    th1_thmdef_extra oc
  end

fun th1_write_pb dir (thmid,(depthyl,depl)) =
  let
    val _ = mkDir_err dir
    val file  = dir ^ "/" ^ name_thm thmid ^ ".p"
    val oc  = TextIO.openOut file
    val tml = collect_tml (thmid :: depl)
  in
    (
    app (fn x => osn oc ("include('" ^ x ^ ".ax').")) depthyl;
    th1_preambule oc tml;
    app (th1_thmdef "axiom" oc) depl;
    th1_thmdef "conjecture" oc thmid;
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(*
load "hhExportTh1"; open hhExportTh1;
val thmid = ("bool","RES_SELECT_THM");
val depl = valOf (hhExportLib.depo_of_thmid thmid);
val dir = HOLDIR ^ "/src/holyhammer/export_th1_test";
th1_write_pb dir (thmid,([],depl));
*)

(* -------------------------------------------------------------------------
   Bushy problems
   ------------------------------------------------------------------------- *)

fun write_thy_bushy dir thy =
  let val cjdepl = bushy_dep thy (DB.theorems thy) in
    print (thy ^ " "); app (th1_write_pb dir) cjdepl
  end

fun th1_export_bushy dir thyl =
  let val thyorder = sorted_ancestry thyl in
    mkDir_err dir; app (write_thy_bushy dir) thyorder
  end

(* -------------------------------------------------------------------------
   Chainy problems
   ------------------------------------------------------------------------- *)

fun th1_export_thy dir thy =
  let
    val _ = mkDir_err dir
    val file  = dir ^ "/" ^ thy ^ ".ax"
    val oc  = TextIO.openOut file
    val thmidl = thmidl_in_thy thy
    val tml = collect_tml thmidl
  in
    (
    th1_preambule oc tml;
    app (th1_thmdef "axiom" oc) thmidl;
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy dir thyorder thy =
  let val cjdepl = chainy_dep thyorder thy (DB.theorems thy) in
    print (thy ^ " "); app (th1_write_pb dir) cjdepl
  end

fun th1_export_chainy dir thyl =
  let val thyorder = sorted_ancestry thyl in
    mkDir_err dir;
    app (th1_export_thy (dir ^ "/theories")) thyorder;
    app (write_thy_chainy (dir ^ "/problems") thyorder) thyorder
  end


end (* struct *)
