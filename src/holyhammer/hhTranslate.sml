(* ========================================================================= *)
(* FILE          : hhTranslate.sml                                           *)
(* DESCRIPTION   : HOL to FOL translation                                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhTranslate :> hhTranslate =
struct

open HolKernel boolLib aiLib

val ERR = mk_HOL_ERR "hhTranslate"
val debugdir = HOLDIR ^ "/src/holyhammer/debug"
fun debug s = debug_in_dir debugdir "hhTranslate" s

(* -------------------------------------------------------------------------
   Numbering terms and variables
   ------------------------------------------------------------------------- *)

val tmn_glob = ref 0 (* number terms for parallel use *)
val translate_cache = ref (dempty Term.compare)

fun incr_genvar iref =
  let val (a,b) = !iref in iref := (a, b+1) end

fun string_of_genvar iref =
  let val (a,b) = !iref in int_to_string a ^ "_" ^ int_to_string b end

(* --------------------------------------------------------------------------
   Preprocessing of the formula:
    (* 1 unfolding ?! *)
    2 fully applying lambdas if at the top of an equality
    3 applying beta conversion whenever possible
  -------------------------------------------------------------------------- *)

fun ELIM_LAMBDA_EQ tm =
  let val (l, r) = dest_eq tm in
    (
    if is_abs l orelse is_abs r
    then
      CHANGED_CONV (ONCE_REWRITE_CONV [FUN_EQ_THM] THENC
      (TRY_CONV (QUANT_CONV (BINOP_CONV BETA_CONV))))
    else NO_CONV
    )
    tm
  end

fun PREP_CONV tm =
  (
  (* PURE_REWRITE_CONV [EXISTS_UNIQUE_THM, EXISTS_UNIQUE_DEF] THENC
     Commented out because it can create very large term.
   *)
  TOP_DEPTH_CONV ELIM_LAMBDA_EQ THENC
  REDEPTH_CONV BETA_CONV
  )
  tm

fun prep_rw tm = rand (only_concl (QCONV PREP_CONV tm))

(* -------------------------------------------------------------------------
   Variable names
   ------------------------------------------------------------------------- *)

(* lifting *)
fun genvar_lifting iref ty =
  let val r = mk_var ("f" ^ string_of_genvar iref, ty) in
    incr_genvar iref; r
  end

(* arity *)
fun genvarl_arity tyl =
  let fun f i ty =  mk_var ("X" ^ int_to_string i, ty) in
    mapi f tyl
  end

(* -------------------------------------------------------------------------
   First-order atoms
   Warning: a and b are considered atoms is !a. a = b instead of a = b
   ------------------------------------------------------------------------- *)

fun must_pred tm =
  is_forall tm orelse is_exists tm orelse is_conj tm orelse is_disj tm orelse
  is_imp tm orelse is_eq tm orelse is_neg tm

local
  val (atoml: term list ref) = ref []
  fun atoms_aux tm =
    if is_conj tm orelse is_disj tm orelse is_imp_only tm orelse is_eq tm
      then (atoms_aux (lhand tm); atoms_aux (rand tm))
    else if is_neg tm      then atoms_aux (rand tm)
    else if is_forall tm   then atoms_aux (snd (dest_forall tm))
    else if is_exists tm   then atoms_aux (snd (dest_exists tm))
    else atoml := tm :: (!atoml)
in
  fun atoms tm = (atoml := []; atoms_aux tm; !atoml)
end

(* -------------------------------------------------------------------------
   Arity
   ------------------------------------------------------------------------- *)

fun update_adict adict arity tm =
  let val oldl = dfind tm (!adict) handle NotFound => [] in
    adict := dadd tm (arity :: oldl) (!adict)
  end

fun collect_arity_aux adict tm =
  if is_const tm orelse is_var tm then update_adict adict 0 tm
  else if is_comb tm then
    let val (oper,argl) = strip_comb tm in
      update_adict adict (length argl) oper;
      app (collect_arity_aux adict) argl
    end
  else if is_abs tm then collect_arity_aux adict (snd (dest_abs tm))
  else raise ERR "collect_arity_aux" ""

fun collect_arity tm =
  let
    val adict = ref (dempty Term.compare)
    fun f (_,l) = mk_fast_set Int.compare l
  in
    app (collect_arity_aux adict) (atoms tm);
    Redblackmap.map f (!adict)
  end

(* -------------------------------------------------------------------------
   FOF checks
   ------------------------------------------------------------------------- *)

(* Lambda *)
fun no_lambda tm = not (exists (can (find_term is_abs)) (atoms tm))
fun no_pred tm   = not (exists (can (find_term must_pred)) (atoms tm))

fun has_fofarity_bv tm =
  let
    val adict = collect_arity tm
    fun f x = length (dfind x adict) <= 1 handle NotFound => true
  in
    all f (all_bvar tm)
  end

(* -------------------------------------------------------------------------
   Lifting proposition and lambdas
   ------------------------------------------------------------------------- *)

fun ATOM_CONV conv tm =
  if is_forall tm orelse is_exists tm
    then QUANT_CONV (ATOM_CONV conv) tm
  else if is_conj tm orelse is_disj tm orelse is_imp_only tm orelse is_eq tm
    then BINOP_CONV (ATOM_CONV conv) tm else
  if is_neg tm
    then RAND_CONV (ATOM_CONV conv) tm
  else conv tm

fun FUN_EQ_CONVL vl eq = case vl of
    [] => REFL eq
  | a :: m => (STRIP_QUANT_CONV (X_FUN_EQ_CONV a) THENC FUN_EQ_CONVL m) eq

fun LIFT_CONV iref tm =
  let
    fun test x = must_pred x orelse is_abs x
    val subtm = find_term test tm handle _ => raise ERR "LIFT_CONV" ""
    val fvl = free_vars_lr subtm
    val v = genvar_lifting iref (type_of (list_mk_abs (fvl,subtm)))
    val rep = list_mk_comb (v,fvl)
    val eq  = list_mk_forall (fvl, (mk_eq (subtm,rep)))
    val thm = ASSUME eq
  in
    if is_abs subtm then
      let
        val (vl,bod) = strip_abs subtm
        val ethm1 = (FUN_EQ_CONVL vl THENC TOP_DEPTH_CONV BETA_CONV) eq
        val ethm2 = UNDISCH (snd (EQ_IMP_RULE ethm1))
        val cthm = PURE_REWRITE_CONV [thm] tm
      in
        PROVE_HYP ethm2 cthm
      end
    else PURE_REWRITE_CONV [thm] tm
  end

fun RPT_LIFT_CONV iref tm =
  let
    val thmo = SOME (REPEATC (ATOM_CONV (TRY_CONV (LIFT_CONV iref))) tm)
    handle UNCHANGED => NONE
  in
    case thmo of
      SOME thm =>
      let
        val (asl,w) = dest_thm thm
        val thml1 = List.concat (map (RPT_LIFT_CONV iref) asl)
      in
        thm :: thml1
      end
    | NONE => [REFL tm]
  end

(* -------------------------------------------------------------------------
   Lowest arity for bound variables. Arity 0.
   ------------------------------------------------------------------------- *)

fun LET_CONV_MIN tm =
  let val (rator,rand) = dest_comb tm in
    SYM (ISPECL [rator,rand] LET_THM)
  end

fun LET_CONV_AUX tm =
 (TRY_CONV (RATOR_CONV LET_CONV_AUX) THENC LET_CONV_MIN) tm

fun LET_CONV_BV bvl tm =
  if not (is_comb tm) then NO_CONV tm else
    let val (f,_) = strip_comb tm in
      if mem f bvl then LET_CONV_AUX tm else NO_CONV tm
    end

(* Warning: assumes free variables and bound variables have distinct names *)
fun LET_CONV_BVL tm =
  let val bvl = all_bvar tm in
    TOP_SWEEP_CONV (LET_CONV_BV bvl) tm
  end

(* -------------------------------------------------------------------------
   Arity equations for constants and free variables.
   Naming is important here as we do not want free variables to have the same
   name across statements unless their definition are alpha equivalent.
   ------------------------------------------------------------------------- *)

fun mk_arity_eq f n =
  let
    val (tyl,_) = strip_type (type_of f)
    val vl = genvarl_arity tyl
    val t1 = list_mk_comb (f, List.take (vl,n))
  in
    GENL vl (LET_CONV_AUX t1)
  end

fun optim_arity_eq tm =
  let
    val l = dlist (collect_arity tm)
    fun g x = x <> 0
    fun f (tm,nl) =
      if is_abs tm orelse is_comb tm then raise ERR "optim_arity_eq" ""
      else
        if length nl >= 2
        then map (mk_arity_eq tm) (filter g nl)
        else []
  in
    List.concat (map f l)
  end

fun all_arity_eq tm =
  let
    val l = dlist (collect_arity tm)
    fun g x = x <> 0
    fun f (tm,nl) =
      if is_abs tm orelse is_comb tm then raise ERR "all_arity_eq" ""
      else map (mk_arity_eq tm) (filter g nl)
  in
    List.concat (map f l)
  end

(* -------------------------------------------------------------------------
   Monorphization: not used in the current FOF translation.
   ------------------------------------------------------------------------- *)

val mk_term_set = mk_fast_set Term.compare
val mk_type_set = mk_fast_set Type.compare

fun name_of_const c =
  let val {Name, Thy, Ty} = dest_thy_const c in
    Thy ^ "." ^ Name
  end

fun regroup_cid cl =
  let
    val dict = ref (dempty String.compare)
    fun update_dict c =
      let
        val cid  = name_of_const c
        val ty   = snd (dest_const c)
        val oldl = dfind cid (!dict) handle NotFound => []
      in
        dict := dadd cid (ty :: oldl) (!dict)
      end
  in
    app update_dict cl;
    dlist (!dict)
  end

(* Types *)
fun inst_mono_one ty tyl =
  if polymorphic ty
  then mapfilter (match_type ty) tyl
  else []

fun inst_mono tyl1 tyl2 =
  let val ll = map (C inst_mono_one tyl2) tyl1 in
    mk_set (List.concat ll)
    (* more efficient to normalize the substution first *)
  end

(* Term *)
fun find_cid cid tm =
  let fun test x = is_const x andalso name_of_const x = cid in
    mk_term_set (find_terms test tm)
  end

fun mono_cid ((cid,tyl2),tml) =
  let
    val cl = mk_term_set (List.concat (map (find_cid cid) tml))
    val tyl1 = map (snd o dest_const) cl
    val tyinstl = inst_mono tyl1 tyl2
    fun inst_tm tm = mk_term_set (tm :: map (C inst tm) tyinstl)
  in
    mk_term_set (List.concat (map inst_tm tml))
  end

fun monomorphize tml cj =
  let
    val cl = find_terms is_const cj
    val cidl = regroup_cid cl
  in
    foldl mono_cid tml cidl
  end

(* -------------------------------------------------------------------------
   Full FOF translation
   ------------------------------------------------------------------------- *)

(* Guarantees that there are no free variables in the term *)
fun prepare_tm tm =
  let val tm' = prep_rw tm in
    rename_bvarl escape (list_mk_forall (free_vars_lr tm', tm'))
  end

(* Slow because of term_to_string *)
fun debug_translate_tm (tmn,tm) =
  let
    val iref = ref (tmn,0)
    val _ = debug ("  " ^ term_to_string tm)
    val tm1 = prepare_tm tm
    val _ = debug ("Renaming variables:\n  " ^ term_to_string tm1)
    val thml1 = RPT_LIFT_CONV iref tm1
    val tml1 = map (rand o concl) thml1
    val _ = debug ("Lifting lambdas and predicates:\n  " ^
      String.concatWith "\n  " (map term_to_string tml1))
    val thml2 = (map (TRY_CONV LET_CONV_BVL THENC REFL)) tml1
    val tml2 = map (rand o concl) thml2
  in
    tml2
  end

fun translate_tm_aux (tmn,tm) =
  let
    val iref  = ref (tmn,0)
    val tm1   = prepare_tm tm
    val thml1 = RPT_LIFT_CONV iref tm1
    val tml1  = map (rand o concl) thml1
    val thml2 = (map (TRY_CONV LET_CONV_BVL THENC REFL)) tml1
    val tml2  = map (rand o concl) thml2
  in
    tml2
  end

fun translate_tm tm =
  dfind tm (!translate_cache) handle NotFound =>
  let val tml = translate_tm_aux ((!tmn_glob),tm) in
    incr tmn_glob;
    translate_cache := dadd tm tml (!translate_cache); tml
  end

fun translate_pb premises cj =
  let
    fun f (name,thm) = (debug ("\n" ^ name);
      (name, translate_tm (concl (DISCH_ALL thm))))
    val cj_tml = translate_tm cj
    val ax_tml = map f premises
    val big_tm =
      list_mk_conj (map list_mk_conj (cj_tml :: (map snd ax_tml)))
    val ari_thml = optim_arity_eq big_tm
    val ari_tml =  map only_concl ari_thml
  in
    (ari_tml, ax_tml, cj_tml)
  end

fun name_pb (ari_tml, ax_tml, cj_tml) =
  let
    (* arity *)
    fun name_ari i tm = ("arity" ^ int_to_string i, tm)
    val axl1 = mapi name_ari ari_tml
    (* axioms *)
    fun name_ax (name,tml) =
      let fun name_axi i tm = (name ^ "." ^ int_to_string i, tm) in
        mapi name_axi tml
      end
    val axl2 = List.concat (map name_ax ax_tml)
    (* conjecture *)
    fun name_cjdef i tm = ("cj_def" ^ int_to_string i, tm)
    val cj = hd cj_tml (* Relies on the behavior of RPT_LIFT_CONV *)
    val axl3 = mapi name_cjdef (tl cj_tml)
  in
    (axl1 @ axl2 @ axl3, cj)
  end


end
