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

(* -------------------------------------------------------------------------
   Eliminating some lambdas without lambda-lifting
   ------------------------------------------------------------------------- *)

fun ELIM_LAMBDA_EQ tm =
  let val (l, r) = dest_eq tm in
    (
    if is_abs l orelse is_abs r then
      CHANGED_CONV (ONCE_REWRITE_CONV [FUN_EQ_THM] THENC
                    REDEPTH_CONV BETA_CONV)
    else NO_CONV
    )
    tm
  end

fun PREP_CONV tm = 
  (REDEPTH_CONV ELIM_LAMBDA_EQ THENC REDEPTH_CONV BETA_CONV) tm

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
  let fun f i ty = mk_var ("X" ^ int_to_string i, ty) in
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
   Extract constants in a term
   ------------------------------------------------------------------------- *)

fun is_app tm = is_var tm andalso fst (dest_var tm) = "app" 

fun is_tptp_fv tm = 
  is_var tm andalso Char.isLower (String.sub (fst (dest_var tm),0))
  andalso fst (dest_var tm) <> "app"
fun is_tptp_bv tm = 
  is_var tm andalso Char.isUpper (String.sub (fst (dest_var tm),0))

fun all_fosubtm tm =
  let val (oper,argl) = strip_comb tm in 
    tm :: List.concat (map all_fosubtm argl)
  end

fun collect_arity tm =
  let 
    val tml1 = List.concat (map all_fosubtm (atoms tm))
    val tml2 = mk_term_set tml1
    fun f subtm = 
      let val (oper,argl) = strip_comb subtm in
        if is_tptp_fv oper orelse is_const oper 
        then SOME (oper,length argl)
        else NONE
      end
  in
    mk_fast_set (cpl_compare Term.compare Int.compare) (List.mapPartial f tml2)
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

fun APP_CONV_MIN tm =
  let 
    val (rator,rand) = dest_comb tm
    val f = mk_var ("f",type_of rator)
    val v = mk_var ("v",type_of rand)
    val bod = mk_comb (f,v) 
    val lam = list_mk_abs (free_vars_lr bod, bod)
    val app = mk_var ("app",type_of lam)
    val eq = mk_eq (app, lam)
    val thm1 = ASSUME eq
    val thm2 = AP_THM (AP_THM thm1 f) v
    val thm3 = CONV_RULE (REDEPTH_CONV BETA_CONV) thm2
    val thm4 = GENL [f,v] thm3
  in
    SYM (ISPECL [rator,rand] thm4)
  end

fun APP_CONV_AUX tm =
  (TRY_CONV (RATOR_CONV APP_CONV_AUX) THENC APP_CONV_MIN) tm

fun APP_CONV_BV tm =
  if not (is_comb tm) then NO_CONV tm else
    let val (oper,_) = strip_comb tm in
      if is_tptp_bv oper then APP_CONV_AUX tm else NO_CONV tm
    end

fun APP_CONV_BVL tm = TOP_SWEEP_CONV APP_CONV_BV tm

(* -------------------------------------------------------------------------
   Arity equations for constants and free variables.
   Naming is important here as we do not want free variables to have the same
   name across statements unless their definition are alpha equivalent.
   ------------------------------------------------------------------------- *)

fun mk_arity_eq (f,n) =
  let
    val (tyl,_) = strip_type (type_of f)
    val vl = genvarl_arity tyl
    val vl' =  List.take (vl,n)
    val tm = list_mk_comb (f,vl')
  in
    concl (GENL vl' (APP_CONV_AUX tm))
  end

fun all_arity_eq tm =
  map mk_arity_eq (filter (fn (_,a) => a <> 0) (collect_arity tm))

(* -------------------------------------------------------------------------
   FOF Translation
   ------------------------------------------------------------------------- *)

fun prepare_tm tm =
  let val tm' = prep_rw tm in
    rename_bvarl escape (list_mk_forall (free_vars_lr tm', tm'))
  end

fun sym_def tm = (rhs o concl o STRIP_QUANT_CONV SYM_CONV) tm

fun fof_translate_aux (tmn,tm) =
  let
    val iref  = ref (tmn,0)
    val tm1   = prepare_tm tm
    val thml1 = RPT_LIFT_CONV iref tm1
    val tml1  = map (rand o concl) thml1
    val thml2 = (map (TRY_CONV APP_CONV_BVL THENC REFL)) tml1
    val tml2  = map (rand o concl) thml2
  in
    (hd tml2, map sym_def (rev (tl tml2)))
  end

fun fof_translate tm =
  dfind tm (!translate_cache) handle NotFound =>
  let val x = fof_translate_aux ((!tmn_glob),tm) in
    incr tmn_glob;
    translate_cache := dadd tm x (!translate_cache); x
  end

fun fof_translate_thm thm = 
  let val tm = (concl o GEN_ALL o DISCH_ALL) thm in fof_translate tm end

(* -------------------------------------------------------------------------
   TFF Translation
   ------------------------------------------------------------------------- *)

fun strip_funty_aux ty =
  if is_vartype ty then [ty] else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in
          tya :: strip_funty_aux tyb
        end
      else [ty]
    end

fun strip_funty ty = case strip_funty_aux ty of
    [] => raise ERR "strip_funty" ""
  | x => (last x, butlast x)

fun mgty_of c =
  let val {Thy, Name, Ty} = dest_thy_const c in
    type_of (prim_mk_const {Thy = Thy, Name = Name})
  end

fun max_tff_arity c = length (snd (strip_funty (mgty_of c)))

fun APP_CONV_TFF tm =
  if not (is_comb tm) then NO_CONV tm else
    let val (oper,argl) = strip_comb tm in
      if is_const oper andalso length argl > max_tff_arity oper  
      then APP_CONV_MIN tm 
      else NO_CONV tm
    end

val APP_CONV_TFF_REC = TRY_CONV (TOP_SWEEP_CONV APP_CONV_TFF) THENC REFL
  

fun tff_translate tm =
  let 
    val (formula,defl) = fof_translate tm 
    fun rw x = (rhs o concl o APP_CONV_TFF_REC) x
  in
    (rw formula, map rw defl)
  end

fun tff_translate_thm thm = 
  let val tm = (concl o GEN_ALL o DISCH_ALL) thm in tff_translate tm end

end
