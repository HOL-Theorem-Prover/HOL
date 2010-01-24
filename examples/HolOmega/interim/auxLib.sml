
structure auxLib = struct

local open HolKernel boolLib bossLib in

infix THENC ORELSEC ;

(* strip_left : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  strip_left_n : int -> ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  repeatedly, or n times, strip off something on the left *)
fun strip_left f th =
  let val (v, th1) = f th ;
    val (vs, thf) = strip_left f th1 ;
  in (v :: vs, thf) end
  handle _ => ([], th) ;

fun strip_left_n 0 f th = ([], th)
  | strip_left_n n f th =
    let val (v, th1) = f th ;
      val (vs, thf) = strip_left_n (n-1) f th1 ;
    in (v :: vs, thf) end
    handle _ => ([], th) ;

(* strip_right : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  strip_right_n : int -> ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  repeatedly strip off something on the right *)
fun strip_right f th =
  let fun strip_right' (th', vs) =
      let val (th1, v) = f th' in strip_right' (th1, v :: vs) end
      handle _ => (th', vs)
  in strip_right' (th, []) end ;

fun strip_right_n 0 f th = (th, [])
  | strip_right_n n f th =
    let fun strip_right_n' n (th', vs) =
	let val (th1, v) = f th' in strip_right_n' (n-1) (th1, v :: vs) end
	handle _ => (th', vs)
    in strip_right_n' n (th, []) end ;

(* list_mk_left : ('b * 'a -> 'a) -> 'b list * 'a -> 'a
  repeatedly join something on the left *)
fun list_mk_left f ([], th) = th
  | list_mk_left f (v :: vs, th) = f (v, list_mk_left f (vs, th)) ;

(* list_mk_left_cur : ('b -> 'a -> 'a) -> 'b list -> 'a -> 'a
  repeatedly join something on the left, curried *)
fun list_mk_left_cur f [] th = th
  | list_mk_left_cur f (v :: vs) th = f v (list_mk_left_cur f vs th) ;

(* list_mk_right : ('a * 'b -> 'a) -> 'a * 'b list -> 'a
  repeatedly join something on the right *)
fun list_mk_right f (th, []) = th
  | list_mk_right f (th, v :: vs) = list_mk_right f (f (th, v), vs) ;

(* rec2 : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  repeatedly strip off something on the right *)
fun rec2 f th =
  let fun rec2' (th', vs) =
      let val (th1, v) = f th' in rec2' (th1, v :: vs) end
      handle _ => (th', vs)
  in rec2' (th, []) end ;

(* SPEC_VARL : thm -> term list * thm, like SPECL and SPEC_VAR *)
val SPEC_VARL = strip_left SPEC_VAR ;
val SPEC_TYVARL = strip_left SPEC_TYVAR ;

(* sfg : (thm -> thm) -> thm -> thm
  remove universal quantifiers, apply f, add quantifiers back *)
fun sfg f thm = 
  let val (vars, sthm) = SPEC_VARL thm ;
  in GENL vars (f sthm) end ;

(* tsfg : (thm -> thm) -> thm -> thm
  remove type universal quantifiers, apply f, add quantifiers back *)
fun tsfg f thm =
  let val (tyvars, sthm) = SPEC_TYVARL thm ;
  in TY_GENL tyvars (f sthm) end ;

(* UNDISCH_TERM : thm -> term * thm
  like UNDISCH, but also returns term *) 
fun UNDISCH_TERM th = 
  let val (hy, _) = boolSyntax.dest_imp (concl th) ;
  in (hy, UNDISCH th) end ; 

(* UNDISCH_ALL_TERMS : thm -> term list * thm  
  UNDISCH_N_TERMS : int -> thm -> term list * thm *) 
val UNDISCH_ALL_TERMS = strip_left UNDISCH_TERM ;
fun UNDISCH_N_TERMS n = strip_left_n n UNDISCH_TERM ;

(* DISCH_TERMS : term list -> thm -> thm
  DISCH a list of terms *)
val DISCH_TERMS = list_mk_left_cur Thm.DISCH ; 

(* reo_prems : (term list -> term list) -> thm -> thm
  reorder premises of implication theorem 
  (or can leave some undischarged) *)
fun reo_prems f thm = 
  let val (ps, c) = UNDISCH_ALL_TERMS thm ;
  in DISCH_TERMS (f ps) c end ;

(* ufd : (thm -> thm) -> thm -> thm
  ufdn : int -> (thm -> thm) -> thm -> thm
  ufdl : (thm -> thm list) -> thm -> thm list
  removes implication antecedents, apply f, restores antecedents,
  assumes thm has no assumptions *)
fun ufd f thm = DISCH_ALL (f (UNDISCH_ALL thm)) ;
fun ufdl f thm = map DISCH_ALL (f (UNDISCH_ALL thm)) ;
(* no longer assume thm has no assumptions *)
fun ufd f thm = 
  let val (ps, cth) = UNDISCH_ALL_TERMS thm ;
  in DISCH_TERMS ps (f cth) end ;
fun ufdl f thm = 
  let val (ps, cth) = UNDISCH_ALL_TERMS thm ;
  in map (DISCH_TERMS ps) (f cth) end ;
fun ufdn n f thm = 
  let val (ps, cth) = UNDISCH_N_TERMS n thm ;
  in DISCH_TERMS ps (f cth) end ;

(* takeDrop : int -> 'a list -> 'a list * 'a list
  splits list into two, with n (if there are that many) in first part *) 
fun takeDrop n [] = ([], []) (* ok if list too short *)
  | takeDrop 0 l = ([], l)
  | takeDrop n (h :: t) = 
    let val (tk, dp) = takeDrop (n-1) t in (h :: tk, dp) end ;

infix RS RSN ;
(* RSN : thm * (int * thm) -> thm
  RS : thm * thm -> thm
  as in Isabelle, but doesn't instantiate th *)
fun th RS ith = ufd (fn cth => MATCH_MP ith cth) th ;

fun mf n ps = 
  let val (fps, ant :: rps) = takeDrop (n-1) ps ;
  in ant :: fps @ rps end ;

fun raa m n ps = 
  let val (mps, qps) = takeDrop m ps ;
    val (nps, rps) = takeDrop n qps ;
  in nps @ mps @ rps end ;

fun th RSN (n, ith) = 
  let val (lps, cth) = UNDISCH_ALL_TERMS th ;
    val rith = reo_prems (mf n) ith ;
    val mth = MATCH_MP rith cth ;
    val dmth = DISCH_TERMS lps mth ;
  in reo_prems (raa (length lps) (n-1)) dmth end ;

(* set of functions to take a nested implication and repeatedly remove the
  antecedents by MATCH_MP against the first matching theorem *)

(* first : ('a -> 'b) -> 'a list -> 'b *) 
fun first f (x :: xs) = (f x handle _ => first f xs) 
  | first f [] = raise Empty ;

(* fmmp : thm list -> thm -> thm *) 
fun fmmp ths imp = first (MATCH_MP imp) ths 
  handle Empty => raise HOL_ERR 
    {message = "MATCH_MP fails in all cases", 
      origin_function = "fmmp", origin_structure = "g_adjointScript"} ;

(* repeat : ('a -> 'a) -> 'a -> 'a *) 
fun repeat f x = repeat f (f x) handle _ => x ;

(* thm_from_ass : thm -> thm list -> thm 
  imp_thm is a (nested) implication theorem 
  (antecedent(s) may be conjuncts, which are converted to nested implications),
  try to remove antecedents (from the front only) by resolving with thms *)
fun thm_from_ass imp_thm thms = repeat (fmmp thms)
  (REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO] imp_thm) ;

(* USE_LIM_RES_TAC : thm_tactic -> thm -> tactic 
  resolve implication theorem against assumptions (as in thm_from_ass)
  and use ttac applied to result *)
fun USE_LIM_RES_TAC ttac imp_thm = 
  ASSUM_LIST (ttac o thm_from_ass imp_thm) ;

(* FIRST_REP_RES : thm_tactic -> thm_tactic
  resolves implication theorem against assumptions as much as possible
  and applies ttac to result - backtracking in regard to choice of assumption
  and whether to fully resolve implication theorem *)
fun FIRST_REP_RES ttac impth =
  FIRST_ASSUM (fn ass => FIRST_REP_RES ttac (MATCH_MP impth ass))
  (* following delayed evaluation since ttac impth can cause an 
    error if called with an impth without antecedents removed *)
  ORELSE (fn asg => ttac impth asg) ;

(* select a particular assumption to rewrite with,
  based on the head of the lhs *)

(* lhs_head_var : term -> string
  get name of var which is head of lhs of quantified equality *)
fun lhs_head_var tm = 
  let open boolSyntax
    val (atys, tm') = strip_tyforall tm ;
    val (bvs, stm) = strip_forall tm' ;
    val (lhs, rhs) = dest_eq stm ;
    val (lhs', args) = strip_comb lhs ;
    val (head, tyargs) = strip_tycomb lhs' ;
    val (name, ty) = dest_var head ;
  in name end ;

(* test_lhs_head_var : string -> thm -> thm
  error if assn not a quantified equality, with head of lhs Var (name, ...) *)
fun test_lhs_head_var name assn = 
  if lhs_head_var (concl assn) = name then assn
  else raise HOL_ERR {message = "wrong head variable", 
    origin_function = "test_lhs_head_var",
    origin_structure = "auxLib"} ; 
  
(* to instantiate equality antecedents *)
fun eq_subs th = 
  let open boolLib
    val (ants, cons) = 
      strip_imp (concl (REWRITE_RULE [GSYM AND_IMP_INTRO] th)) ;
    val eqants = filter is_eq ants ;
    (* assume lhs is a variable *)
    fun mksub (lhs, rhs) = lhs |-> rhs ;
  in map (mksub o dest_eq) eqants end ;
  
fun inst_eqs th =  Rewrite.REWRITE_RULE [] (INST (eq_subs th) th) ;

(* useful theorems *)
val iffD1 = 
  (DISCH_ALL o CONJUNCT1 o UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL) EQ_IMP_THM ;

(* abbreviate much used tactics *)
(* farwmmp, frrc_rewr : thm -> tactic,
  for resolving an implicative theorem against the assumptions, 
  in a way which will rewrite, and change, the goal;
  farwmmp resolves implication exactly once, frrc_rewr any number of times *)
fun farwmmp con = (FIRST_ASSUM (fn th =>
  CHANGED_TAC (REWRITE_TAC [MATCH_MP con th]))) ;

fun frrc_rewr impth =
  FIRST_REP_RES (fn th => CHANGED_TAC (REWRITE_TAC [th])) impth ;

(* given f = \x. ..., put into more usual form *)
fun fix_abs_eq rewrs th =
  let val th0 = REWRITE_RULE ([TY_FUN_EQ_THM, FUN_EQ_THM] @ rewrs) th ;
    val th1 = CONV_RULE (DEPTH_CONV TY_BETA_CONV) th0 ;
    val th2 = CONV_RULE (DEPTH_CONV BETA_CONV) th1 ;
  in th2 end ;

fun fix_abs_eq_conv rewrs =
  let val conv0 = REWRITE_CONV ([TY_FUN_EQ_THM, FUN_EQ_THM] @ rewrs) ;
    val conv1 = (DEPTH_CONV (BETA_CONV ORELSEC TY_BETA_CONV)) ;
  in conv0 THENC conv1 end ;

fun fix_abs_eq rewrs = CONV_RULE (fix_abs_eq_conv rewrs) ;

(* given a definition of the form f = \:'a b. \ (c,d) (e,f,g). body
  make it into f [:'a,'b:] (c,d) (e,f,g) = body
  look at making this more efficient ; mk_exp_thm'' seems quickest *)

val exp_convs = [ TY_BETA_CONV, BETA_CONV,
  HO_REWR_CONV pairTheory.FORALL_PROD, REWR_CONV pairTheory.UNCURRY_DEF,
  REWR_CONV TY_FUN_EQ_THM, REWR_CONV FUN_EQ_THM ] ;

val mk_exp_thm = CONV_RULE (REDEPTH_CONV (FIRST_CONV exp_convs)) ;
val mk_exp_thm' = CONV_RULE (TOP_DEPTH_CONV (FIRST_CONV exp_convs)) ;

val exp_rwdconvs = [ HO_REWR_CONV pairTheory.FORALL_PROD, 
  REWR_CONV TY_FUN_EQ_THM, REWR_CONV FUN_EQ_THM ] ;

fun mk_exp_thm'' th0 = 
  let val th2 = CONV_RULE (TOP_SWEEP_CONV (FIRST_CONV exp_rwdconvs)) th0 ;
    val th4 = CONV_RULE (DEPTH_CONV (FIRST_CONV [
      (REWR_CONV pairTheory.UNCURRY_DEF THENC RATOR_CONV BETA_CONV),
      BETA_CONV, TY_BETA_CONV])) th2 ;
  in th4 end ;

val mk_exp_conv'' = (TOP_SWEEP_CONV (FIRST_CONV exp_rwdconvs)) THENC
  (DEPTH_CONV (FIRST_CONV [
    (REWR_CONV pairTheory.UNCURRY_DEF THENC RATOR_CONV BETA_CONV),
    BETA_CONV, TY_BETA_CONV])) ;

(*
mk_exp_thm dist_law_def ;
mk_exp_thm' dist_law_def ;
mk_exp_thm'' dist_law_def ;
*)


end ; (* local open HolKernel bossLib *)

end ; (* structure auxLib *)

