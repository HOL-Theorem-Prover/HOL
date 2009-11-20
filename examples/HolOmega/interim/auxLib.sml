
structure auxLib = struct

(* strip_left : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  repeatedly strip off something on the left *)
fun strip_left f th =
  let val (v, th1) = f th ;
    val (vs, thf) = strip_left f th1 ;
  in (v :: vs, thf) end
  handle _ => ([], th) ;

(* strip_right : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  repeatedly strip off something on the right *)
fun strip_right f th =
  let fun strip_right' (th', vs) =
      let val (th1, v) = f th' in strip_right' (th1, v :: vs) end
      handle _ => (th', vs)
  in strip_right' (th, []) end ;

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
val SPEC_VARL = strip_left Drule.SPEC_VAR ;
val SPEC_TYVARL = strip_left Drule.SPEC_TYVAR ;

local open HolKernel in 

(* sfg : (thm -> thm) -> thm -> thm
  remove universal quantifiers, apply f, add quantifiers back *)
fun sfg f thm = 
  let val (vars, sthm) = SPEC_VARL thm ;
  in GENL vars (f sthm) end ;

(* tsfg : (thm -> thm) -> thm -> thm
  remove type universal quantifiers, apply f, add quantifiers back *)
fun tsfg f thm =
  let val (tyvars, sthm) = SPEC_TYVARL thm ;
  in Drule.TY_GENL tyvars (f sthm) end ;

(* ufd : (thm -> thm) -> thm -> thm
  removes implication antecedents, apply f, restores antecedents,
  assumes thm has no assumptions *)
fun ufd f thm = Drule.DISCH_ALL (f (Drule.UNDISCH_ALL thm)) ;

(* UNDISCH_TERM : thm -> term * thm
  like UNDISCH, but also returns term *) 
fun UNDISCH_TERM th = 
  let val (hy, _) = boolSyntax.dest_imp (concl th) ;
  in (hy, Drule.UNDISCH th) end ; 

(* UNDISCH_ALL_TERMS : thm -> term list * thm *) 
val UNDISCH_ALL_TERMS = strip_left UNDISCH_TERM ;

(* DISCH_TERMS : term list -> thm -> thm
  DISCH a list of terms *)
val DISCH_TERMS = list_mk_left_cur Thm.DISCH ; 

(* set of functions to take a nested implication and repeatedly remove the
  antecedents by MATCH_MP against the first matching theorem *)

(* first : ('a -> 'b) -> 'a list -> 'b *) 
fun first f (x :: xs) = (f x handle _ => first f xs) 
  | first f [] = raise Empty ;

(* fmmp : thm list -> thm -> thm *) 
fun fmmp ths imp = first (Drule.MATCH_MP imp) ths 
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
  (Rewrite.REWRITE_RULE [Conv.GSYM boolTheory.AND_IMP_INTRO] imp_thm) ;

(* USE_LIM_RES_TAC : thm_tactic -> thm -> tactic 
  resolve implication theorem against assumptions (as in thm_from_ass)
  and use ttac applied to result *)
fun USE_LIM_RES_TAC ttac imp_thm = 
  Tactical.ASSUM_LIST (ttac o thm_from_ass imp_thm) ;

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
fun inst_eqs th = 
  let open boolLib
    val (ants, cons) = 
      strip_imp (concl (REWRITE_RULE [GSYM AND_IMP_INTRO] th)) ;
    val eqants = filter is_eq ants ;
    (* assume lhs is a variable *)
    fun mksub (lhs, rhs) = lhs |-> rhs ;
    val subs = map (mksub o dest_eq) eqants ;
  in Rewrite.REWRITE_RULE [] (INST subs th) end ;

(* useful theorems *)
local open boolLib in
val iffD1 = 
  (DISCH_ALL o CONJUNCT1 o UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL) EQ_IMP_THM ;
end ;
end ; (* local open HolKernel *)

end ; (* structure auxLib *)

