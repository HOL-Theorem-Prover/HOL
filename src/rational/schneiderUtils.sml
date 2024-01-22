structure schneiderUtils :> schneiderUtils =
struct

open HolKernel Parse boolLib;

structure Parse =
struct
  open Parse
  val (Type,Term) = parse_from_grammars bool_grammars
end

(* ************************************************************ *)
(* PROP_TAC    : A tautology checker with prop. abstraction     *)
(* REW_PROP_TAC: Same as PROP_TAC, but rewrites first with asm. *)
(* UNDISCH_HD_TAC: UNDISCH with the head of the assumptions     *)
(* UNDISCH_NO_TAC i: UNDISCH the ith assumption                 *)
(* POP_NO_ASSUM i : Takes the ith assumption for a thm_tactic   *)
(* POP_NO_TAC i: Eliminates the ith Assumption                  *)
(* ASM_TAC i: Same as POP_NO_ASSUM, but retains the assumption  *)
(* ASM_LIST_TAC il : Uses a sublist of the assumptions          *)
(* APPLY_ASM_TAC i tac: Applies tac on the ith assumption       *)
(* ************************************************************ *)


fun elem 0 l = hd l | elem i l = elem (i-1) (tl l)
fun delete i l = if i=0 then tl l
                 else (hd l)::(delete (i-1) (tl l))

fun UNDISCH_HD_TAC (asm,g) = (UNDISCH_TAC (hd asm))(asm,g)
fun UNDISCH_ALL_TAC (asm,g) = (MAP_EVERY UNDISCH_TAC asm)(asm,g)
fun UNDISCH_NO_TAC i (asm,g) = (UNDISCH_TAC (elem i asm))(asm,g)
fun POP_NO_ASSUM i thfun (asl,w) = thfun (ASSUME (elem i asl)) ((delete i asl),w)
fun POP_NO_TAC i = POP_NO_ASSUM i (fn x=> ALL_TAC)
fun ASM_TAC i tac (asm,g) = (tac (ASSUME(elem i asm))) (asm,g)
fun ASM_LIST_TAC il tac (asm,g) = (tac (map ASSUME(map (fn i=>elem i asm)il))) (asm,g)

fun REWRITE1_TAC t = REWRITE_TAC[t]


(* ********************** COPY_ASM_NO i *********************** *)
(*                                                              *)
(*                      [a0,...,an] |- g                        *)
(*         ==========================================           *)
(*          [ai,a0,...,ai-1,ai+1,...,an] |- ai ==> g            *)
(* ************************************************************ *)

fun COPY_ASM_NO i =
    ASSUM_LIST (fn thl => let val th = List.nth(thl,i)
                          in
                            UNDISCH_THEN (concl th)
                                         (fn th => MP_TAC th THEN
                                                   ASSUME_TAC th)
                          end)

(* ************************************************************ *)
(* ************************************************************ *)
fun FORALL_UNFREE_CONV t =
    let val (x,f) = dest_forall t
        val lemma = TAC_PROOF(([],“!P.(!x:'a.P) = P”),
                GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[])
        val lemma' = INST_TYPE[alpha |-> type_of x] lemma
     in
        BETA_RULE(SPEC f lemma')
    end


fun FORALL_IN_CONV t =
  if is_forall t then
        let val (x,f) = dest_forall t
         in if x IN FVs f then
                ((FORALL_AND_CONV t) handle HOL_ERR _=> REFL t)
            else FORALL_UNFREE_CONV t
        end else
  if is_abs t then (ABS_CONV FORALL_IN_CONV) t else
  if is_comb t then ((RAND_CONV FORALL_IN_CONV) THENC
                     (RATOR_CONV FORALL_IN_CONV)) t
  else REFL t





(* ********* LEFT_EXISTS_TAC & LEFT_FORALL_TAC **************** *)
(*                                                              *)
(*   ?x.P[x],G|-phi             !x.P[x],G|-phi                  *)
(*  ================           ================ t               *)
(*    P[x'],G|-phi                P[t],G|-phi                   *)
(* ************************************************************ *)

val LEFT_EXISTS_TAC = POP_ASSUM (CHOOSE_THEN ASSUME_TAC)
fun LEFT_FORALL_TAC t = POP_ASSUM (ASSUME_TAC o SPEC t)

(* ******* LEFT_NO_EXISTS_TAC & LEFT_NO_FORALL_TAC ************ *)
(* These tactics do exactly the same as the tactics above, but  *)
(* the quantified formulae need not be the topmost assumption   *)
(* and are therefore specified by their number. Note that the   *)
(* topmost assumption has number 0, then comes 1,...            *)
(* ************************************************************ *)

fun LEFT_NO_EXISTS_TAC i =
        (UNDISCH_NO_TAC i) THEN CONV_TAC LEFT_IMP_EXISTS_CONV
        THEN GEN_TAC THEN DISCH_TAC

fun LEFT_NO_FORALL_TAC i t =
        (UNDISCH_NO_TAC i) THEN CONV_TAC LEFT_IMP_FORALL_CONV
        THEN EXISTS_TAC t THEN DISCH_TAC



(* ********* LEFT_DISJ_TAC & RIGHT_DISJ_TAC ******************* *)
(*                                                              *)
(*      G |- a\/b                       G |- a\/b               *)
(*     ===========                     ===========              *)
(*      G,~b |- a                       G,~a |- b               *)
(* ************************************************************ *)

local
val lem = TAC_PROOF(([],“!a b. a\/b <=> ~b==>a”),
                REPEAT GEN_TAC THEN BOOL_CASES_TAC (“a:bool”)
                THEN REWRITE_TAC[])
in
fun LEFT_DISJ_TAC (asm,g) =
    let
        val (a,b) = dest_disj g
     in (SUBST1_TAC(SPECL[a,b]lem) THEN DISCH_TAC) (asm,g)
    end
end

local
val lem = TAC_PROOF(([],“!a b. a\/b <=> ~a==>b”),
                REPEAT GEN_TAC THEN BOOL_CASES_TAC (“a:bool”)
                THEN REWRITE_TAC[])
in
fun RIGHT_DISJ_TAC (asm,g) =
    let val (a,b) = dest_disj g
     in (SUBST1_TAC(SPECL[a,b]lem) THEN DISCH_TAC) (asm,g)
    end
end


(* ********* LEFT_CONJ_TAC & RIGHT_CONJ_TAC ******************* *)
(*                                                              *)
(*          G |- a/\b                       G |- a/\b           *)
(*     ==================               =================       *)
(*      G |- a  | G,a|- b               G |- b  | G,b|- a       *)
(* ************************************************************ *)

val LEFT_CONJ_TAC = CONJ_ASM1_TAC
val RIGHT_CONJ_TAC = CONJ_ASM2_TAC

(* ********** LEFT_LEMMA_DISJ_CASES_TAC *********************** *)
(* Given a theorem G|-a\/b, these tactics behave as follows:    *)
(*                                                              *)
(*           A|-phi                            A|-phi           *)
(*  ============================   ============================ *)
(*   A,G,a|-phi  A,G,~a,b|-phi      A,G,a,~b|-phi  A,G,b|-phi   *)
(*                                                              *)
(* ************************************************************ *)

local
  val absorb_lem = prove(“!a b. a\/b <=> a \/(~a/\b)”,
                        REPEAT GEN_TAC THEN BOOL_CASES_TAC (“a:bool”)
                        THEN REWRITE_TAC[])
in
fun LEFT_LEMMA_DISJ_CASES_TAC th =
    let val (a,b) = dest_disj (concl th)
     in DISJ_CASES_TAC (EQ_MP (SPECL[a,b]absorb_lem) th) THEN UNDISCH_HD_TAC
        THEN STRIP_TAC
    end
end

local
  val absorb_lem = prove(“!a b. a\/b <=> (a/\~b) \/ b”,
                        REPEAT GEN_TAC THEN BOOL_CASES_TAC (“b:bool”)
                        THEN REWRITE_TAC[])
in
fun RIGHT_LEMMA_DISJ_CASES_TAC th =
    let val (a,b) = dest_disj (concl th)
     in DISJ_CASES_TAC (EQ_MP (SPECL[a,b]absorb_lem) th) THEN UNDISCH_HD_TAC
        THEN STRIP_TAC
    end
end

(* ********************* MY_MP_TAC **************************** *)
(*              A ?- t                                          *)
(*   =======================  MP2_TAC s                         *)
(*   A ?- s  |  A ?- s ==> t                                    *)
(*                                                              *)
(* ************************************************************ *)

fun MY_MP_TAC t = SUBGOAL_THEN t MP_TAC

(* ********************* BOOL_VAR_ELIM_TAC ******************** *)
(* BOOL_VAR_ELIM_CONV v P[v:bool] proves the following theorem  *)
(* |- (!v.P[v]) = P[T] /\ P[F]                                  *)
(* The corresponding tactic looks as follows:                   *)
(*                                                              *)
(*                G |- P[v:bool]                                *)
(*              =================                               *)
(*              G |- P[T] /\ P[F]                               *)
(*                                                              *)
(* Note: This tactic is more useful than BOOL_CASES_TAC if the  *)
(* two formulae P[T] and P[F] are identical. Then the variable  *)
(* v is simply eliminated.                                      *)
(* ************************************************************ *)

local
  val lemma = prove(“!P.(!b.P b) <=> (P T) /\ (P F)”,
                        GEN_TAC THEN EQ_TAC THENL[
                                DISCH_TAC,
                                STRIP_TAC THEN
                                GEN_TAC THEN BOOL_CASES_TAC (“b:bool”)]
                        THEN ASM_REWRITE_TAC[])
in
fun BOOL_VAR_ELIM_CONV v Pv =
        BETA_RULE (SPEC (mk_abs(v,Pv)) lemma)
end


fun BOOL_VAR_ELIM_TAC v (asm,g) =
    let val x = genvar bool
        val Pv = subst[v |-> x]g
        val lemma = snd(EQ_IMP_RULE(BOOL_VAR_ELIM_CONV x Pv))
     in
        (SPEC_TAC(v,x) THEN MATCH_MP_TAC lemma) (asm,g)
    end



(* ************************************************************ *)
(* COND_FUN_EXT_CONV ((c=>f|g)x)  -->                           *)
(*            |- ((c=>f|g)x) = (c => (f x) | (g x))             *)
(* ************************************************************ *)

fun COND_FUN_EXT_CONV condi =
    let val (t,x) = dest_comb condi
        val (c,f,g) = dest_cond t
        val fx = mk_comb(f,x)
        val gx = mk_comb(g,x)
        val t' = mk_cond(c,fx,gx)
        val gl = mk_eq(condi,t')
     in
        prove(gl,COND_CASES_TAC THEN REWRITE_TAC[])
    end

val COND_FUN_EXT_TAC = CONV_TAC (TOP_DEPTH_CONV COND_FUN_EXT_CONV);


end;
