(* ===================================================================== *)
(* FILE          : pairScript.sml                                        *)
(* DESCRIPTION   : The theory of pairs. This is a mix of the original    *)
(*                 non-definitional theory of pairs from hol88           *)
(*                 and John Harrison's definitional theory of pairs from *)
(*                 GTT, plus some subsequent simplifications from        *)
(*                 Konrad Slind.                                         *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, John Harrison, Konrad Slind          *)
(*                 Jim Grundy                                            *)
(*                 University of Cambridge                               *)
(* DATE          : August 7, 1997                                        *)
(* ===================================================================== *)

(*  interactive use:
 app load ["Q", "relationTheory", "mesonLib", "OpenTheoryMap", "BasicProvers"];
 open Parse relationTheory mesonLib;
*)

open HolKernel Parse boolLib relationTheory mesonLib metisLib
open quotientLib simpLib boolSimps BasicProvers

local open computeLib in end

val _ = new_theory "pair";

fun simp ths = simpLib.asm_simp_tac (srw_ss()) ths (* don't eta-reduce *)

(*---------------------------------------------------------------------------*)
(* Define the type of pairs and tell the grammar about it.                   *)
(*---------------------------------------------------------------------------*)

val pairfn = Term `\a b. (a=x) /\ (b=y)`;

val PAIR_EXISTS = Q.prove
(`?p:'a -> 'b -> bool. (\p. ?x y. p = ^pairfn) p`,
 BETA_TAC
  THEN Ho_Rewrite.ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN Q.EXISTS_TAC `x`
  THEN Ho_Rewrite.ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN Q.EXISTS_TAC `y`
  THEN EXISTS_TAC pairfn
  THEN REFL_TAC);

val ABS_REP_prod =
 let val tydef = new_type_definition("prod", PAIR_EXISTS)
 in
   define_new_type_bijections
      {ABS="ABS_prod", REP="REP_prod",
       name="ABS_REP_prod", tyax=tydef}
 end;

val _ = add_infix_type
         {Prec = 70,
          ParseName = SOME "#", Name = "prod",
          Assoc = HOLgrammars.RIGHT};
val _ = TeX_notation { hol = "#", TeX = ("\\HOLTokenProd{}", 1)}
local
  open OpenTheoryMap
  val ns = ["Data","Pair"]
in
  val _ = OpenTheory_tyop_name{tyop={Thy="pair",Tyop="prod"},name=(ns,"*")}
  fun ot0 x y = OpenTheory_const_name{const={Thy="pair",Name=x},name=(ns,y)}
  fun ot x = ot0 x x
end

val REP_ABS_PAIR = Q.prove
(`!x y. REP_prod (ABS_prod ^pairfn) = ^pairfn`,
 REPEAT GEN_TAC
  THEN REWRITE_TAC [SYM (SPEC pairfn (CONJUNCT2 ABS_REP_prod))]
  THEN BETA_TAC
  THEN MAP_EVERY Q.EXISTS_TAC [`x`, `y`]
  THEN REFL_TAC);


(*---------------------------------------------------------------------------*)
(*  Define the constructor for pairs, and install grammar rule for it.       *)
(*---------------------------------------------------------------------------*)

val COMMA_DEF =
 Q.new_definition
  ("COMMA_DEF[notuserdef]",
   `$, x y = ABS_prod ^pairfn`);
val _ = ot","

val _ = add_rule {term_name = ",", fixity = Infixr 50,
                  pp_elements = [TOK ",", BreakSpace(0,0)],
                  paren_style = ParoundName,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 0))};


(*---------------------------------------------------------------------------
     The constructor for pairs is one-to-one.
 ---------------------------------------------------------------------------*)

val PAIR_EQ = Q.store_thm
("PAIR_EQ",
 `((x,y) = (a,b)) <=> (x=a) /\ (y=b)`,
 EQ_TAC THENL
 [REWRITE_TAC[COMMA_DEF]
   THEN DISCH_THEN(MP_TAC o Q.AP_TERM `REP_prod`)
   THEN REWRITE_TAC [REP_ABS_PAIR]
   THEN Ho_Rewrite.REWRITE_TAC [FUN_EQ_THM]
   THEN DISCH_THEN (MP_TAC o Q.SPECL [`x`,  `y`])
   THEN REWRITE_TAC[],
  STRIP_TAC THEN ASM_REWRITE_TAC[]]);

Theorem CLOSED_PAIR_EQ[simp,compute] = itlist Q.GEN [`x`, `y`, `a`, `b`] PAIR_EQ;


(*---------------------------------------------------------------------------
     Case analysis for pairs.
 ---------------------------------------------------------------------------*)

val ABS_PAIR_THM = Q.store_thm
("ABS_PAIR_THM",
 `!x. ?q r. x = (q,r)`,
 GEN_TAC THEN REWRITE_TAC[COMMA_DEF]
  THEN MP_TAC(Q.SPEC `REP_prod x` (CONJUNCT2 ABS_REP_prod))
  THEN REWRITE_TAC[CONJUNCT1 ABS_REP_prod] THEN BETA_TAC
  THEN DISCH_THEN(Q.X_CHOOSE_THEN `a` (Q.X_CHOOSE_THEN `b` MP_TAC))
  THEN DISCH_THEN(MP_TAC o Q.AP_TERM `ABS_prod`)
  THEN REWRITE_TAC[CONJUNCT1 ABS_REP_prod]
  THEN DISCH_THEN SUBST1_TAC
  THEN MAP_EVERY Q.EXISTS_TAC [`a`, `b`]
  THEN REFL_TAC);

val pair_CASES = save_thm("pair_CASES", ABS_PAIR_THM)


(*---------------------------------------------------------------------------*
 * Surjective pairing and definition of projection functions.                *
 *                                                                           *
 *        PAIR = |- !x. (FST x,SND x) = x                                    *
 *        FST  = |- !x y. FST (x,y) = x                                      *
 *        SND  = |- !x y. SND (x,y) = y                                      *
 *---------------------------------------------------------------------------*)

val PAIR =
 boolLib.new_specification
  ("PAIR[simp]", ["FST","SND"],
   Ho_Rewrite.REWRITE_RULE[SKOLEM_THM] (GSYM ABS_PAIR_THM));

local val th1 = REWRITE_RULE [PAIR_EQ] (SPEC (Term`(x,y):'a#'b`) PAIR)
      val (th2,th3) = (CONJUNCT1 th1, CONJUNCT2 th1)
in
Theorem FST[simp,compute] = itlist Q.GEN [`x`,`y`] th2;
Theorem SND[simp,compute] = itlist Q.GEN [`x`,`y`] th3;
end;
val _ = ot0 "FST" "fst"
val _ = ot0 "SND" "snd"

val PAIR_FST_SND_EQ = store_thm(
  "PAIR_FST_SND_EQ",
  ``!(p:'a # 'b) q. (p = q) <=> (FST p = FST q) /\ (SND p = SND q)``,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN ``p1:'a`` (X_CHOOSE_THEN ``p2:'b`` SUBST_ALL_TAC)
                (SPEC ``p:'a # 'b`` ABS_PAIR_THM) THEN
  X_CHOOSE_THEN ``q1:'a`` (X_CHOOSE_THEN ``q2:'b`` SUBST_ALL_TAC)
                (SPEC ``q:'a # 'b`` ABS_PAIR_THM) THEN
  REWRITE_TAC [PAIR_EQ, FST, SND]);

val SWAP_def = new_definition ("SWAP_def", ``SWAP a = (SND a, FST a)``)

(* Theorem the SWAP inverts itself *)
Theorem SWAP_SWAP[simp]:
    !x. SWAP (SWAP x) = x
Proof
    simp[SWAP_def]
QED

(*---------------------------------------------------------------------------*)
(* CURRY and UNCURRY. UNCURRY is needed for terms of the form `\(x,y).t`     *)
(*---------------------------------------------------------------------------*)

val CURRY_DEF = Q.new_definition ("CURRY_DEF", `CURRY f x y :'c = f (x,y)`);
val _ = BasicProvers.export_rewrites ["CURRY_DEF"]

val UNCURRY = Q.new_definition
  ("UNCURRY",
   `UNCURRY f (v:'a#'b) = f (FST v) (SND v)`);
val _ = ot0 "UNCURRY" "uncurry"

val UNCURRY_VAR = save_thm("UNCURRY_VAR", UNCURRY);  (* compatibility *)

val ELIM_UNCURRY = Q.store_thm(
  "ELIM_UNCURRY",
  `!f:'a -> 'b -> 'c. UNCURRY f = \x. f (FST x) (SND x)`,
  GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
  REWRITE_TAC [UNCURRY] THEN CONV_TAC (RAND_CONV BETA_CONV) THEN
  REFL_TAC);

Theorem UNCURRY_DEF[simp,compute]:
    !f x y. UNCURRY f (x,y) :'c = f x y
Proof
  REWRITE_TAC [UNCURRY,FST,SND]
QED

Theorem IN_UNCURRY_R[simp]:
  (x,y) IN UNCURRY R <=> R x y
Proof
  simp[IN_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* CURRY_UNCURRY_THM = |- !f. CURRY(UNCURRY f) = f                           *)
(* ------------------------------------------------------------------------- *)

val CURRY_UNCURRY_THM =
    let val th1 = prove
                (“CURRY (UNCURRY (f:'a->'b->'c)) x y = f x y”,
                 REWRITE_TAC [UNCURRY_DEF, CURRY_DEF])
        val th2 = GEN “y:'b” th1
        val th3 = EXT th2
        val th4 = GEN “x:'a” th3
        val th4 = EXT th4
    in
        GEN “f:'a->'b->'c” th4
    end;
Theorem CURRY_UNCURRY_THM[simp] = CURRY_UNCURRY_THM

(* ------------------------------------------------------------------------- *)
(* UNCURRY_CURRY_THM = |- !f. UNCURRY(CURRY f) = f                           *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_CURRY_THM =
  let val th1 = prove
        (“UNCURRY (CURRY (f:('a#'b)->'c)) (x,y) = f(x,y)”,
         REWRITE_TAC [CURRY_DEF, UNCURRY_DEF])
      val th2 = Q.INST [`x:'a` |-> `FST (z:'a#'b)`,
                        `y:'b` |-> `SND (z:'a#'b)`] th1
      val th3 = CONV_RULE (RAND_CONV
                    (RAND_CONV (K (ISPEC “z:'a#'b” PAIR))))  th2
      val th4 = CONV_RULE(RATOR_CONV (RAND_CONV
                   (RAND_CONV (K (ISPEC “z:'a#'b” PAIR)))))th3
      val th5 = GEN “z:'a#'b” th4
      val th6 = EXT th5
  in
        GEN “f:('a#'b)->'c” th6
  end;

Theorem UNCURRY_CURRY_THM[simp] = UNCURRY_CURRY_THM;

(* ------------------------------------------------------------------------- *)
(* CURRY_ONE_ONE_THM = |- (CURRY f = CURRY g) = (f = g)                      *)
(* ------------------------------------------------------------------------- *)

val CURRY_ONE_ONE_THM =
    let val th1 = ASSUME “(f:('a#'b)->'c) = g”
        val th2 = AP_TERM “CURRY:(('a#'b)->'c)->('a->'b->'c)” th1
        val th3 = DISCH_ALL th2
        val thA = ASSUME “(CURRY (f:('a#'b)->'c)) = (CURRY g)”
        val thB = AP_TERM “UNCURRY:('a->'b->'c)->(('a#'b)->'c)” thA
        val thC = PURE_REWRITE_RULE [UNCURRY_CURRY_THM] thB
        val thD = DISCH_ALL thC
    in
        IMP_ANTISYM_RULE thD th3
    end;

Theorem CURRY_ONE_ONE_THM[simp] = CURRY_ONE_ONE_THM;

(* ------------------------------------------------------------------------- *)
(* UNCURRY_ONE_ONE_THM = |- (UNCURRY f = UNCURRY g) = (f = g)                *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_ONE_ONE_THM =
    let val th1 = ASSUME “(f:'a->'b->'c) = g”
        val th2 = AP_TERM “UNCURRY:('a->'b->'c)->(('a#'b)->'c)” th1
        val th3 = DISCH_ALL th2
        val thA = ASSUME “(UNCURRY (f:'a->'b->'c)) = (UNCURRY g)”
        val thB = AP_TERM “CURRY:(('a#'b)->'c)->('a->'b->'c)” thA
        val thC = PURE_REWRITE_RULE [CURRY_UNCURRY_THM] thB
        val thD = DISCH_ALL thC
    in
        IMP_ANTISYM_RULE thD th3
    end;

Theorem UNCURRY_ONE_ONE_THM[simp] = UNCURRY_ONE_ONE_THM;

(* ----------------------------------------------------------------------
    UNCURRY_EQ = |- UNCURRY f x = y <=> ?a b. x = (a,b) /\ f a b = y

    (given that UNCURRY = flip pair_CASE, this is the "case equality"
     theorem recast)
   ---------------------------------------------------------------------- *)

Theorem UNCURRY_EQ:
  UNCURRY f x = y <=> ?a b. x = (a,b) /\ f a b = y
Proof
  Q.SPEC_THEN ‘x’ STRIP_ASSUME_TAC pair_CASES >>
  ASM_SIMP_TAC bool_ss [UNCURRY_DEF, PAIR_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* pair_Axiom = |- !f. ?fn. !x y. fn (x,y) = f x y                           *)
(* ------------------------------------------------------------------------- *)

val pair_Axiom = Q.store_thm("pair_Axiom",
 `!f:'a->'b->'c. ?fn. !x y. fn (x,y) = f x y`,
 GEN_TAC THEN Q.EXISTS_TAC`UNCURRY f` THEN REWRITE_TAC[UNCURRY_DEF]);

(* -------------------------------------------------------------------------*)
(*   UNCURRY_CONG =                                                         *)
(*           |- !f' f M' M.                                                 *)
(*                (M = M') /\                                               *)
(*                (!x y. (M' = (x,y)) ==> (f x y = f' x y))                 *)
(*                     ==>                                                  *)
(*                (UNCURRY f M = UNCURRY f' M')                             *)
(* -------------------------------------------------------------------------*)

val UNCURRY_CONG = store_thm(
  "UNCURRY_CONG",
  ``!f' f M' M.
       (M = M') /\ (!x y. (M' = (x,y)) ==> (f x y = f' x y)) ==>
       (UNCURRY f M = UNCURRY f' M')``,
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC pair_CASES THEN
  Q.SPEC_THEN `M'` FULL_STRUCT_CASES_TAC pair_CASES THEN
  FULL_SIMP_TAC bool_ss [PAIR_EQ, UNCURRY_DEF])

(*---------------------------------------------------------------------------
         LAMBDA_PROD = |- !P. (\p. P p) = (\(p1,p2). P (p1,p2))
 ---------------------------------------------------------------------------*)

val LAMBDA_PROD = Q.store_thm("LAMBDA_PROD",
`!P:'a#'b->'c. (\p. P p) = \(p1,p2). P(p1,p2)`,
 GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
   THEN STRUCT_CASES_TAC (Q.SPEC `p` ABS_PAIR_THM)
   THEN REWRITE_TAC [UNCURRY,FST,SND]
   THEN BETA_TAC THEN REFL_TAC)

(*---------------------------------------------------------------------------
         EXISTS_PROD = |- (?p. P p) = ?p_1 p_2. P (p_1,p_2)
 ---------------------------------------------------------------------------*)

val EXISTS_PROD = Q.store_thm("EXISTS_PROD",
 `(?p. P p) = ?p_1 p_2. P (p_1,p_2)`,
 EQ_TAC THEN STRIP_TAC
   THENL [MAP_EVERY Q.EXISTS_TAC [`FST p`, `SND p`], Q.EXISTS_TAC `p_1, p_2`]
   THEN ASM_REWRITE_TAC[PAIR]);

(*---------------------------------------------------------------------------
         FORALL_PROD = |- (!p. P p) = !p_1 p_2. P (p_1,p_2)
 ---------------------------------------------------------------------------*)

val FORALL_PROD = Q.store_thm("FORALL_PROD",
 `(!p. P p) = !p_1 p_2. P (p_1,p_2)`,
 EQ_TAC THENL
   [DISCH_THEN(fn th => REPEAT GEN_TAC THEN ASSUME_TAC (Q.SPEC `p_1, p_2` th)),
    REPEAT STRIP_TAC
      THEN REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC (Q.SPEC `p` ABS_PAIR_THM)
   ]
 THEN ASM_REWRITE_TAC[]);


Theorem pair_induction = #2(EQ_IMP_RULE FORALL_PROD) |> GEN_ALL

(* ----------------------------------------------------------------------
    PROD_ALL
   ---------------------------------------------------------------------- *)

val PROD_ALL_def = new_definition(
  "PROD_ALL_def",
  ``PROD_ALL (P:'a -> bool) (Q : 'b -> bool) p <=> P (FST p) /\ Q (SND p)``);

Theorem PROD_ALL_THM[simp,compute]:
  PROD_ALL P Q (x:'a,y:'b) <=> P x /\ Q y
Proof REWRITE_TAC [PROD_ALL_def, FST, SND]
QED

val PROD_ALL_MONO = store_thm(
  "PROD_ALL_MONO",
  ``(!x:'a. P x ==> P' x) /\ (!y:'b. Q y ==> Q' y) ==>
    PROD_ALL P Q p ==> PROD_ALL P' Q' p``,
  Q.SPEC_THEN `p` STRUCT_CASES_TAC ABS_PAIR_THM THEN
  REWRITE_TAC [PROD_ALL_THM] THEN REPEAT STRIP_TAC THEN RES_TAC);
val _ = IndDefLib.export_mono "PROD_ALL_MONO"

val PROD_ALL_CONG = store_thm(
  "PROD_ALL_CONG",
  ``!p p' P P' Q Q'.
      (p = p') /\ (!x:'a y:'b. (p' = (x,y)) ==> (P x <=> P' x)) /\
      (!x:'a y:'b. (p' = (x,y)) ==> (Q y <=> Q' y)) ==>
      (PROD_ALL P Q p <=> PROD_ALL P' Q' p')``,
  SIMP_TAC (BasicProvers.srw_ss()) [FORALL_PROD, PAIR_EQ]);

(* ------------------------------------------------------------------------- *)
(* ELIM_PEXISTS = |- !P. (?p. P (FST p) (SND p)) = ?p1 p2. P p1 p2           *)
(* ------------------------------------------------------------------------- *)

val ELIM_PEXISTS = Q.store_thm
("ELIM_PEXISTS",
 `(?p. P (FST p) (SND p)) = ?p1 p2. P p1 p2`,
 EQ_TAC THEN STRIP_TAC THENL
 [MAP_EVERY Q.EXISTS_TAC [`FST p`, `SND p`] THEN ASM_REWRITE_TAC [],
  Q.EXISTS_TAC `(p1,p2)` THEN ASM_REWRITE_TAC [FST,SND]]);

(* ------------------------------------------------------------------------- *)
(* ELIM_PFORALL = |- !P. (!p. P (FST p) (SND p)) = !p1 p2. P p1 p2           *)
(* ------------------------------------------------------------------------- *)

val ELIM_PFORALL = Q.store_thm
("ELIM_PFORALL",
 `(!p. P (FST p) (SND p)) = !p1 p2. P p1 p2`,
 EQ_TAC THEN REPEAT STRIP_TAC THENL
 [POP_ASSUM (MP_TAC o Q.SPEC `(p1,p2)`) THEN REWRITE_TAC [FST,SND],
  ASM_REWRITE_TAC []]);

(* ------------------------------------------------------------------------- *)
(* PFORALL_THM = |- !P. (!x y. P x y) = (!(x,y). P x y)                      *)
(* ------------------------------------------------------------------------- *)

val PFORALL_THM = Q.store_thm
("PFORALL_THM",
 `!P:'a -> 'b -> bool. (!x y. P x y) = !(x,y). P x y`,
 REWRITE_TAC [ELIM_UNCURRY] THEN BETA_TAC THEN
 MATCH_ACCEPT_TAC (GSYM ELIM_PFORALL));

(* ------------------------------------------------------------------------- *)
(* PEXISTS_THM = |- !P. (?x y. P x y) = (?(x,y). P x y)                      *)
(* ------------------------------------------------------------------------- *)

val PEXISTS_THM = Q.store_thm
("PEXISTS_THM",
 `!P:'a -> 'b -> bool. (?x y. P x y) = ?(x,y). P x y`,
 REWRITE_TAC [ELIM_UNCURRY] THEN BETA_TAC THEN
 MATCH_ACCEPT_TAC (GSYM ELIM_PEXISTS));


(* ------------------------------------------------------------------------- *)
(* Rewrite versions of ELIM_PEXISTS and ELIM_PFORALL                         *)
(* ------------------------------------------------------------------------- *)

val ELIM_PEXISTS_EVAL = Q.store_thm
("ELIM_PEXISTS_EVAL",
 `$? (UNCURRY (\x. P x)) = ?x. $? (P x)`,
 Q.SUBGOAL_THEN `!x. P x = \y. P x y` (fn th => ONCE_REWRITE_TAC [th]) THEN
 REWRITE_TAC [ETA_THM, PEXISTS_THM]);

val ELIM_PFORALL_EVAL = Q.store_thm
("ELIM_PFORALL_EVAL",
 `$! (UNCURRY (\x. P x)) = !x. $! (P x)`,
 Q.SUBGOAL_THEN `!x. P x = \y. P x y` (fn th => ONCE_REWRITE_TAC [th]) THEN
 REWRITE_TAC [ETA_THM, PFORALL_THM]);

(*---------------------------------------------------------------------------
        Map for pairs
 ---------------------------------------------------------------------------*)

val PAIR_MAP = Q.new_infixr_definition
 ("PAIR_MAP",
  `$## (f:'a->'c) (g:'b->'d) p = (f (FST p), g (SND p))`, 490);

Theorem PAIR_MAP_THM[simp,compute]:
  !f g x y. (f##g) (x,y) = (f x, g y)
Proof REWRITE_TAC [PAIR_MAP,FST,SND]
QED

Theorem FST_PAIR_MAP[simp]:
  !p f g. FST ((f ## g) p) = f (FST p)
Proof REWRITE_TAC [PAIR_MAP, FST]
QED

Theorem SND_PAIR_MAP[simp]:
  !p f g. SND ((f ## g) p) = g (SND p)
Proof REWRITE_TAC [PAIR_MAP, SND]
QED

Theorem PAIR_MAP_I[simp,quotient_simp]:
  (I ## I) = (I : 'a # 'b -> 'a # 'b)
Proof
  simp[FUN_EQ_THM, FORALL_PROD]
QED


(*---------------------------------------------------------------------------
        Distribution laws for paired lets. Only will work for the
        exact form given. See also boolTheory.
 ---------------------------------------------------------------------------*)

val LET2_RAND = Q.store_thm("LET2_RAND",
`!(P:'c->'d) (M:'a#'b) N.
    P (let (x,y) = M in N x y) = (let (x,y) = M in P (N x y))`,
REWRITE_TAC[boolTheory.LET_DEF] THEN REPEAT GEN_TAC THEN BETA_TAC
 THEN REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC
       (SPEC (Term `M:'a#'b`) ABS_PAIR_THM)
 THEN REWRITE_TAC[UNCURRY_DEF] THEN BETA_TAC THEN REFL_TAC);

val LET2_RATOR = Q.store_thm("LET2_RATOR",
`!(M:'a1#'a2) (N:'a1->'a2->'b->'c) (b:'b).
      (let (x,y) = M in N x y) b = let (x,y) = M in N x y b`,
REWRITE_TAC [boolTheory.LET_DEF] THEN BETA_TAC
  THEN REWRITE_TAC [UNCURRY_VAR] THEN BETA_TAC
  THEN REWRITE_TAC[]);

val o_UNCURRY_R = store_thm(
  "o_UNCURRY_R",
  ``f o UNCURRY g = UNCURRY ((o) f o g)``,
  SRW_TAC [][FUN_EQ_THM, UNCURRY]);

val C_UNCURRY_L = store_thm(
  "C_UNCURRY_L",
  ``combin$C (UNCURRY f) x = UNCURRY (combin$C (combin$C o f) x)``,
  SRW_TAC [][FUN_EQ_THM, UNCURRY]);

val S_UNCURRY_R = store_thm(
  "S_UNCURRY_R",
  ``S f (UNCURRY g) = UNCURRY (S (S o ((o) f) o (,)) g)``,
  SRW_TAC [][FUN_EQ_THM, UNCURRY, PAIR]);

val UNCURRY' = prove(
  ``UNCURRY f = \p. f (FST p) (SND p)``,
  SRW_TAC [][FUN_EQ_THM, UNCURRY]);

val FORALL_UNCURRY = store_thm(
  "FORALL_UNCURRY",
  ``(!) (UNCURRY f) = (!) ((!) o f)``,
  SRW_TAC [][UNCURRY', combinTheory.o_DEF] THEN
  Q.SUBGOAL_THEN `!x. f x = \y. f x y` (fn th => ONCE_REWRITE_TAC [th]) THENL [
    REWRITE_TAC [FUN_EQ_THM] THEN BETA_TAC THEN REWRITE_TAC [],
    ALL_TAC
  ] THEN
  SRW_TAC [][FORALL_PROD, FST, SND]);

(* --------------------------------------------------------------------- *)
(* A nice theorem from Tom Melham, lifted from examples/lambda/ncScript  *)
(* States ability to express a function:                                 *)
(*                                                                       *)
(*    h : A -> B x C                                                     *)
(*                                                                       *)
(* as the combination h = <f,g> of two component functions               *)
(*                                                                       *)
(*   f : A -> B   and   g : A -> C                                       *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

val PAIR_FUN_THM = Q.store_thm
("PAIR_FUN_THM",
 `!P. (?!f:'a->('b#'c). P f) =
      (?!p:('a->'b)#('a->'c). P(\a.(FST p a, SND p a)))`,
RW_TAC bool_ss [EXISTS_UNIQUE_THM]
 THEN EQ_TAC THEN RW_TAC bool_ss []
 THENL
  [Q.EXISTS_TAC `FST o f, SND o f`
    THEN RW_TAC bool_ss [FST,SND,combinTheory.o_THM,PAIR,ETA_THM],
   STRIP_ASSUME_TAC (Q.ISPEC `p:('a -> 'b) # ('a -> 'c)` ABS_PAIR_THM) THEN
   STRIP_ASSUME_TAC (Q.ISPEC `p':('a -> 'b) # ('a -> 'c)` ABS_PAIR_THM)
    THEN RW_TAC bool_ss []
    THEN RULE_ASSUM_TAC (REWRITE_RULE [FST,SND])
    THEN ``(\a:'a. (q a:'b,r a:'c)) = (\a:'a. (q' a:'b,r' a:'c))`` via RES_TAC
    THEN simpLib.FULL_SIMP_TAC bool_ss [FUN_EQ_THM,PAIR_EQ],
   PROVE_TAC[],
   Q.PAT_ASSUM `$! M`
      (MP_TAC o Q.SPECL [`(FST o f, SND o f)`, `(FST o y, SND o y)`])
     THEN RW_TAC bool_ss [FST,SND,combinTheory.o_THM,
                          PAIR,PAIR_EQ,FUN_EQ_THM,ETA_THM]
     THEN PROVE_TAC [PAIR_EQ,PAIR]]);


(*---------------------------------------------------------------------------
       TFL support.
 ---------------------------------------------------------------------------*)

val pair_CASE_def =
  new_definition("pair_CASE_def",
                 “pair_CASE (p:('a#'b)) f = f (FST p) (SND p)”)
val _ = ot0 "pair_case" "case"

Theorem pair_case_thm =
  pair_CASE_def |> Q.SPEC ‘(x,y)’ |> REWRITE_RULE [FST, SND] |> SPEC_ALL

(* and, to be consistent with what would be generated if we could use
   Hol_datatype to generate the pair type: *)
Theorem pair_case_def = pair_case_thm
Overload case = “pair_CASE”


Theorem pair_CASE_UNCURRY:
  pair_CASE = flip UNCURRY
Proof
  SIMP_TAC bool_ss [FUN_EQ_THM, pair_CASE_def, combinTheory.C_DEF, UNCURRY]
QED

val pair_case_cong = save_thm("pair_case_cong",
  Prim_rec.case_cong_thm pair_CASES pair_case_thm);
val pair_rws = [PAIR, FST, SND];

Theorem pair_case_eq:
  (pair_CASE p f = v) <=> ?x y. (p = (x,y)) /\ (f x y = v)
Proof
  SIMP_TAC bool_ss [pair_CASE_UNCURRY, UNCURRY_EQ, combinTheory.C_DEF]
QED

val pair_case_ho_elim = Q.store_thm(
  "pair_case_ho_elim",
  ‘!f'. f'(pair_CASE p f) = (?x y. p = (x,y) /\ f'(f x y))’,
  strip_tac THEN
  Q.ISPEC_THEN ‘p’ STRUCT_CASES_TAC pair_CASES THEN
  SRW_TAC[][pair_CASE_def, FST, SND, PAIR_EQ]);

val _ = TypeBase.export [
      TypeBasePure.mk_datatype_info_no_simpls {
        ax=TypeBasePure.ORIG pair_Axiom,
        case_def=pair_case_thm,
        case_cong=pair_case_cong,
        case_eq = pair_case_eq,
        case_elim = pair_case_ho_elim,
        induction=TypeBasePure.ORIG pair_induction,
        nchotomy=ABS_PAIR_THM,
        size=NONE,
        encode=NONE,
        fields=[],
        accessors=[],
        updates=[],
        destructors=[FST,SND],
        recognizers=[],
        lift=SOME(mk_var("pairSyntax.lift_prod",
                         “:'type -> ('a -> 'term) -> ('b -> 'term) -> 'a # 'b ->
                           'term”)),
        one_one=SOME CLOSED_PAIR_EQ,
        distinct=NONE
      }
    ];

(*---------------------------------------------------------------------------
    Generate some ML that gets evaluated at theory load time.

    The TFL definition package uses "pair_case" as a case construct,
    rather than UNCURRY. This (apparently) solves a deeply buried
    problem in termination condition extraction involving paired
    beta-reduction.

 ---------------------------------------------------------------------------*)



val S = PP.add_string and NL = PP.NL and B = PP.block PP.CONSISTENT 0

val _ = adjoin_to_theory
{sig_ps = SOME(fn _ => S "val pair_rws : thm list"),
 struct_ps = SOME(fn _ => S "val pair_rws = [PAIR, FST, SND];")};

val datatype_pair = store_thm(
  "datatype_pair",
  ``DATATYPE (pair ((,) : 'a -> 'b -> 'a # 'b))``,
  REWRITE_TAC [DATATYPE_TAG_THM]);


(*---------------------------------------------------------------------------
                 Wellfoundedness and pairs.
 ---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * The lexicographic combination of two wellfounded orderings is wellfounded.
 * The minimal element of this relation is found by
 *
 *    1. Finding the set of first elements of the pairs in B
 *    2. That set is non-empty, so it has an R-minimal element, call it min
 *    3. Find the set of second elements of those pairs in B whose first
 *       element is min.
 *    4. This set is non-empty, so it has a Q-minimal element, call it min'.
 *    5. A minimal element is (min,min').
 *---------------------------------------------------------------------------*)

val LEX_DEF =
Q.new_infixr_definition
("LEX_DEF",
  `$LEX (R1:'a->'a->bool) (R2:'b->'b->bool)
     =
   \(s,t) (u,v). R1 s u \/ (s=u) /\ R2 t v`, 490);

val LEX_DEF_THM = Q.store_thm
("LEX_DEF_THM",
 `(R1 LEX R2) (a,b) (c,d) <=> R1 a c \/ (a = c) /\ R2 b d`,
  REWRITE_TAC [LEX_DEF,UNCURRY_DEF] THEN BETA_TAC THEN
  REWRITE_TAC [UNCURRY_DEF] THEN BETA_TAC THEN REFL_TAC);

val LEX_MONO = store_thm("LEX_MONO",
  ``(!x y. R1 x y ==> R2 x y) /\
    (!x y. R3 x y ==> R4 x y)
    ==>
    (R1 LEX R3) x y ==> (R2 LEX R4) x y``,
  STRIP_TAC THEN
  Q.SPEC_THEN`x`FULL_STRUCT_CASES_TAC pair_CASES THEN
  Q.SPEC_THEN`y`FULL_STRUCT_CASES_TAC pair_CASES THEN
  SRW_TAC[][LEX_DEF_THM] THEN
  PROVE_TAC[])
val () = IndDefLib.export_mono"LEX_MONO";

val WF_LEX = Q.store_thm("WF_LEX",
 `!(R:'a->'a->bool) (Q:'b->'b->bool). WF R /\ WF Q ==> WF (R LEX Q)`,
REWRITE_TAC [LEX_DEF, relationTheory.WF_DEF]
  THEN CONV_TAC (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
  THEN REPEAT STRIP_TAC
  THEN Q.SUBGOAL_THEN `?w1. (\v. ?y. B (v,y)) w1`  STRIP_ASSUME_TAC THENL
  [BETA_TAC THEN MAP_EVERY Q.EXISTS_TAC [`FST w`, `SND w`]
     THEN ASM_REWRITE_TAC pair_rws,
   Q.SUBGOAL_THEN
   `?min. (\v. ?y. B (v,y)) min
         /\ !b. R b min ==>
               ~(\v. ?y. B (v,y)) b` STRIP_ASSUME_TAC THENL
   [RES_TAC THEN ASM_MESON_TAC[],
    Q.SUBGOAL_THEN
      `?w2:'b. (\z. B (min:'a,z)) w2` STRIP_ASSUME_TAC THENL
    [BETA_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN ASM_REWRITE_TAC[],
     Q.SUBGOAL_THEN
     `?min':'b. (\z. B (min,z)) min'
       /\  !b. Q b min' ==>
              ~((\z. B (min,z)) b)` STRIP_ASSUME_TAC THENL
     [RES_TAC THEN ASM_MESON_TAC[],
      RULE_ASSUM_TAC BETA_RULE
       THEN EXISTS_TAC (Term`(min:'a, (min':'b))`)
       THEN ASM_REWRITE_TAC[]
       THEN GEN_TAC THEN SUBST_TAC [GSYM(Q.SPEC`b:'a#'b` PAIR)]
       THEN REWRITE_TAC [UNCURRY_DEF] THEN BETA_TAC
       THEN REWRITE_TAC [UNCURRY_DEF] THEN BETA_TAC
       THEN ASM_MESON_TAC pair_rws]]]]);

(*---------------------------------------------------------------------------
 * The relational product of two wellfounded relations is wellfounded. This
 * is a consequence of WF_LEX.
 *---------------------------------------------------------------------------*)

val RPROD_DEF =
Q.new_definition
("RPROD_DEF",
   `RPROD (R1:'a->'b->bool)
          (R2:'c->'d->bool) = \(s,t) (u,v). R1 s u /\ R2 t v`);


val WF_RPROD =
Q.store_thm("WF_RPROD",
 `!(R:'a->'a->bool) (Q:'b->'b->bool). WF R /\ WF Q  ==>  WF(RPROD R Q)`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC relationTheory.WF_SUBSET
 THEN Q.EXISTS_TAC`R LEX Q`
 THEN CONJ_TAC
 THENL [MATCH_MP_TAC WF_LEX THEN ASM_REWRITE_TAC[],
        REWRITE_TAC[LEX_DEF,RPROD_DEF]
         THEN GEN_TAC THEN SUBST_TAC [GSYM(Q.SPEC`x:'a#'b` PAIR)]
         THEN GEN_TAC THEN SUBST_TAC [GSYM(Q.SPEC`y:'a#'b` PAIR)]
         THEN REWRITE_TAC [UNCURRY_DEF] THEN BETA_TAC
         THEN REWRITE_TAC [UNCURRY_DEF] THEN BETA_TAC
         THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);

(* more relational properties of LEX *)
val total_LEX = store_thm(
  "total_LEX",
  ``total R1 /\ total R2 ==> total (R1 LEX R2)``,
  ASM_SIMP_TAC (srw_ss()) [total_def, FORALL_PROD, LEX_DEF, UNCURRY_DEF] THEN
  METIS_TAC[]);
val _ = export_rewrites ["total_LEX"]

val transitive_LEX = store_thm(
  "transitive_LEX",
  ``transitive R1 /\ transitive R2 ==> transitive (R1 LEX R2)``,
  SIMP_TAC (srw_ss()) [transitive_def, FORALL_PROD, LEX_DEF, UNCURRY_DEF] THEN
  METIS_TAC[]);
val _ = export_rewrites ["transitive_LEX"]

val reflexive_LEX = store_thm(
  "reflexive_LEX",
  ``reflexive (R1 LEX R2) <=> reflexive R1 \/ reflexive R2``,
  SIMP_TAC (srw_ss()) [reflexive_def, LEX_DEF, FORALL_PROD, UNCURRY_DEF] THEN
  METIS_TAC[])
val _ = export_rewrites ["reflexive_LEX"]

val symmetric_LEX = store_thm(
  "symmetric_LEX",
  ``symmetric R1 /\ symmetric R2 ==> symmetric (R1 LEX R2)``,
  SIMP_TAC (srw_ss()) [symmetric_def, LEX_DEF, FORALL_PROD, UNCURRY_DEF] THEN
  METIS_TAC[]);
val _ = export_rewrites ["symmetric_LEX"]

val LEX_CONG = Q.store_thm
("LEX_CONG",
 `!R1 R2 v1 v2 R1' R2' v1' v2'.
     (v1 = v1') /\ (v2 = v2') /\
     (!a b c d. (v1' = (a,b)) /\ (v2' = (c,d)) ==> (R1 a c = R1' a c)) /\
     (!a b c d. (v1' = (a,b)) /\ (v2' = (c,d)) /\ (a=c) ==> (R2 b d = R2' b d))
   ==>
    ($LEX R1 R2 v1 v2 = $LEX R1' R2' v1' v2')`,
 Ho_Rewrite.REWRITE_TAC [LEX_DEF,FORALL_PROD,PAIR_EQ]
   THEN NTAC 2 (REWRITE_TAC [UNCURRY_VAR,FST,SND] THEN BETA_TAC)
   THEN METIS_TAC[]);

(* ----------------------------------------------------------------------
    PAIR_REL : ('a -> 'c -> bool) -> ('b -> 'd -> bool) ->
               ('a # 'b -> 'c # 'd -> bool)
   ---------------------------------------------------------------------- *)

Overload PAIR_REL = “RPROD”
val _ = set_mapped_fixity{fixity = Infixr 490, term_name = "PAIR_REL",
                          tok = "###"}

Theorem PAIR_REL = RPROD_DEF
Theorem PAIR_REL_THM[simp,compute]:
  (R1 ### R2) (a,b) (c,d) <=> R1 a c /\ R2 b d
Proof
  SIMP_TAC (srw_ss()) [PAIR_REL]
QED

Theorem PAIR_REL_EQ[simp,quotient_simp]:
  ($= ### $=) = $=
Proof
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, FORALL_PROD]
QED

Theorem PAIR_REL_REFL:
  (!x:'a. R1 x x) /\ (!y:'b. R2 y y) ==>
  !xy. (R1 ### R2) xy xy
Proof
  SIMP_TAC (srw_ss()) [FORALL_PROD]
QED

Theorem PAIR_REL_SYM:
  (!x y:'a. R1 x y <=> R1 y x) /\ (!a b:'b. R2 a b <=> R2 b a) ==>
  !xy ab. (R1 ### R2) xy ab <=> (R1 ### R2) ab xy
Proof
  SIMP_TAC (srw_ss()) [FORALL_PROD]
QED

Theorem PAIR_REL_TRANS:
  (!x y z:'a. R1 x y /\ R1 y z ==> R1 x z) /\
  (!a b c:'b. R2 a b /\ R2 b c ==> R2 a c) ==>
  !xy ab uv. (R1 ### R2) xy ab /\ (R1 ### R2) ab uv ==>
             (R1 ### R2) xy uv
Proof
  SIMP_TAC (srw_ss()) [FORALL_PROD] >> METIS_TAC[]
QED

Theorem PAIR_EQUIV[quotient_equiv]:
  !(R1:'a -> 'a -> bool) (R2 : 'b -> 'b -> bool).
    EQUIV R1 ==> EQUIV R2 ==> EQUIV (R1 ### R2)
Proof
  rpt gen_tac >> simp[EQUIV_def, EQUIV_REFL_SYM_TRANS, PAIR_REL_REFL] >>
  rpt strip_tac
  >- (irule $ iffLR PAIR_REL_SYM >> simp[EQ_IMP_THM]) >>
  irule PAIR_REL_TRANS >> METIS_TAC[]
QED

(* ----------------------------------------------------------------------
    PAIR_SET : ('a -> 'c set) -> ('b -> 'c set) -> 'a # 'b -> 'c set
   ---------------------------------------------------------------------- *)

val PAIR_SET_def = new_definition(
  "PAIR_SET_def",
  “PAIR_SET f g = \(a:'a, b:'b) c:'c. c IN f a \/ c IN g b”);

Theorem IN_PAIR_SET:
  c IN PAIR_SET f g (a,b) <=> c IN f a \/ c IN g b
Proof
  SIMP_TAC (srw_ss()) [PAIR_SET_def, IN_DEF]
QED

Overload setFST = “PAIR_SET $= (K (\x. F))”
Overload setSND = “PAIR_SET (K (\x. F)) $=”

Theorem IN_setFSTSND[simp]:
  (a IN setFST ab <=> FST ab = a) /\
  (b IN setSND ab <=> SND ab = b)
Proof
  Q.ID_SPEC_TAC ‘ab’ >> SIMP_TAC (srw_ss()) [FORALL_PROD, IN_PAIR_SET] >>
  SIMP_TAC (srw_ss()) [IN_DEF]
QED

Theorem PAIR_MAP_CONG:
  (!a:'a. a IN setFST ab ==> f1 a = f2 a :'c) /\
  (!b:'b. b IN setSND ab ==> g1 b = g2 b :'d) ==>
  (f1 ## g1) ab = (f2 ## g2) ab
Proof
  Q.ID_SPEC_TAC ‘ab’ >> SIMP_TAC (srw_ss()) [FORALL_PROD]
QED

Theorem PAIR_MAP_SET:
  (c IN setFST ((f ## g) ab) <=> ?a:'a. c:'c = f a /\ a IN setFST ab) /\
  (d IN setSND ((f ## g) ab) <=> ?b:'b. d:'d = g b /\ b IN setSND ab)
Proof
  Q.ID_SPEC_TAC ‘ab’ >> SIMP_TAC (srw_ss()) [FORALL_PROD] >>
  METIS_TAC[]
QED

(* ----------------------------------------------------------------------
    Theorems to support the quotient package
   ---------------------------------------------------------------------- *)

Theorem PAIR_QUOTIENT[quotient]:
  !R1 (abs1:'a -> 'c) rep1.
    QUOTIENT R1 abs1 rep1 ==>
    !R2 (abs2:'b -> 'd) rep2.
      QUOTIENT R2 abs2 rep2 ==>
      QUOTIENT (R1 ### R2) (abs1 ## abs2) (rep1 ## rep2)
Proof
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT CONJ_TAC
    THENL
      [ rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >>
        simp[FORALL_PROD],

        rpt (dxrule_then assume_tac QUOTIENT_REP_REFL) >>
        simp[FORALL_PROD],

        simp[FORALL_PROD] >>
        rpt (dxrule_then (fn th => simp[Once th, SimpLHS]) QUOTIENT_REL) >>
        simp[AC CONJ_ASSOC CONJ_COMM]
      ]
QED



(* Here are some definitional and well-formedness theorems
   for some standard polymorphic operators.  Could almost certainly be
   generated and proved automatically.
*)

(* FST, SND, COMMA, CURRY, UNCURRY, ## *)

Theorem FST_PRS[quotient_prs]:
  !R1 (abs1:'a -> 'c) rep1.
    QUOTIENT R1 abs1 rep1 ==>
    !R2 (abs2:'b -> 'd) rep2.
      QUOTIENT R2 abs2 rep2 ==>
      !p. FST p = abs1 (FST ((rep1 ## rep2) p))
Proof
  REPEAT (rpt GEN_TAC THEN DISCH_TAC) >>
  rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >>
  simp[FORALL_PROD]
QED

Theorem FST_RSP[quotient_rsp]:
  !R1 (abs1:'a -> 'c) rep1.
    QUOTIENT R1 abs1 rep1 ==>
    !R2 (abs2:'b -> 'd) rep2.
      QUOTIENT R2 abs2 rep2 ==>
      !p1 p2. (R1 ### R2) p1 p2 ==> R1 (FST p1) (FST p2)
Proof
  simp[FORALL_PROD]
QED

Theorem SND_PRS[quotient_prs]:
  !R1 (abs1:'a -> 'c) rep1.
    QUOTIENT R1 abs1 rep1 ==>
    !R2 (abs2:'b -> 'd) rep2.
      QUOTIENT R2 abs2 rep2 ==>
      !p. SND p = abs2 (SND ((rep1 ## rep2) p))
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC >>
  rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >>
  simp[FORALL_PROD]
QED

Theorem SND_RSP[quotient_rsp]:
  !R1 (abs1:'a -> 'c) rep1.
    QUOTIENT R1 abs1 rep1 ==>
    !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
                              !p1 p2.
                                (R1 ### R2) p1 p2 ==> R2 (SND p1) (SND p2)
Proof
  simp[FORALL_PROD]
QED

Theorem COMMA_PRS[quotient_prs]:
  !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a b. (a,b) = (abs1 ## abs2) (rep1 a, rep2 b)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC >>
  rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >>
  simp[]
QED

Theorem COMMA_RSP[quotient_rsp]:
  !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a1 a2 b1 b2.
          R1 a1 b1 /\ R2 a2 b2 ==>
          (R1 ### R2) (a1,a2) (b1,b2)
Proof
  simp[]
QED

Theorem CURRY_PRS[quotient_prs]:
  !R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f a b. CURRY f a b =
                 abs3 (CURRY (((abs1 ## abs2) --> rep3) f)
                             (rep1 a) (rep2 b))
Proof
  ntac 3 (REPEAT GEN_TAC THEN DISCH_TAC) >>
  rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >>
  simp[FUN_MAP_THM]
QED

Theorem CURRY_RSP[quotient_rsp]:
   !R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f1 f2.
          ((R1 ### R2) ===> R3) f1 f2 ==>
          (R1 ===> R2 ===> R3) (CURRY f1) (CURRY f2)
Proof
  simp[FUN_REL]
QED

Theorem UNCURRY_PRS[quotient_prs]:
  !R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f p. UNCURRY f p =
               abs3 (UNCURRY ((abs1 --> abs2 --> rep3) f)
                             ((rep1 ## rep2) p))
Proof
  REPEAT (REPEAT GEN_TAC THEN DISCH_TAC) >>
  rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >>
  simp[FUN_MAP_THM, FORALL_PROD]
QED

Theorem UNCURRY_RSP[quotient_rsp]:
   !R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f1 f2.
          (R1 ===> R2 ===> R3) f1 f2 ==>
          ((R1 ### R2) ===> R3) (UNCURRY f1) (UNCURRY f2)
Proof
  simp[FUN_REL, FORALL_PROD]
QED

Theorem PAIR_MAP_PRS[quotient_prs]:
    !R1 (abs1:'a -> 'e) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'f) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'g) rep3. QUOTIENT R3 abs3 rep3 ==>
        !R4 (abs4:'d -> 'h) rep4. QUOTIENT R4 abs4 rep4 ==>
         !f g. (f ## g) =
               ((rep1 ## rep3) --> (abs2 ## abs4))
                   (((abs1 --> rep2) f) ## ((abs3 --> rep4) g))
Proof
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC) >>
    rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >>
    simp[FUN_EQ_THM, FORALL_PROD, FUN_MAP_THM]
QED

Theorem PAIR_MAP_RSP[quotient_rsp]:
   !R1 (abs1:'a -> 'e) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'f) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'g) rep3. QUOTIENT R3 abs3 rep3 ==>
        !R4 (abs4:'d -> 'h) rep4. QUOTIENT R4 abs4 rep4 ==>
         !f1 f2 g1 g2.
          (R1 ===> R2) f1 f2 /\ (R3 ===> R4) g1 g2 ==>
          ((R1 ### R3) ===> (R2 ### R4)) (f1 ## g1) (f2 ## g2)
Proof
  simp[FUN_REL, FORALL_PROD]
QED


(*---------------------------------------------------------------------------
    Generate some ML that gets evaluated at theory load time.
    It adds relevant rewrites into the global compset.
 ---------------------------------------------------------------------------*)

fun stA s =
  let
    val nm = s ^ "_lazyfied"
    val th = save_thm(nm, computeLib.lazyfy_thm $ DB.fetch "-" s)
  in
    ThmAttribute.store_at_attribute {
      name = nm, attrname = "compute", args = [], thm = th
    }
  end

(* not super apparent to me why these need to be lazyfied, with possible
   exception of pair_case_thm, which gives us some evaluation order control
*)
val _ = app stA ["pair_case_thm", "SWAP_def", "CURRY_DEF"]

(*---------------------------------------------------------------------------
    Some messiness in order to teach the definition principle about
    varstructs.
 ---------------------------------------------------------------------------*)

val _ = adjoin_to_theory
{sig_ps = SOME(fn _ => B[
      S "type hol_type = Abbrev.hol_type", NL,
      S "type term     = Abbrev.term", NL,
      S "type conv     = Abbrev.conv", NL,NL,
      S "val uncurry_tm       : term", NL,
      S "val comma_tm         : term", NL,
      S "val dest_pair        : term -> term * term", NL,
      S "val strip_pair       : term -> term list", NL,
      S "val spine_pair       : term -> term list", NL,
      S "val is_vstruct       : term -> bool", NL,
      S "val mk_pabs          : term * term -> term", NL,
      S "val PAIRED_BETA_CONV : conv", NL]),
 struct_ps = SOME(fn _ => B[
S"(*---------------------------------------------------------------", NL,
S"       Support for definitions using varstructs", NL,
S"----------------------------------------------------------------*)", NL,
NL,
S "open HolKernel boolLib;", NL,
S "infix |-> ORELSEC THENC;", NL,
NL,
S "val ERR1 = mk_HOL_ERR \"pairSyntax\"", NL,
S "val ERR2 = mk_HOL_ERR \"PairedLambda\"", NL,
S "val ERR3 = mk_HOL_ERR \"pairTheory.dest\"", NL,
NL,
S "val comma_tm = prim_mk_const {Name=\",\", Thy=\"pair\"};", NL,
S "val uncurry_tm = prim_mk_const {Name=\"UNCURRY\", Thy=\"pair\"};", NL,
NL,
S "val dest_pair = dest_binop comma_tm (ERR1 \"dest_pair\" \"not a pair\")", NL,
S "val strip_pair = strip_binop dest_pair;", NL,
S "val spine_pair = spine_binop (total dest_pair);", NL,
NL,
S "local fun check [] = true", NL,
S "        | check (h::t) = is_var h andalso not(tmem h t) andalso check t", NL,
S "in", NL,
S "fun is_vstruct M = check (strip_pair M)",
S "end;", NL,
NL,
S "fun mk_uncurry_tm(xt,yt,zt) = ", NL,
S "  inst [alpha |-> xt, beta |-> yt, gamma |-> zt] uncurry_tm;", NL,
NL,
NL,
S "fun mk_pabs(vstruct,body) =", NL,
S "  if is_var vstruct then Term.mk_abs(vstruct, body)", NL,
S "  else let val (fst,snd) = dest_pair vstruct", NL,
S "       in mk_comb(mk_uncurry_tm(type_of fst, type_of snd, type_of body),", NL,
S "                  mk_pabs(fst,mk_pabs(snd,body)))", NL,
S "       end handle HOL_ERR _ => raise ERR1 \"mk_pabs\" \"\";", NL,
NL,
NL,
S "local val vs = map genvar [alpha --> beta --> gamma, alpha, beta]", NL,
S "      val DEF = SPECL vs UNCURRY_DEF", NL,
S "      val RBCONV = RATOR_CONV BETA_CONV THENC BETA_CONV", NL,
S "      fun conv tm = ", NL,
S "       let val (Rator,Rand) = dest_comb tm", NL,
S "           val (fst,snd) = dest_pair Rand", NL,
S "           val (Rator,f) = dest_comb Rator", NL,
S "           val _ = assert (same_const uncurry_tm) Rator", NL,
S "           val (t1,ty') = dom_rng (type_of f)", NL,
S "           val (t2,t3) = dom_rng ty'", NL,
S "           val iDEF = INST_TYPE [alpha |-> t1, beta |-> t2, gamma |-> t3] DEF", NL,
S "           val (fv,xyv) = strip_comb(rand(concl iDEF))", NL,
S "           val xv = hd xyv and yv = hd (tl xyv)", NL,
S "           val def = INST [yv |-> snd, xv |-> fst, fv |-> f] iDEF", NL,
S "       in", NL,
S "         TRANS def ", NL,
S "          (if Term.is_abs f ", NL,
S "           then if Term.is_abs (body f) ", NL,
S "                then RBCONV (rhs(concl def))", NL,
S "                else CONV_RULE (RAND_CONV conv)", NL,
S "                      (AP_THM(BETA_CONV(mk_comb(f, fst))) snd)", NL,
S "           else let val recc = conv (rator(rand(concl def)))", NL,
S "                in if Term.is_abs (rhs(concl recc))", NL,
S "                   then RIGHT_BETA (AP_THM recc snd)", NL,
S "                   else TRANS (AP_THM recc snd) ", NL,
S "                           (conv(mk_comb(rhs(concl recc), snd)))", NL,
S "                end)", NL,
S "       end", NL,
S "in", NL,
S "fun PAIRED_BETA_CONV tm ", NL,
S "    = conv tm handle HOL_ERR _ => raise ERR2 \"PAIRED_BETA_CONV\" \"\"", NL,
S "end;", NL,
NL,
NL,
S "(*---------------------------------------------------------------------------", NL,
S "     Lifting primitive definition principle to understand varstruct", NL,
S "     arguments in definitions.", NL,
S " ---------------------------------------------------------------------------*)", NL,
NL,
S "fun inter s1 [] = []", NL,
S "  | inter s1 (h::t) = case op_intersect aconv s1 h of [] => inter s1 t | X => X", NL,
NL,
S "fun joint_vars []  = []", NL,
S "  | joint_vars [_] = []", NL,
S "  | joint_vars (h::t) = case inter h t of [] => joint_vars t | X => X;", NL,
NL,
S "fun dest t = ", NL,
S "  let val (lhs,rhs) = dest_eq (snd(strip_forall t))", NL,
S "      val (f,args) = strip_comb lhs", NL,
S "      val f = mk_var(dest_const f) handle HOL_ERR _ => f", NL,
S "  in ", NL,
S "  case filter (not o is_vstruct) args ", NL,
S "   of [] => (case joint_vars (map free_vars args)", NL,
S "              of [] => (args, mk_eq(f,itlist (curry mk_pabs) args rhs))", NL,
S "               | V  => raise ERR3 \"new_definition\" (String.concat", NL,
S "                       (\"shared variables between arguments: \" ::", NL,
S "                        commafy (map Parse.term_to_string V))))", NL,
S "    | tml => raise ERR3 \"new_definition\" (String.concat", NL,
S "             (\"The following arguments are not varstructs: \"::", NL,
S "              commafy (map Parse.term_to_string tml)))", NL,
S "  end;", NL,
NL,
S "fun RHS_CONV conv th = TRANS th (conv(rhs(concl th)));", NL,
NL,
S "fun add_varstruct v th = ", NL,
S "  RHS_CONV(BETA_CONV ORELSEC PAIRED_BETA_CONV) (AP_THM th v)", NL,
NL,
S "fun post (V,th) =", NL,
S "  let val vars = List.concat (map free_vars_lr V)", NL,
S "  in", NL,
S "    itlist GEN vars (rev_itlist add_varstruct V th)", NL,
S "  end;", NL,
S "  ", NL,
S "val _ = Definition.new_definition_hook := (dest, post)", NL])};

val FST_EQ_EQUIV = Q.store_thm("FST_EQ_EQUIV",
  `(FST p = x) <=> ?y. p = (x,y)`,
  Q.ISPEC_THEN `p` STRUCT_CASES_TAC pair_CASES >> simp_tac(srw_ss())[]);
val SND_EQ_EQUIV = Q.store_thm("SND_EQ_EQUIV",
  ‘(SND p = y) <=> ?x. p = (x,y)’,
  Q.ISPEC_THEN `p` STRUCT_CASES_TAC pair_CASES >> simp_tac(srw_ss())[]);



val comma_tm = Term.prim_mk_const{Name=",", Thy="pair"};
fun is_pair tm = Term.same_const comma_tm (fst(strip_comb tm));
fun dest_pair tm =
  case snd (strip_comb tm) of [a,b] => (a,b) | _ => raise Match;

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME(fn _ =>
                    S "val _ = BasicProvers.new_let_thms\
                          \[o_UNCURRY_R, C_UNCURRY_L, S_UNCURRY_R, \
                          \FORALL_UNCURRY]")}

val _ = export_theory();

val _ = export_theory_as_docfiles "pair-help/thms"
