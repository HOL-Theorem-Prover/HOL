(*---------------------------------------------------------------------------
                Five Axioms of Alpha Conversion
                   (Andy Gordon & Tom Melham)


                  Part II: name-carrying terms

 ---------------------------------------------------------------------------*)

(* Interactive use:
   app load ["bossLib", "Q", "pred_setTheory", "stringTheory", "dBTheory"];
*)

open HolKernel Parse boolLib
     bossLib arithmeticTheory pred_setTheory dBTheory
     BasicProvers basic_swapTheory

val _ = new_theory "nc";


(*---------------------------------------------------------------------------
            Support bumpf.
 ---------------------------------------------------------------------------*)

val FUN_EQ_TAC = CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)
                   THEN GEN_TAC THEN BETA_TAC;


(*---------------------------------------------------------------------------
            Definition of the type of name carrying terms.
 ---------------------------------------------------------------------------*)

val BI_nc =
  define_new_type_bijections
      {name = "BI_nc",
       ABS  = "ABS_nc",
       REP  = "REP_nc",
       tyax = new_type_definition ("nc",
                 Q.prove(`?x:'a dB. dOK x`, PROVE_TAC [dOK_DEF]))};

val REP_nc_11 = prove_rep_fn_one_one BI_nc;
val ABS_nc_11 = prove_abs_fn_one_one BI_nc;

val (ABS_REP, OK_REP_ABS) =
  let val (b1,b2) = CONJ_PAIR BI_nc
  in (b1, GEN_ALL (fst (EQ_IMP_RULE (SPEC_ALL b2))))
  end;

val OK_REP = Q.prove(`!u. dOK (REP_nc u)`, PROVE_TAC [BI_nc]);

val OK_ss = std_ss && [OK_REP, OK_REP_ABS, dOK_DEF, ABS_REP, dOK_dSUB];

(* --------------------------------------------------------------------- *)
(* Definition of the constructors.                                       *)
(* --------------------------------------------------------------------- *)

Definition CON: CON c   = ABS_nc (dCON c)
End
Definition VARR: VAR x   = ABS_nc (dVAR x)
End
Definition LAM: LAM x m = ABS_nc (dLAMBDA x (REP_nc m))
End
Definition APP: $@@ m n = ABS_nc (dAPP (REP_nc m) (REP_nc n))
End

val _ = set_fixity "@@" (Infixl 901);


(* --------------------------------------------------------------------- *)
(* Definition of the free variable function. At the abstract level, this *)
(* will satisfy the following defining property:                         *)
(*                                                                       *)
(*    |- (!k. FV(CON k) = {}) /\                                         *)
(*       (!x. FV(VAR x) = {x}) /\                                        *)
(*       (!t u. FV(t @@ u) = (FV t) UNION (FV u)) /\                     *)
(*       (!x n. FV(LAM x n) = (FV n) DELETE x)                           *)
(*                                                                       *)
(* which also forms a part of the abstract characterization of the type  *)
(* of name-carrying terms.                                               *)
(* --------------------------------------------------------------------- *)

val FV =
 Define
    `FV u = dFV (REP_nc u)`;

val FV_THM = Q.store_thm("FV_THM",
 `(!k.   FV (CON k:'a nc)   = {})  /\
  (!x.   FV (VAR x:'a nc)   = {x}) /\
  (!t u. FV (t @@ u:'a nc)  = (FV t) UNION (FV u)) /\
  (!x n. FV (LAM x n:'a nc) = (FV n) DELETE x)`,
RW_TAC OK_ss
  [FV, CON, VARR, APP, LAM, dFV_def, dFV_dLAMBDA]);
val _ = export_rewrites ["FV_THM"]


(* --------------------------------------------------------------------- *)
(* Definition of substitution. At the abstract level, this will satisfy  *)
(* the following defining property:                                      *)
(*                                                                       *)
(*    |- (!s k. (CON k) SUB s = CON k) /\                                *)
(*       (!u x. (VAR x) SUB (u,x) = u) /\                                *)
(*       (!u x y. ~(x = y) ==> ((VAR y) SUB (u,x) = VAR y)) /\           *)
(*       (!s t u. (t @@ u) SUB s = (t SUB s) @@ (u SUB s)) /\            *)
(*       (!x t u. (LAM x t) SUB (u,x) = LAM x t) /\                      *)
(*       (!x y u.                                                        *)
(*         ~(x = y) /\ ~y IN (FV u) ==>                                  *)
(*          !t. ((LAM y t) SUB (u,x) = LAM y(t SUB (u,x))))              *)
(*                                                                       *)
(* which also forms a part of the abstract characterization of the type  *)
(* of name-carrying terms.                                               *)
(* --------------------------------------------------------------------- *)

val SUB_DEF =
 Define
    `SUB new old u = ABS_nc ([old |-> REP_nc new] (REP_nc u))`;

val _ = add_rule {term_name = "SUB", fixity = Closefix,
                  pp_elements = [TOK "[", TM, TOK "/", TM, TOK "]"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};


val lem = Q.prove(
`!r r'. dOK r /\ dOK r' /\ (r=r') ==> (ABS_nc r = ABS_nc r')`,
PROVE_TAC [ABS_nc_11]);

val u = Term`u:'a nc`;

val SUB_THM =
 Q.store_thm ("SUB_THM",
  `(!^u x k.             [u/x](CON k)   = CON k)   /\
   (!^u x.               [u/x](VAR x)   = u)       /\
   (!^u x y. ~(x=y) ==> ([u/x](VAR y)   = VAR y))  /\
   (!^u s t x.           [u/x](s @@ t)  = [u/x]s @@ [u/x]t) /\
   (!^u t x.             [u/x](LAM x t) = LAM x t)          /\
   (!^u x y. ~(x=y) /\ ~(y IN FV u)
                 ==> !t. [u/x](LAM y t) = LAM y ([u/x]t))`,
RW_TAC OK_ss
  [LAM, APP, VARR, CON, FV, SUB_DEF,lem, NEQ_dVAR_dSUB,
   EQ_dVAR_dSUB,dCON_dSUB, dAPP_dSUB,dLAMBDA_dSUB_EQ,dLAMBDA_dSUB]);

(* ADG: following should be the axiomatisation *)

val SUB_VAR = Q.store_thm("SUB_VAR",
`!x y t. [t/y](VAR x) = if x=y then t else VAR x`,
RW_TAC std_ss [SUB_THM]);



(* --------------------------------------------------------------------- *)
(* Alpha conversion. This is also part of the characterization of name-  *)
(* carrying terms. Open question: prove the independence of ALPHA.       *)
(* --------------------------------------------------------------------- *)

val ALPHA =
 Q.store_thm ("ALPHA",
  `!x y ^u.
       ~(y IN (FV (LAM x u))) ==> (LAM x u = LAM y ([VAR y/x]u))`,
RW_TAC std_ss [FV_THM,DE_MORGAN_THM,IN_DELETE,FV, LAM, SUB_DEF, VARR]
 THEN MATCH_MP_TAC lem
 THEN RW_TAC OK_ss []
 THEN Cases_on `y:string = x`
 THEN ZAP_TAC (OK_ss && [dSUB_ID]) [dALPHA,OK_REP]);


val ALPHA_LEMMA = Q.prove(
    `!x u. LAM x ([VAR x/x]u) = LAM x u`,
PROVE_TAC [ALPHA,FV_THM,IN_DELETE]);


(* --------------------------------------------------------------------- *)
(* Weaker version of Alpha Conversion.                                   *)
(* --------------------------------------------------------------------- *)

val SIMPLE_ALPHA =
 Q.store_thm ("SIMPLE_ALPHA",
   `!y u.
      ~(y IN FV u) ==> !x. LAM x u = LAM y ([VAR y/x]u)`,
PROVE_TAC [ALPHA,FV_THM,IN_DELETE]);


(* --------------------------------------------------------------------- *)
(* Now unique iterator.                                                  *)
(* --------------------------------------------------------------------- *)

val EXISTENCE = Q.prove(
  `!con : 'a->'b.
   !var : string->'b.
   !app : 'b->'b->'b.
   !lam : (string->'b) -> 'b.
    ?hom:'a nc -> 'b.
      (!k.   hom(CON k)   = con k) /\
      (!x.   hom(VAR x)   = var x) /\
      (!n m. hom(n @@ m)  = app (hom n) (hom m)) /\
      (!x n. hom(LAM x n) = lam(\y. hom([VAR y/x]n)))`,
RW_TAC std_ss []
  THEN Q.EXISTS_TAC `\x. HOM (con:'a ->'b) var lam app (REP_nc x)`
  THEN RW_TAC OK_ss [CON,VARR,APP,LAM, HOM_THM,SUB_DEF]);


val nc_ITERATOR =
 Q.store_thm ("nc_ITERATOR",
   `!con : 'a->'b.
    !var : string->'b.
    !app : 'b->'b->'b.
    !lam : (string->'b)->'b.
       ?!hom :'a nc -> 'b.
          (!k. hom(CON k)     = con k) /\
          (!x. hom(VAR x)     = var x) /\
          (!t u. hom(t @@ u)  = app (hom t) (hom u)) /\
          (!x u. hom(LAM x u) = lam(\y. hom([VAR y/x]u)))`,
CONV_TAC (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV)
 THEN RW_TAC std_ss [EXISTENCE,CON,VARR,APP,LAM,SUB_DEF] THEN FUN_EQ_TAC
 THEN PURE_ONCE_REWRITE_TAC [GSYM ABS_REP] THEN
   let val th1 = Q.ISPEC `REP_nc (n:'a nc)` (UNDISCH (SPEC_ALL UNIQUE_HOM_THM))
       val th2 = REWRITE_RULE [OK_REP] th1
       val th3 = itlist Q.GEN [`f`, `g`] (DISCH_ALL th2)
       val th4 = Q.ISPECL [`(f:'a nc->'b) o ABS_nc`,
                           `(g:'a nc->'b) o ABS_nc`] th3
   in MATCH_MP_TAC (REWRITE_RULE [combinTheory.o_THM] th4) end
 THEN RW_TAC std_ss [] THEN IMP_RES_THEN (SUBST1_TAC o GSYM) OK_REP_ABS
 THEN RW_TAC OK_ss []);

(* --------------------------------------------------------------------- *)
(* Abstraction function.                                                 *)
(* --------------------------------------------------------------------- *)

val lemma =
 Q.prove(`REP_nc o (\s. [VAR s/x]^u) = \s. REP_nc([VAR s/x]u)`,
RW_TAC std_ss
    [combinTheory.o_DEF]);


val ABS_EXISTS = Q.prove(
  `?abs:(string->'a nc)->'a nc.
     !^u x. abs (\s. [VAR s/x]u) = LAM x u`,
STRIP_ASSUME_TAC WRAP_DB_EXISTS
  THEN Q.EXISTS_TAC `\f. ABS_nc(wrap (REP_nc o f))`
  THEN RW_TAC OK_ss [lemma,LAM,SUB_DEF,VARR]);


val ABS_DEF = new_specification ("ABS_DEF", ["ABS"], ABS_EXISTS);

(* ********************************************************************* *)
(* End of characterization.                                              *)
(* ********************************************************************* *)

(* --------------------------------------------------------------------- *)
(* Alternative characterization, with ABS as primitive.                  *)
(* --------------------------------------------------------------------- *)

val (ALT_FV,ALT_SUB_THM,ALT_ALPHA,ALT_ITERATOR)
  = let val f = REWRITE_RULE [GSYM ABS_DEF]
    in
       (f FV_THM, f SUB_THM, f ALPHA, f nc_ITERATOR)
    end;
val _ = save_thm("ALT_FV", ALT_FV);
val _ = save_thm("ALT_SUB_THM", ALT_SUB_THM);
val _ = save_thm("ALT_ALPHA", ALT_ALPHA);
val _ = save_thm("ALT_ITERATOR", ALT_ITERATOR);


(* ===================================================================== *)
(* Distinctness.  This follows easily from iterators.                    *)
(* ===================================================================== *)

val ethm =
  let val sth = Q.SPECL [`\k.   (F,F)`,    (* map CON to zero  *)
                         `\x.   (F,T)`,    (* map VAR to one   *)
                         `\n m. (T,F)`,    (* map APP to two   *)
                         `\f.   (T,T)`]    (* map LAM to three *)
                 (INST_TYPE [beta |-> Type`:bool#bool`] nc_ITERATOR)
  in
    CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV (BETA_RULE sth))
  end;

val nc_DISTINCT =
 Q.store_thm ("nc_DISTINCT",
   `(!(k:'a) x. ~(CON k = VAR x)) /\
    (!k x u. ~(CON k = LAM x ^u)) /\
    (!k t u. ~(CON k = t @@ ^u))  /\
    (!x t u. ~(VAR x = t @@ ^u))  /\
    (!x y u. ~(VAR x = LAM y ^u)) /\
    (!x u t p. ~(LAM x ^u = t @@ p))`,
STRIP_ASSUME_TAC ethm THEN RW_TAC std_ss []
  THEN DISCH_THEN (MP_TAC o Q.AP_TERM `hom:'a nc -> bool#bool`)
  THEN RW_TAC std_ss []);

(* ===================================================================== *)
(* Case analysis.  This follows trivially from iterators.                *)
(* ===================================================================== *)

val ithm =
  let val sth = Q.SPECL [`\k. T`, `\x. T`, `\n m. T`, `\f. T`]
                 (INST_TYPE [beta |-> bool] nc_ITERATOR)
    val uth = CONJUNCT2 (CONV_RULE EXISTS_UNIQUE_CONV (BETA_RULE sth))
    val thm1 = REWRITE_RULE [] (Q.SPEC `\u. T` uth)
    val thm2 = Q.SPEC `\p:'a nc. (?k. p = CON k)
                            \/   (?x. p = VAR x)
                            \/   (?t u. p = t @@ u)
                            \/   (?x u. p = LAM x u)` thm1
    val thm3 = CONV_RULE FUN_EQ_CONV (UNDISCH (BETA_RULE thm2))
  in
    DISCH_ALL (REWRITE_RULE [] (BETA_RULE thm3))
  end;

val nc_CASES =
 Q.store_thm ("nc_CASES",
   `!v:'a nc. (?k. v = CON k)
          \/  (?x. v = VAR x)
          \/  (?t u. v = t @@ u)
          \/  (?x u. v = LAM x u)`,
PROVE_TAC [ithm]);


(* ===================================================================== *)
(* Initiality + Wrap implies recursion!                                  *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* In what follows, we will need to be able to express a function:       *)
(*                                                                       *)
(*    h : A -> B x C                                                     *)
(*                                                                       *)
(* as the combination h = <f,g> of two component functions               *)
(*                                                                       *)
(*   f : A -> B   and   g : A -> C                                       *)
(*                                                                       *)
(* The following lemma lets us do this.                                  *)
(* --------------------------------------------------------------------- *)

val COMPONENT_THM = Q.prove(
`!P. (?!f:'A->('B#'C). P f) = ?!p. P(\a.(FST p a, SND p a))`,
GEN_TAC THEN CONV_TAC (DEPTH_CONV EXISTS_UNIQUE_CONV)
  THEN EQ_TAC THEN RW_TAC std_ss [] THENL
  [Q.EXISTS_TAC `FST o f, SND o f`
    THEN RW_TAC std_ss [combinTheory.o_THM,ETA_THM],
   Cases_on `p` THEN Cases_on `p'`
     THEN RULE_ASSUM_TAC (REWRITE_RULE pairTheory.pair_rws)
     THEN `(\a:'A. (q a, r a):'B#'C) =  \a:'A. (q' a, r' a)` by RES_TAC
     THEN PROVE_TAC [pairTheory.PAIR_EQ,EQ_EXT],
   PROVE_TAC[],
   Q.PAT_X_ASSUM `$! M`
      (MP_TAC o Q.SPECL [`(FST o f, SND o f)`, `(FST o f', SND o f')`])
     THEN RW_TAC std_ss [combinTheory.o_THM, FUN_EQ_THM,ETA_THM]
     THEN PROVE_TAC [pairTheory.PAIR_EQ,pairTheory.PAIR,FUN_EQ_THM]]);


val wee_lemma = Q.prove(
`(FST o \y. (f([VAR y/x]^u), g([VAR y/x]u)):'A1#'A2)
      =
 \y. f ([VAR y/x]u)`,
FUN_EQ_TAC THEN RW_TAC std_ss [combinTheory.o_THM]);

val COPY_BUILD_lemma =
 let val instth = INST_TYPE [beta |-> Type`:'a nc # 'b`] nc_ITERATOR
     val con = Term`\k:'a. (CON k, (con k:'b) )`
     and var = Term`\s:string. (VAR s:'a nc, (var s:'b) )`
     and app = Term`\p:'a nc # 'b.
               \q:'a nc # 'b.
               ((FST p) @@ (FST q):'a nc, (app p q:'b) )`
    and lam = Term`\f:string->('a nc # 'b).
                let u:'a nc = ABS (FST o f) in (u, (lam f:'b))`
    val th1 = SPECL [con,var,app,lam] instth
    val th2 = BETA_RULE (ISPEC (rand(concl th1)) COMPONENT_THM)
    val th3 = EQ_MP th2 (BETA_RULE th1)
    val th4 = CONV_RULE (DEPTH_CONV pairLib.let_CONV) th3
    val th5 = REWRITE_RULE [pairTheory.PAIR_EQ,wee_lemma] (BETA_RULE th4)
  in
    CONV_RULE (DEPTH_CONV FORALL_AND_CONV) th5
  end;

val COPY_BUILD = Q.prove(
`?!p:('a nc -> 'a nc) # ('a nc -> 'b).
   ((!k. FST p(CON k) = CON k) /\
    (!x. FST p(VAR x) = VAR x) /\
    (!t u. FST p(t @@ u) = (FST p t)@@(FST p u)) /\
    (!x u. FST p(LAM x u) = ABS(\y. FST p([VAR y/x]u))))
   /\
   ((!k. SND p(CON k) = con k) /\
    (!x. SND p(VAR x) = var x) /\
    (!t u. SND p(t @@ u) = app(FST p t, SND p t) (FST p u, SND p u)) /\
    (!x u. SND p(LAM x u) =
              lam(\y. (FST p([VAR y/x]u),SND p([VAR y/x]u)))))`,
RW_TAC std_ss [DECIDE (Term
                  `(a /\ b /\ c /\ d) /\ (e /\ f /\ g /\ h)
                        ⇔
                   (a /\ e) /\ (b /\ f) /\ (c /\ g) /\ (d /\ h)`),
               REWRITE_RULE pairTheory.pair_rws COPY_BUILD_lemma]);

val lemma =
  let
    val instth = INST_TYPE [beta |-> Type`:'a nc`] nc_ITERATOR
    val con = Term`\k. CON k:'a nc` and
        var = Term`\x:string. VAR x:'a nc` and
        app = Term`\t:'a nc. \u:'a nc. t @@ u` and
        lam = Term`\f:string->'a nc. ABS f`
    val th1 = BETA_RULE (SPECL [con,var,app,lam] instth)
    val th2 = CONJUNCT2 (CONV_RULE EXISTS_UNIQUE_CONV th1)
    val th3 = BETA_RULE (Q.SPEC `\x:'a nc.x` th2)
    val th4 = REWRITE_RULE [ABS_DEF] th3
    val th5 = GSYM (UNDISCH (SPEC_ALL th4))
  in
    GEN_ALL (DISCH_ALL th5)
  end;

val COPY_ID = Q.prove(
 `!hom:'a nc->'a nc.
    (!k. hom(CON k) = CON k) /\
    (!x. hom(VAR x) = VAR x) /\
    (!t u. hom(t @@ u) = (hom t) @@ (hom u)) /\
    (!x u. hom(LAM x u) = ABS(\y. hom([VAR y/x]u)))
         ⇔
    (hom = \x.x)`,
GEN_TAC THEN EQ_TAC THEN STRIP_TAC
  THENL [MATCH_MP_TAC lemma, ALL_TAC]
  THEN RW_TAC std_ss [ABS_DEF]);

val messy_lemma = Q.prove(
`!p:('a nc -> 'a nc) # ('a nc -> 'b).
    ((FST p = \x. x) /\
     (!k. SND p (CON k) = con k) /\
     (!x. SND p (VAR x) = var x) /\
     (!t u. SND p (t @@ u) = app(FST p t,SND p t) (FST p u,SND p u)) /\
     (!x u. SND p (LAM x u) = lam(\y. (FST p([VAR y/x]u), SND p([VAR y/x]u)))))
      =
     ((FST p = (\x . x)) /\
      (!k. SND p(CON k) = con k) /\
      (!x. SND p(VAR x) = var x) /\
      (!t u. SND p(t @@ u) = app(t,SND p t)(u,SND p u)) /\
      (!x u. SND p(LAM x u) = lam(\y. ([VAR y/x]u, SND p([VAR y/x]u)))))`,
GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss []);

val pair_lemma = Q.prove(
`!P Q. (?!p:'a #'b. P(FST p) /\ Q(SND p)) ==> ?!s:'b. Q s`,
CONV_TAC (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV)
   THEN RW_TAC std_ss [] THENL
   [PROVE_TAC [],
    Q.PAT_X_ASSUM `$! M`
        (MP_TAC o Q.SPECL [`(FST (p:'a#'b),s)`, `(FST (p:'a#'b),s')`])
      THEN RW_TAC std_ss []]);

val COPY_THEOREM =
 let val th1 = REWRITE_RULE [COPY_ID,messy_lemma] COPY_BUILD
     val (conj1, conj2) = dest_conj(body(rand (concl th1)))
     val p = Term `p : ('a nc -> 'a nc) # ('a nc -> 'b)`
     val v1 = genvar (Type`:'a nc -> 'a nc`)
     and v2 = genvar (Type`:'a nc -> 'b`)
     val P = subst [Term`FST ^p` |-> v1] conj1
     and Q = subst [Term`SND ^p` |-> v2] conj2
     val lp = Term`\^v1. ^P`
     val lq = Term`\^v2. ^Q`
     val th2 = BETA_RULE (ISPECL [lp,lq] pair_lemma)
     val th3_0 = Q.INST [`var` |-> `var`, `con` |-> `con`,
                 `app` |-> `\p q. app' (SND p) (SND q) (FST p) (FST q)`,
                 `lam` |-> `\f. lam' (\y. SND(f y)) (\y. FST(f y))`]
               (MP th2 th1)
     val th3 = Q.INST [`lam'` |-> `lam`, `app'` |-> `app`] th3_0
     val th4 = REWRITE_RULE [] (BETA_RULE th3)
  in
    REWRITE_RULE pairTheory.pair_rws (BETA_RULE th4)
  end;

val nc_RECURSION = Q.store_thm ("nc_RECURSION",
  `!con:'a -> 'b.
   !var:string -> 'b.
   !app:'b -> 'b -> 'a nc -> 'a nc -> 'b.
   !lam:(string -> 'b) -> (string -> 'a nc) -> 'b.
      ?!hom:'a nc -> 'b.
         (!k. hom(CON k)     = con k) /\
         (!x. hom(VAR x)     = var x) /\
         (!t u. hom(t @@ u)  = app (hom t) (hom u) t u) /\
         (!x u. hom(LAM x u) = lam (\y. hom([VAR y/x]u))
                                   (\y. [VAR y/x] u))`,
     REWRITE_TAC [COPY_THEOREM]);

val nc_RECURSION_WEAK = Q.store_thm(
 "nc_RECURSION_WEAK",
  `!con var app lam.
     ?hom : 'a nc -> 'b.
       (!k. hom (CON k) = con k) /\
       (!x. hom (VAR x) = var x) /\
       (!t u. hom (t @@ u) = app t u (hom t) (hom u)) /\
       (!x u. hom (LAM x u) = lam (\y. [VAR y /x] u) (\y. hom([VAR y /x] u)))`,
  REPEAT GEN_TAC THEN
  STRIP_ASSUME_TAC ((CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV o
                     Q.SPECL [`con`, `var`, `\ht hu t u. app t u ht hu`,
                              `\hu u. lam u hu`])
                    nc_RECURSION) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  Q.EXISTS_TAC `hom` THEN ASM_REWRITE_TAC []);

(* ===================================================================== *)
(* Definition of destructors. These are derivable from recursion.        *)
(* ===================================================================== *)

fun nc_recDefine s q =
  Prim_rec.new_recursive_definition
     {rec_axiom = nc_RECURSION_WEAK, name=s, def=Term q};

val VNAME_DEF = nc_recDefine "VNAME_DEF" `VNAME (VAR s) = s`;
val CNAME_DEF = nc_recDefine "CNAME_DEF" `CNAME (CON k) = k`;
val RATOR_DEF = nc_recDefine "RATOR_DEF" `RATOR(M @@ N) = M`;
val RAND_DEF  = nc_recDefine "RAND_DEF"  `RAND (M @@ N) = N`;

val BODY_DEF =
 let val instth = INST_TYPE [beta |-> Type`:string->'a nc`] nc_RECURSION
     val vs = fst(strip_forall (concl instth))
     val th1 = SPECL (rev(tl(rev vs))) instth
     val tm = Term`\(s:string->(string->'a nc)) (t:string->'a nc). t`
     val th2 = CONJUNCT1(CONV_RULE (EXISTS_UNIQUE_CONV) (SPEC tm th1))
     val lemma = Q.prove(
      `?f:'a nc -> (string->'a nc). !x u. f(LAM x ^u) = \y. [VAR y/x]u`,
      STRIP_ASSUME_TAC th2 THEN Q.EXISTS_TAC `hom` THEN RW_TAC std_ss [])
 in
    new_specification ("BODY_DEF", ["BODY"], lemma)
 end;

(* --------------------------------------------------------------------- *)
(* Note the following relations between ABS and Body.                    *)
(* --------------------------------------------------------------------- *)

val ABS_BODY = Q.store_thm("ABS_BODY",
 `!x u. ABS(BODY(LAM x u)) = LAM x u`,
REWRITE_TAC [ABS_DEF,BODY_DEF]);

val BODY_ABS = Q.store_thm("BODY_ABS",
 `!x u. BODY(ABS(\y. [VAR y/x]u)) = \y. [VAR y/x]u`,
REWRITE_TAC [ABS_DEF,BODY_DEF]);


(* ===================================================================== *)
(* Injectivity.  This follows from the existence of destructors.         *)
(* Question: how to strengthen the LAM case to equality?                 *)
(* ===================================================================== *)

val nc_INJECTIVITY = Q.store_thm ("nc_INJECTIVITY",
`(!k:'a . !k'. (CON k = CON k') = (k = k')) /\
 (!x x'. (VAR x:'a nc = VAR x') = (x = x')) /\
 (!t u t' u'. (t @@ ^u = t' @@ u') = ((t = t') /\ (u = u'))) /\
 (!x u x' u'. (LAM x ^u = LAM x' u')
                 ==>
              !y. [VAR y/x]u = [VAR y/x']u')`,
REPEAT (STRIP_TAC ORELSE EQ_TAC)
 THEN ZAP_TAC std_ss
      [CNAME_DEF,VNAME_DEF,RATOR_DEF,RAND_DEF,BODY_DEF]);

(* --------------------------------------------------------------------- *)
(* Note that, from injectivity, we could derive destructors.             *)
(* --------------------------------------------------------------------- *)

val lemma1 = Q.prove(
`?vname. !s. vname(VAR s) = s`,
Q.EXISTS_TAC`\u. @s. VAR s = u` THEN RW_TAC std_ss [nc_INJECTIVITY]);

val lemma2 = Q.prove(
`?cname. !k. cname(CON k) = k`,
Q.EXISTS_TAC`\u. @k. CON k = u` THEN RW_TAC std_ss [nc_INJECTIVITY]);

val lemma3 = Q.prove(
`?rator. !t u. rator(t @@ u) = t`,
Q.EXISTS_TAC`\n. @t. ?u. (t @@ u) = n` THEN RW_TAC std_ss [nc_INJECTIVITY]);

val lemma4 = Q.prove(
`?rand. !t u. rand(t @@ u) = u`,
Q.EXISTS_TAC`\n. @u. ?t. (t @@ u) = n` THEN RW_TAC std_ss [nc_INJECTIVITY]);


(* ===================================================================== *)
(* Induction. This should follow from the uniqueness part of recursion.  *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We can derive INDUCTION:                                              *)
(*                                                                       *)
(* |- !P.                                                                *)
(*    (!k. P(CON k)) /\                                                  *)
(*    (!x. P(VAR x)) /\                                                  *)
(*    (!t u. P t /\ P u ==> P(t @@ u)) /\                                *)
(*    (!x u. (!y. P(u SUB (VAR y,x))) ==> P(LAM x u)) ==>                *)
(*    (!u. P u)                                                          *)
(*                                                                       *)
(* from RECURSION and ABS as follows.                                    *)
(* --------------------------------------------------------------------- *)

val nc_INDUCTION =
 let val instth = INST_TYPE [Type.beta |-> Type.bool] nc_RECURSION
     val con = Term`\x:'a. T` and
         var = Term`\x:string. T` and
         app = Term`\p q. \n m. (p /\ q) \/ P((n @@ m):'a nc)` and
         lam = Term`\f:string->bool. \g:string->'a nc. $! f \/ P(ABS g)`
     val th1 = BETA_RULE (SPECL [con,var,app,lam] instth)
     val th2 = CONJUNCT2 (CONV_RULE EXISTS_UNIQUE_CONV th1)
     val th3 = BETA_RULE (Q.SPECL [`\x.T`, `P`] th2)
     val th4 = AP_THM (UNDISCH (REWRITE_RULE [] th3)) (Term`u:'a nc`)
     val th5 = GEN_ALL (REWRITE_RULE [] (BETA_RULE th4))
 in
    GEN_ALL
      (REWRITE_RULE [ABS_DEF,DECIDE (Term`(A ⇔ B \/ A) ⇔ (B ==> A)`)]
                    (DISCH_ALL th5))
 end;

val _ = save_thm("nc_INDUCTION", nc_INDUCTION);


(* --------------------------------------------------------------------- *)
(* The induction tactic.                                                 *)
(* --------------------------------------------------------------------- *)

fun nc_INDUCT_TAC (A,g) =
 let val (_,P) = dest_comb g
      val ith = ISPEC P nc_INDUCTION
      fun bconv tm =
        if rator tm !~ P then
          raise mk_HOL_ERR "ncScript.sml" "nc_INDUCT_TAC" "function bconv failed"
        else BETA_CONV tm
      val bth = CONV_RULE (ONCE_DEPTH_CONV bconv) ith
  in
    (MATCH_MP_TAC bth
      THEN REPEAT CONJ_TAC THENL
         [ALL_TAC, ALL_TAC,
          GEN_TAC THEN GEN_TAC THEN STRIP_TAC,
          GEN_TAC THEN GEN_TAC THEN STRIP_TAC]) (A,g)
  end;

(* --------------------------------------------------------------------- *)
(* A useful tactic from Andy's original development.                     *)
(*                                                                       *)
(*            A |- P ([u/x](VAR y))                                      *)
(*   =======================================  VAR_SUB_TAC                *)
(*     A |- P(u)    A, ~(x=y) |- P(VAR y)                                *)
(* --------------------------------------------------------------------- *)

local val SUBconst = prim_mk_const{Thy="nc",Name="SUB"}
      val VARconst = prim_mk_const{Thy="nc",Name="VAR"}
in
fun dest_sub tm =
 case strip_comb tm
  of (sub,[new,old,VARapp]) =>
      let val _ = assert (same_const SUBconst) sub
          val (Rator,Rand) = dest_comb VARapp
          val _ = assert (same_const VARconst) Rator
        in (Rand,new,old)
        end
   |   _ => raise mk_HOL_ERR "ncScript.sml" "dest_sub" ""
end

fun VAR_SUB_TAC (A,g) =
 let val (v,new,old) = dest_sub (find_term (can dest_sub) g)
 in
    DISJ_CASES_THEN2
      (fn eq =>  SUBST_ALL_TAC eq THEN
           PURE_ONCE_REWRITE_TAC [el 2 (CONJUNCTS SUB_THM)])
      (fn neq => STRIP_ASSUME_TAC neq THEN
           PURE_ONCE_REWRITE_TAC [MATCH_MP (el 3 (CONJUNCTS SUB_THM)) neq])
    (SPEC (mk_eq(old, v)) EXCLUDED_MIDDLE)
    (A,g)
 end
 handle e => raise wrap_exn "ncScript" "VAR_SUB_TAC" e;

(* ===================================================================== *)
(* Sanity check - try to prove Lemma 1.14 from Hindley and Seldin using  *)
(* our new induction principle.  It's provable, but makes use of the     *)
(* stronger form of alpha conversion.  Question: does it make essential  *)
(* use of this stronger form?                                            *)
(* ===================================================================== *)

val lemma14a = Q.store_thm ("lemma14a",
`!u x. [VAR x/x]u = u`,
nc_INDUCT_TAC THEN RW_TAC std_ss [SUB_THM] THENL
  [VAR_SUB_TAC THEN REFL_TAC,
   Cases_on `x':string = x` THENL
     [RW_TAC std_ss [SUB_THM],
      `~(x IN FV (VAR x'))` by RW_TAC std_ss [FV_THM,IN_SING]
        THEN RW_TAC std_ss [SUB_THM]
        THEN Q.PAT_X_ASSUM `$! M`
              (MP_TAC o Q.AP_TERM `LAM x` o Q.SPECL [`x:string`, `x':string`])
        THEN IMP_RES_TAC (el 6 (CONJUNCTS SUB_THM))
        THEN Q.PAT_X_ASSUM `$! M` (ASSUME_TAC o GSYM)
        THEN RW_TAC std_ss [ALPHA_LEMMA]]]);

(* can now prove a simple version of induction, where you don't want that
   extra strength in the LAM case *)
val simple_induction = store_thm(
  "simple_induction",
  ``!P. (!s. P (VAR s)) /\ (!k. P (CON k)) /\
        (!t u. P t /\ P u ==> P(t @@ u)) /\
        (!v t. P t ==> P (LAM v t)) ==>
        (!t. P t)``,
  GEN_TAC THEN STRIP_TAC THEN HO_MATCH_MP_TAC nc_INDUCTION THEN
  PROVE_TAC [lemma14a]);


(* --------------------------------------------------------------------- *)
(* Andy has observed that lemma14a plus weak alpha gives strong alpha.   *)
(* --------------------------------------------------------------------- *)
val slemma = Q.prove(
`!x y u.
   ~(y IN (FV (LAM x u))) ==> (LAM x u = LAM y([VAR y/x]u))`,
ZAP_TAC (std_ss && [FV_THM,IN_DELETE,IN_SING,DE_MORGAN_THM])
         [lemma14a,SIMPLE_ALPHA]);

(* ===================================================================== *)
(* Sanity check: set of free variables is finite. This was a postulate   *)
(* in Andy's 1993 paper. Here, it depends on induction and the strong    *)
(* alpha axiom (via lemma14a).                                           *)
(* ===================================================================== *)

val FINITE_FV = Q.store_thm ("FINITE_FV",
`!u. FINITE(FV u)`,
nc_INDUCT_TAC
   THEN RW_TAC std_ss
         [FV_THM,FINITE_EMPTY,FINITE_SING,FINITE_UNION,FINITE_DELETE]
   THEN PROVE_TAC [lemma14a]);
val _ = export_rewrites ["FINITE_FV"]

(* ===================================================================== *)
(* Injectivity theorems                                                  *)
(* ===================================================================== *)

val INJECTIVITY_LEMMA1 = Q.store_thm("INJECTIVITY_LEMMA1",
`!x u x1 u1.
   (LAM x u = LAM x1 u1) ==> (u = [VAR x/x1]u1)`,
PROVE_TAC [nc_INJECTIVITY,lemma14a]);

val LAM_VAR_INJECTIVE = store_thm(
  "LAM_VAR_INJECTIVE",
  ``!x b1 b2. (LAM x b1 = LAM x b2) = (b1 = b2)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC std_ss [] THEN STRIP_TAC THEN
  IMP_RES_THEN SUBST_ALL_TAC INJECTIVITY_LEMMA1 THEN
  SIMP_TAC std_ss [lemma14a]);


val lemma =
 REWRITE_RULE [IN_UNION,IN_SING,DE_MORGAN_THM,IN_INSERT]
  (Q.prove(`?gv:string.
              ~(gv IN FV ^u UNION FV (u1:'a nc) UNION {x;x1})`,
      MATCH_MP_TAC new_exists
        THEN REWRITE_TAC [FINITE_UNION,FINITE_FV,FINITE_SING,
                          IN_INSERT,FINITE_INSERT,FINITE_EMPTY]));

val INJECTIVITY_LEMMA2 = Q.store_thm("INJECTIVITY_LEMMA2",
`!x u x' u1.
  (LAM x u = LAM x' u1)
     ==>
  ?z. ~(z IN FV u) /\ ~(z IN FV u1) /\ ([VAR z/x] u = [VAR z/x'] u1)`,
RW_TAC std_ss []
  THEN X_CHOOSE_THEN (Term`gv:string`) STRIP_ASSUME_TAC (GSYM lemma)
  THEN let val ac1 = UNDISCH(Q.SPECL [`gv`, `u`] SIMPLE_ALPHA)
           val ac2 = UNDISCH(Q.SPECL [`gv`,`u1`] SIMPLE_ALPHA)
       in PURE_ONCE_REWRITE_TAC [ac1,ac2]
       end
  THEN RW_TAC std_ss  [nc_INJECTIVITY] THEN PROVE_TAC []);

val INJECTIVITY_LEMMA3 = Q.store_thm("INJECTIVITY_LEMMA3",
`!x u x' u1.
   (?z. ~(z IN FV ^u) /\ ~(z IN FV u1) /\ ([VAR z/x]u = [VAR z/x']u1))
   ==>
   (LAM x u = LAM x' u1)`,
PROVE_TAC [SIMPLE_ALPHA]);

val LAM_INJ_ALPHA_FV = store_thm(
  "LAM_INJ_ALPHA_FV",
  ``!M N x y. (LAM x M = LAM y N) /\ ~(x = y) ==>
              ~(x IN FV N) /\ ~(y IN FV M)``,
  REPEAT STRIP_TAC THENL [
    `x IN FV (LAM y N)` by SRW_TAC [][FV_THM] THEN
    `x IN FV (LAM x M)` by PROVE_TAC [],
    `y IN FV (LAM x M)` by SRW_TAC [][FV_THM] THEN
    `y IN FV (LAM y N)` by PROVE_TAC []
  ] THEN FULL_SIMP_TAC (srw_ss()) [FV_THM]);

(* ===================================================================== *)
(* Andy's second induction theorem -- follows easily.                    *)
(* ===================================================================== *)

val nc_INDUCTION2 = Q.store_thm (
  "nc_INDUCTION2",
  `!P X. (!k. P(CON k)) /\
         (!x. P(VAR x)) /\
         (!t u. P t /\ P u ==> P(t @@ u)) /\
         (!y u. ~(y IN X) /\ P u ==> P(LAM y u)) /\
         FINITE X
     ==>
         !u. P u`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN nc_INDUCT_TAC THEN RW_TAC std_ss []
 THEN MP_TAC (Q.SPEC `FV ^u UNION X` new_exists)
 THEN SRW_TAC [][]
 THEN PROVE_TAC [SIMPLE_ALPHA]);

(* --------------------------------------------------------------------- *)
(* Induction tactic for this kind of induction.                          *)
(* --------------------------------------------------------------------- *)

fun nc_INDUCT_TAC2 q (A,g) =
  let val (_,P) = dest_comb g
      val ith = ISPEC P nc_INDUCTION2
      fun bconv tm =
        if rator tm !~ P then
          raise mk_HOL_ERR "ncScript.sml" "nc_INDUCT_TAC2"
                           "function bconv failed"
        else BETA_CONV tm
      val bth = CONV_RULE (ONCE_DEPTH_CONV bconv) ith
  in
        (MATCH_MP_TAC bth THEN Q.EXISTS_TAC q THEN REPEAT CONJ_TAC
          THENL [ALL_TAC, ALL_TAC,
                 GEN_TAC THEN GEN_TAC THEN STRIP_TAC,
                 GEN_TAC THEN GEN_TAC THEN
                 REWRITE_TAC [IN_UNION, IN_INSERT, IN_DELETE,
                              DE_MORGAN_THM] THEN
                 STRIP_TAC,
                 ALL_TAC]) (A,g)
  end;

(* ===================================================================== *)
(* So, we can now prove some of Hindley and Seldin's theorems using both *)
(* induction theorems.  The comparison is interesting, as is the         *)
(* sensitivity to order of quantifiers.                                   *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Andy's induction scheme. Fix both t and x.                            *)
(* Compare the original proof of Andy's -- witness FV(u) + FV(t) + {x}   *)
(* --------------------------------------------------------------------- *)

val lemma14b = Q.store_thm(
  "lemma14b",
  `!t x u. ~(x IN FV u) ==> ([t/x]u = u)`,
  NTAC 2 GEN_TAC THEN nc_INDUCT_TAC2 `x INSERT FV t` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);


(* ----------------------------------------------------------------------
    Andy's induction scheme. Fix only t. This also works, but it does
    force an unnecessary case split.
   ---------------------------------------------------------------------- *)

Theorem lemma14b[allow_rebind]:
  !t u x. ~(x IN FV u) ==> ([t/x]u = u)
Proof
  GEN_TAC THEN nc_INDUCT_TAC2 `FV t` THEN
  SRW_TAC [][SUB_THM, SUB_VAR] THEN SRW_TAC [][SUB_THM] THEN
  Cases_on `x = y` THEN SRW_TAC [][SUB_THM]
QED

(* --------------------------------------------------------------------- *)
(* The remaining Hindley and Seldin theorems.                            *)
(* --------------------------------------------------------------------- *)

val lemma14c = Q.store_thm(
  "lemma14c",
  `!t x u. x IN FV u ==> (FV ([t/x]u) = FV t UNION (FV u DELETE x))`,
  NTAC 2 GEN_TAC THEN nc_INDUCT_TAC2 `x INSERT FV t` THEN
  ASM_SIMP_TAC (srw_ss()) [SUB_THM, SUB_VAR, EXTENSION] THENL [
    STRIP_TAC THENL [
      Cases_on `x IN FV u` THEN SRW_TAC [][lemma14b] THEN METIS_TAC [],
      Cases_on `x IN FV t'` THEN SRW_TAC [][lemma14b] THEN METIS_TAC []
    ],
    METIS_TAC []
  ]);

val lemma15a = Q.store_thm("lemma15a",
  `!t y u.
     ~(y IN FV u) ==> ([t/y]([VAR y/x]u) = [t/x]u)`,
  NTAC 2 GEN_TAC THEN nc_INDUCT_TAC2 `{x;y} UNION FV t` THEN
  SRW_TAC [][SUB_THM, SUB_VAR] THEN SRW_TAC [][SUB_VAR]);


val lemma15b = Q.store_thm("lemma15b",
`!y u.
   ~(y IN FV u) ==> !x. [VAR x/y] ([VAR y/x]u) = u`,
RW_TAC std_ss [lemma15a,lemma14a]);


(* --------------------------------------------------------------------- *)
(* BETA is definable given BODY.                                         *)
(* Needs Hindley and Seldin lemma15a.                                    *)
(* --------------------------------------------------------------------- *)

val lemma = Q.prove(
`!x u. (~((@y. ~(y IN (FV(LAM x u)))) IN (FV u)))
       \/
      ((@y. ~(y IN (FV(LAM x u)))) = x)`,
REWRITE_TAC [FV_THM,DE_MORGAN_THM,IN_DELETE]
  THEN REPEAT GEN_TAC THEN CONV_TAC SELECT_CONV
  THEN PROVE_TAC []);

val BETA_EXISTS = Q.prove(
 `?beta.
     !u t x. beta (LAM x u) t = [t/x]u`,
Q.EXISTS_TAC `\lam t. let x = @x. ~(x IN (FV lam)) in [t/x](BODY lam x)`
   THEN RW_TAC std_ss [BODY_DEF, LET_THM]
   THEN STRIP_ASSUME_TAC (SPEC_ALL lemma)
   THEN RW_TAC std_ss [lemma15a,lemma14a]);

val BETA = new_specification ("BETA_DEF", ["BETA"], BETA_EXISTS);

(* --------------------------------------------------------------------- *)
(* BODY is definable given BETA.                                         *)
(* --------------------------------------------------------------------- *)

val lemma = Q.prove(`?body. !x u. body(LAM x ^u) = \y. [VAR y/x]u`,
Q.EXISTS_TAC `\u y. BETA u (VAR y)` THEN RW_TAC std_ss [BETA]);


(* ===================================================================== *)
(* Iterated substitutions.                                               *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(*       t ISUB [(t1,x1),...,(tn,xn)] = t SUB (t1,x1) ... SUB (tn,xn)    *)
(*       DOM [(t1,x1),...,(tn,xn)] = {x1,...,xn}                         *)
(*       FVS [(t1,x1),...,(tn,xn)] = FV t1 UNION ... UNION FV tn         *)
(* --------------------------------------------------------------------- *)

val ISUB_def =
 Define
     `($ISUB t [] = t)
  /\  ($ISUB t ((s,x)::rst) = $ISUB ([s/x]t) rst)`;

val _ = set_fixity "ISUB" (Infixr 501);

val DOM_DEF =
 Define
     `(DOM [] = {})
  /\  (DOM ((x,y)::rst) = {y} UNION DOM rst)`;

val FVS_DEF =
 Define
    `(FVS [] = {})
 /\  (FVS ((t,x)::rst) = FV t UNION FVS rst)`;


val FINITE_DOM = Q.store_thm("FINITE_DOM",
 `!ss. FINITE (DOM ss)`,
Induct THENL [ALL_TAC, Cases]
   THEN RW_TAC std_ss [DOM_DEF, FINITE_EMPTY, FINITE_UNION, FINITE_SING]);
val _ = export_rewrites ["FINITE_DOM"]


val FINITE_FVS = Q.store_thm("FINITE_FVS",
`!ss. FINITE (FVS ss)`,
Induct THENL [ALL_TAC, Cases]
   THEN RW_TAC std_ss [FVS_DEF, FINITE_EMPTY, FINITE_UNION, FINITE_FV]);
val _ = export_rewrites ["FINITE_FVS"]


(* --------------------------------------------------------------------- *)
(* A renaming is a parallel substitution of variables for variables.     *)
(*                                                                       *)
(*       RENAMING []                     always                          *)
(*       RENAMING ((x,VAR y)::R)         if RENAMING R                   *)
(* --------------------------------------------------------------------- *)

val (RENAMING_DEF,RENAMING_IND,RENAMING_CASES) = Hol_reln
     `RENAMING ([]:('a nc # string) list)
  /\  (!R x y. RENAMING R ==> RENAMING ((VAR y,x)::R))`;

val _ = save_thm("RENAMING_DEF",RENAMING_DEF);
val _ = save_thm("RENAMING_IND",RENAMING_IND);
val _ = save_thm("RENAMING_CASES",RENAMING_CASES);

val RENAME_DEF =
 Define
     `(RENAME [] x          = x)
  /\  (RENAME ((p,q)::ss) x = RENAME ss (if x=q then VNAME p else x))`;


val RENAMING_LEMMA = Q.store_thm("RENAMING_LEMMA",
`!ss. RENAMING ss
       ==>
      !tt. RENAMING tt ==> RENAMING (APPEND ss tt)`,
HO_MATCH_MP_TAC RENAMING_IND
   THEN RW_TAC list_ss []
   THEN PROVE_TAC [RENAMING_CASES]);

(* ----------------------------------------------------------------------
    Simple properties of ISUB
   ---------------------------------------------------------------------- *)

val SUB_ISUB_SINGLETON = store_thm(
  "SUB_ISUB_SINGLETON",
  ``!t x u. [t/x]u = u ISUB [(t,x)]``,
  SRW_TAC [][ISUB_def]);

val ISUB_APPEND = store_thm(
  "ISUB_APPEND",
  ``!R1 R2 t. (t ISUB R1) ISUB R2 = t ISUB (APPEND R1 R2)``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, ISUB_def]);

(* ----------------------------------------------------------------------
    ... and of RENAMING
   ---------------------------------------------------------------------- *)

val _ = temp_type_abbrev("renaming", ``:('a nc # string) list``)
val RENAMING_THM = store_thm(
  "RENAMING_THM",
  ``RENAMING ([]:'a renaming) /\
    (!(R:'a renaming) h.
       RENAMING (h::R) ⇔ RENAMING R /\ ?y x. h = (VAR y,x)) /\
    (!R1 R2:'a renaming.
       RENAMING (APPEND R1 R2) ⇔ RENAMING R1 /\ RENAMING R2)``,
  Q.SUBGOAL_THEN
    `RENAMING ([]:'a renaming) /\
    (!R:'a renaming h.
       RENAMING (h::R) ⇔ RENAMING R /\ ?y x. h = (VAR y,x))`
    (fn th => STRIP_ASSUME_TAC th THEN ASM_REWRITE_TAC [])
  THENL [
    SIMP_TAC (srw_ss()) [RENAMING_DEF] THEN REPEAT GEN_TAC THEN
    CONV_TAC (LAND_CONV (REWR_CONV RENAMING_CASES)) THEN SRW_TAC [][] THEN
    PROVE_TAC [],
    Induct THEN SRW_TAC [][] THEN PROVE_TAC []
  ]);


(* --------------------------------------------------------------------- *)
(* Interaction of ISUB with syntax constructors.                         *)
(* --------------------------------------------------------------------- *)

val R = Term `R : ('a nc # string) list`;


val ISUB_VAR_RENAME = Q.store_thm("ISUB_VAR_RENAME",
`!ss. RENAMING ss
        ==>
      !x. (VAR x) ISUB ss = VAR (RENAME ss x)`,
HO_MATCH_MP_TAC RENAMING_IND
  THEN RW_TAC std_ss [ISUB_def, RENAME_DEF, VNAME_DEF, SUB_VAR]
  THEN RW_TAC std_ss []);

val ISUB_CON = Q.store_thm("ISUB_CON",
`!^R k. (CON k) ISUB ^R = CON k`,
Induct THEN Ho_Rewrite.REWRITE_TAC[pairTheory.FORALL_PROD]
 THEN RW_TAC std_ss [ISUB_def, SUB_THM]);

val ISUB_APP = Q.store_thm("ISUB_APP",
`!^R t u. (t @@ u) ISUB ^R = (t ISUB ^R) @@ (u ISUB ^R)`,
Induct THEN Ho_Rewrite.REWRITE_TAC[pairTheory.FORALL_PROD]
  THEN RW_TAC std_ss [ISUB_def, SUB_THM]);

val ISUB_LAM = Q.store_thm("ISUB_LAM",
`!^R x. ~(x IN (DOM ^R UNION FVS ^R))
           ==>
        !t. (LAM x t) ISUB ^R = LAM x (t ISUB ^R)`,
Induct THENL
 [ALL_TAC, Ho_Rewrite.REWRITE_TAC[pairTheory.FORALL_PROD]
           THEN Cases_on `x` THEN POP_ASSUM MP_TAC]
 THEN RW_TAC list_ss
 [ISUB_def,DOM_DEF,FVS_DEF,FV_THM,IN_UNION,IN_SING,DE_MORGAN_THM,SUB_THM]);

val _ = export_rewrites ["nc_DISTINCT","nc_INJECTIVITY", "LAM_VAR_INJECTIVE"];


val FV_SUB = store_thm(
  "FV_SUB",
  ``!t u v. FV ([t/v] u) = if v IN FV u then FV t UNION (FV u DELETE v)
                           else FV u``,
  PROVE_TAC [lemma14b, lemma14c]);

val nc_RECURSION2 = save_thm(
  "nc_RECURSION2",
  (SIMP_RULE bool_ss [ABS_DEF] o
   Q.INST [`lam'` |-> `lam`] o
   Q.INST [`lam` |-> `\r t. let v = NEW (FV (ABS t) UNION X)
                            in lam' (r v) v (t v)`] o
   SPEC_ALL) nc_RECURSION)

val size_def = new_specification (
  "size", ["size"],
  (CONJUNCT1 o
   CONV_RULE EXISTS_UNIQUE_CONV o
   SIMP_RULE bool_ss [pred_setTheory.UNION_EMPTY] o
   Q.INST [`con` |-> `\x. 1`, `var` |-> `\s. 1`,
           `app` |-> `\rt ru t u. rt + ru + 1`,
           `lam` |-> `\rt v t. rt + 1`,
           `X` |-> `{}`] o
   INST_TYPE [beta |-> numSyntax.num]) nc_RECURSION2)

val _ = augment_srw_ss [rewrites [LET_THM]]
val size_isub = store_thm(
  "size_isub",
  ``!t R. RENAMING R ==> (size (t ISUB R) = size t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][ISUB_CON, size_def],
    SRW_TAC [][ISUB_VAR_RENAME, size_def],
    SRW_TAC [][ISUB_APP, size_def],
    REPEAT STRIP_TAC THEN
    Q.ABBREV_TAC `avds = FVS R UNION DOM R UNION FV t` THEN
    `FINITE avds`
       by (Q.UNABBREV_TAC `avds` THEN
           SRW_TAC [][FINITE_FVS, FINITE_DOM, FINITE_FV]) THEN
    Q.ABBREV_TAC `z = NEW avds` THEN
    `~(z IN avds)`
        by (Q.UNABBREV_TAC `z` THEN SRW_TAC [][NEW_def]) THEN
    `~(z IN FVS R) /\ ~(z IN DOM R) /\ ~(z IN FV t)`
        by (Q.UNABBREV_TAC `z` THEN Q.UNABBREV_TAC `avds` THEN
            SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []) THEN
    REPEAT (Q.PAT_X_ASSUM `Abbrev X` (K ALL_TAC)) THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [][ISUB_LAM] THEN
    ASM_SIMP_TAC bool_ss [size_def] THEN
    ONCE_REWRITE_TAC [SUB_ISUB_SINGLETON] THEN
    ASM_SIMP_TAC bool_ss [ISUB_APPEND,RENAMING_DEF, RENAMING_LEMMA] THEN
    SRW_TAC [][]
  ]);

val size_vsubst = store_thm(
  "size_vsubst",
  ``size ([VAR v/u] t) = size t``,
  SRW_TAC [][size_isub, SUB_ISUB_SINGLETON, RENAMING_DEF]);
val _ = export_rewrites ["size_vsubst"]

val size_thm = save_thm(
  "size_thm",
  SIMP_RULE (srw_ss()) [size_vsubst] size_def);

val size_nonzero = store_thm(
  "size_nonzero",
  ``!t. 0 < size t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [numSimps.ARITH_ss][size_thm]);

val _ = export_theory();
