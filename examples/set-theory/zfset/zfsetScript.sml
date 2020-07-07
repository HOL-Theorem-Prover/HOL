
(*****************************************************************************)
(* Development of set theory on top of the axioms for ``:zfset``             *)
(* in zfset_axiomsTheory (a port of the 1994 HOL88 file mk_ST.ml to HOL4)    *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE FOR COMPILATION                                         *)
(*****************************************************************************)

(******************************************************************************
* Load theories
******************************************************************************)
(* Load for interative use
quietdec := true;
map load ["zfset_axiomsTheory","pred_setLib","pairLib"];
open zfsetTheory pred_setLib pred_setTheory pairLib pairTheory combinTheory;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;
open zfset_axiomsTheory pred_setLib pred_setTheory pairLib
     pairTheory combinTheory;

(******************************************************************************
* Open theories
******************************************************************************)

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)


(*****************************************************************************)
(* Create zfset_extras_theory.                                               *)
(*****************************************************************************)
val _ = new_theory "zfset";
val _ = ParseExtras.temp_loose_equality()

(*---------------------------------------------------------------------------*)
(* Hack to hide constant ``W``, where: |- W = (\f x. f x x)                  *)
(*---------------------------------------------------------------------------*)
val _ = hide "W";

val ImageId =
 store_thm
  ("ImageId",
   ``!s. Image (\x. x) s = s``,
   RW_TAC std_ss [Extension_ax,Image_def]);

(*---------------------------------------------------------------------------*)
(* The Axiom of Choice                                                       *)
(*---------------------------------------------------------------------------*)
val Choice =
 store_thm
 ("Choice",
  ``?f. !s. ~(s = Empty) ==> f s In s``,
  Q.EXISTS_TAC `\s.@x. x In s`
   THEN BETA_TAC
   THEN REWRITE_TAC[GSYM NotEmpty]
   THEN REPEAT GEN_TAC
   THEN DISCH_TAC
   THEN POP_ASSUM(ACCEPT_TAC o SELECT_RULE));

(*---------------------------------------------------------------------------*)
(* Definition of an inhabited (i.e. non-empty) set.                          *)
(*---------------------------------------------------------------------------*)
val Inhab_def =
 Define
  `Inhab X = ?x. x In X`;

(*---------------------------------------------------------------------------*)
(* Singleton = |- !x y. y In (Sing x) = (y = x)                              *)
(*---------------------------------------------------------------------------*)
val SetCons_def =
 Define
  `SetCons x s = Singleton x U s`;

val _ = overload_on("EMPTY", ``Empty``);
val _ = overload_on("INSERT",``SetCons``);

val InSetCons =
 store_thm
  ("InSetCons",
   ``!x s t. x In (SetCons s t) = ((x = s) \/ x In t)``,
   METIS_TAC[SetCons_def,Extension_ax,U_def,Singleton_def]);

val InSing =
 store_thm
  ("InSing",
   ``!x y. x In {y} = (x = y)``,
   METIS_TAC[Extension_ax,U_def,Singleton_def,InSetCons,Empty_def]);

val SingNotEmpty =
 store_thm
  ("SingNotEmpty",
   ``!x. ~({x} = {}) /\ ~({} = {x})``,
   METIS_TAC[Extension_ax,InSing,Empty_def]);

val InDouble =
 store_thm
  ("InDouble",
   ``!x x1 x2. x In {x1;x2} = ((x = x1) \/ (x = x2))``,
   METIS_TAC[Extension_ax,U_def,Singleton_def,InSetCons,Empty_def]);

val DoubleNotEmpty =
 store_thm
  ("DoubleNotEmpty",
   ``!x y. ~({x;y} = {}) /\ ~({} = {x;y})``,
   METIS_TAC[Extension_ax,InDouble,Empty_def]);

val SingEq =
 store_thm
  ("SingEq",
   ``!x1 x2. ({x1} = {x2}) = (x1 = x2)``,
   METIS_TAC[Extension_ax,InSing]);

val NotInSelf =
 store_thm
  ("NotInSelf",
   ``!x. ~(x In x)``,
   METIS_TAC[SingNotEmpty,InSing,Foundation_ax,Intersect_def,Empty_def]);

val InRefl =
 store_thm
  ("InRefl",
   ``!x y. x In y ==> ~(y In x)``,
   METIS_TAC[Foundation_ax,InDouble,DoubleNotEmpty,Intersect_def,Empty_def]);

val DoubleRefl =
 store_thm
  ("DoubleRefl",
   ``!x. {x;x} = {x}``,
  METIS_TAC[Extension_ax,InSing,InDouble]);

val SingDoubleEq =
 store_thm
  ("SingDoubleEq",
   ``!x x1 x2. ({x} = {x1;x2}) = (x = x1) /\ (x = x2)``,
   METIS_TAC[Extension_ax,InSing,InDouble]);

val DoubleCancel =
 store_thm
  ("DoubleCancel",
   ``!x x1 x2. ({x;x1} = {x;x2}) = (x1 = x2)``,
   METIS_TAC[Extension_ax,InDouble]);

val Pair_def =
 Define
  `Pair x y = {{x}; {x;y}}`;

val PairEqLemma1 =
 store_thm
  ("PairEqLemma1",
   ``!x x1 x2. ~(x1 = x2) ==> ~({x} = {x1;x2})``,
   METIS_TAC[Pair_def,Extension_ax,InSing,InDouble]);

val PairEq =
 store_thm
  ("PairEq",
   ``!x1 x2 y1 y2. (Pair x1 y1 = Pair x2 y2) = (x1 = x2) /\ (y1 = y2)``,
  REPEAT GEN_TAC
   THEN REWRITE_TAC[Pair_def,DoubleRefl,SingDoubleEq,SingEq]
   THEN ASM_CASES_TAC ``(x1:zfset) = y1``
   THEN ASM_CASES_TAC ``(x2:zfset) = y2``
   THENL
    [RW_TAC std_ss [DoubleRefl,SingEq],
     METIS_TAC[DoubleRefl,SingEq,SingDoubleEq],
     METIS_TAC[DoubleRefl,SingEq,SingDoubleEq],
     IMP_RES_TAC PairEqLemma1
      THEN ONCE_REWRITE_TAC[Extension_ax]
      THEN ONCE_REWRITE_TAC[InDouble]
      THEN REWRITE_TAC[GSYM Extension_ax]
      THEN EQ_TAC
      THEN REPEAT STRIP_TAC
      THEN ASM_REWRITE_TAC[]
      THEN ASSUM_LIST(fn thl =>(ASSUME_TAC(SIMP_RULE std_ss [el 2 thl, el 3 thl, SingEq] (Q.SPEC `{x1}` (el 1 thl)))))
      THEN RW_TAC std_ss []
      THEN ASM_CASES_TAC ``(y1:zfset) = y2``
      THEN RW_TAC std_ss []
      THEN ASSUM_LIST(fn thl =>(ASSUME_TAC(SIMP_RULE std_ss [] (Q.SPEC `{x2;x1}` (el 2 thl)))))
      THEN METIS_TAC[DoubleRefl,SingDoubleEq,SingEq,InSing,InDouble]]);

val Fst_def =
 Define
  `Fst p = @x. ?y. p = Pair x y`;

val Snd_def =
 Define
  `Snd p = @y. ?x. p = Pair x y`;

val FstLemma =
 prove
  (``!x. (@x'. ?y'. Pair x y = Pair x' y') = x``,
   RW_TAC std_ss [PairEq]);

val Fst =
 store_thm
  ("Fst",
   ``!x y. Fst(Pair x y) = x``,
   METIS_TAC[Fst_def,FstLemma]);

val SndLemma =
 prove
  (``!y. (@y'. ?x'. Pair x y = Pair x' y') = y``,
   RW_TAC std_ss [PairEq]);

val Snd =
 store_thm
  ("Snd",
   ``!x y. Snd(Pair x y) = y``,
   METIS_TAC[Snd_def,SndLemma]);

val SingletonThm =
 store_thm
  ("SingletonThm",
   ``!x. Singleton x = {x}``,
   METIS_TAC[Extension_ax,InSing,Singleton_def]);

val NotSuc =
 store_thm
  ("NotSuc",
   ``!x. ~(Suc x = {}) /\ ~({} = Suc x)``,
  METIS_TAC[SingletonThm,Extension_ax,U_def,InSing,Empty_def,Suc_def]);

val InvSucEq =
 store_thm
  ("InvSucEq",
   ``!x y. (Suc x = Suc y) = (x = y)``,
  RW_TAC std_ss [Suc_def,Extension_ax,U_def,InSing,Singleton_def]
   THEN METIS_TAC[InRefl]);

(*---------------------------------------------------------------------------*)
(* InfSet = |- {} In InfSet /\ (!x. x In InfSet ==> (Suc x) In InfSet)       *)
(*---------------------------------------------------------------------------*)
val InfSet_def = new_specification("InfSet_def", ["InfSet"], Infinity_ax);

(*---------------------------------------------------------------------------*)
(* |- SET_TYPE s (rep:ty->zfset)                                             *)
(*                                                                           *)
(* If s is in bijection with ty.                                             *)
(*---------------------------------------------------------------------------*)
val SET_TYPE_def =
 Define
  `SET_TYPE s (rep:'a->zfset) = TYPE_DEFINITION (\x. x In s) rep`;

val SET_TYPE_In =
 store_thm
  ("SET_TYPE_In",
   ``!s (rep:'a->zfset). SET_TYPE s rep ==> !x. rep x In s``,
   RW_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION]
    THEN POP_ASSUM(ASSUME_TAC o SPEC ``(rep:'a->zfset)x``)
    THEN METIS_TAC[]);

(*---------------------------------------------------------------------------*)
(* Truth values.                                                             *)
(*---------------------------------------------------------------------------*)

val False_def =
 Define
  `False = {}`;

val True_def =
 Define
  `True = {{}}`;

val Bool_def =
 Define
  `Bool = {False;True}`;

val Bool_CLAUSES =
 store_thm
  ("Bool_CLAUSES",
   ``~(True = False) /\ ~(False = True)``,
  REWRITE_TAC[True_def,False_def,SingNotEmpty]);

val InhabBool =
 store_thm
  ("InhabBool",
   ``Inhab Bool``,
   METIS_TAC[Inhab_def,Bool_def,InDouble]);

val bool2Bool_def =
 Define
  `bool2Bool b = if b then True else False`;

val bool2BoolEqTrue =
 store_thm
  ("bool2BoolEqTrue",
   ``!b. (bool2Bool b = True) = b``,
   METIS_TAC[bool2Bool_def,Bool_CLAUSES]);

val bool2BoolEqFalse =
 store_thm
  ("bool2BoolEqFalse",
   ``!b. (bool2Bool b = False) = ~b``,
   METIS_TAC[bool2Bool_def,Bool_CLAUSES]);

val bool2BoolEq =
 store_thm
  ("bool2BoolEq",
   ``!b1 b2. (bool2Bool b1 = bool2Bool b2) = (b1 = b2)``,
   METIS_TAC[bool2Bool_def,Bool_CLAUSES]);

val TrueInBool =
 store_thm
  ("TrueInBool",
   ``True In Bool``,
  REWRITE_TAC[True_def,Bool_def,InSetCons]);

val FalseInBool =
 store_thm
  ("FalseInBool",
   ``False In Bool``,
  REWRITE_TAC[True_def,Bool_def,InSetCons]);

val boolBool =
 store_thm
  ("boolBool",
   ``SET_TYPE Bool bool2Bool``,
   RW_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION,bool2BoolEq,Bool_def,bool2Bool_def,InDouble]
    THEN METIS_TAC[]);

(*---------------------------------------------------------------------------*)
(* Proof that Von Neumann numbers are isomorphic to HOL's numbers.           *)
(*---------------------------------------------------------------------------*)
val num2Num_def =
 Define
  `(num2Num 0 = {}) /\
   (num2Num(SUC n) = Suc(num2Num n))`;

val num2NumInf =
 store_thm
  ("num2NumInf",
   ``!n. num2Num n In InfSet``,
  Induct
   THEN RW_TAC std_ss [num2Num_def,InfSet_def]);

(*---------------------------------------------------------------------------*)
(* Von Neumann numbers.                                                      *)
(*---------------------------------------------------------------------------*)

val Num_def =
 Define
  `Num = Spec InfSet (\s. ?n. s = num2Num n)`;

val InhabNum =
 store_thm
  ("InhabNum",
   ``Inhab Num``,
   RW_TAC std_ss [Inhab_def]
    THEN EXISTS_TAC ``num2Num 0``
    THEN RW_TAC std_ss [Num_def,Spec_def]
    THEN METIS_TAC[num2NumInf]);

val num2NumSucNotEmpty =
 store_thm
  ("num2NumSucNotEmpty",
   ``!n.  num2Num 0 <> num2Num (SUC n)``,
   Induct
    THEN RW_TAC std_ss [NotSuc,num2Num_def,InvSucEq]);

val num2NumInfset =
 store_thm
  ("num2NumInfset",
   ``!n. num2Num n In InfSet``,
   Induct
    THEN RW_TAC std_ss [NotSuc,num2Num_def,InvSucEq,InfSet_def]);

val numNum =
 store_thm
  ("numNum",
   ``SET_TYPE Num num2Num``,
   SIMP_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION]
    THEN CONJ_TAC
    THENL
     [Induct THEN Induct
       THEN RW_TAC std_ss [NotSuc,num2Num_def,InvSucEq],
      RW_TAC std_ss [Num_def,Spec_def]
       THEN METIS_TAC[num2NumInfset]]);

(*---------------------------------------------------------------------------*)
(* Representation of product types.                                          *)
(*---------------------------------------------------------------------------*)

val PROD_def =
 Define
  `$PROD (rep1:'a->zfset) (rep2:'b->zfset) = \(x1,x2). Pair(rep1 x1)(rep2 x2)`;

val _ = set_fixity "PROD" (Infixr 400); (* Precedence may need adjusting *)

val PairPROD =
 store_thm
  ("PairPROD",
   ``!(rep1:'a->zfset) (rep2:'b->zfset) x1 x2.
    Pair (rep1 x1) (rep2 x2) = (rep1 PROD rep2)(x1,x2)``,
  RW_TAC std_ss [PROD_def]);

(*---------------------------------------------------------------------------*)
(* Cartesian product of sets.                                                *)
(*---------------------------------------------------------------------------*)

val Prod_def =
 Define
  `$Prod s1 s2 =
     Spec
      (Pow(Pow(s1 U s2)))
      (\s. ?x1 x2. (s = Pair x1 x2) /\ x1 In s1 /\ x2 In s2)`;

val _ = set_fixity "#" (Infixr 400); (* Precedence may need adjusting *)

val _ = overload_on("#", ``$Prod``);

val PairBound =
 store_thm
  ("PairBound",
   ``!x1 x2 s1 s2. x1 In s1 /\ x2 In s2 ==> Pair x1 x2 In Pow(Pow(s1 U s2))``,
   RW_TAC std_ss [Pair_def,Pow_def,U_def,InDouble,InSing]
    THEN FULL_SIMP_TAC std_ss [InSing,InDouble]);

val InProd =
 store_thm
  ("InProd",
   ``!x1 x2 s1 s2. x1 In s1 /\ x2 In s2 = Pair x1 x2 In (s1 # s2)``,
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss[Pair_def,InSing,InDouble]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss[Pair_def,InSing,InDouble]
    THEN RW_TAC std_ss []);

val InProdEq =
 store_thm
  ("InProdEq",
   ``!z s1 s2 x1 x2.
       z In (s1 # s2) = ?x1 x2. x1 In s1 /\ x2 In s2 /\ (z = Pair x1 x2)``,
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss[Pair_def,InSing,InDouble]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss[Pair_def,InSing,InDouble]
    THEN RW_TAC std_ss []
    THEN METIS_TAC[]);

val FstType =
 store_thm
  ("FstType",
   ``!p X Y. p In (X # Y) ==> (Fst p) In X``,
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN RW_TAC std_ss [Fst]);

val SndType =
 store_thm
  ("SndType",
   ``!p X Y. p In (X # Y) ==> (Snd p) In Y``,
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN RW_TAC std_ss [Snd]);

val PairIn =
 store_thm
  ("PairIn",
   ``!p. p In (X # Y) ==> (Pair(Fst p)(Snd p) = p)``,
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN RW_TAC std_ss [PairEq,Fst,Snd]);

val EmptyProd = Q.store_thm(
"EmptyProd",
`∀x. ({} # x = {}) ∧ (x # {} = {})`,
srw_tac [][Extension_ax,Empty_def,InProdEq]);
val _ = export_rewrites["EmptyProd"];

val ProdEmpty = Q.store_thm(
"ProdEmpty",
`∀x y. (x # y = {}) = ((x = {}) \/ (y = {}))`,
srw_tac [][EQ_IMP_THM] >> srw_tac [][] >>
spose_not_then strip_assume_tac >>
fsrw_tac [][GSYM NotEmpty] >>
metis_tac [InProd,Empty_def]);

val ProdEq = Q.store_thm(
"ProdEq",
`!x1 x2 y1 y2. (x1 # y1 = x2 # y2) = ((x1 # y1 = {}) /\ (x2 # y2 = {})) \/ ((x1 = x2) /\ (y1 = y2))`,
rpt gen_tac >>
reverse EQ_TAC >- (
  srw_tac [][] >> srw_tac [][] ) >>
strip_tac >>
srw_tac [][ProdEmpty] >>
Cases_on `x1 = {}` >- (
  fsrw_tac [][] >> fsrw_tac [][ProdEmpty] ) >>
Cases_on `y1 = {}` >- (
  fsrw_tac [][] >> fsrw_tac [][ProdEmpty] ) >>
Cases_on `x2 = {}` >- (
  fsrw_tac [][] >> fsrw_tac [][ProdEmpty] ) >>
Cases_on `y2 = {}` >- (
  fsrw_tac [][] >> fsrw_tac [][ProdEmpty] ) >>
srw_tac [][] >>
fsrw_tac [][GSYM NotEmpty] >>
fsrw_tac [][Extension_ax] >>
fsrw_tac [][InProdEq] >>
PROVE_TAC [PairEq]);

val ABS_THM =
 store_thm
  ("ABS_THM",
   ``!P rep.
      TYPE_DEFINITION P rep
      ==>
      (?abs. (!a. abs(rep a) = a) /\ (!r. P r = (rep(abs r) = r)))``,
   METIS_TAC[TYPE_DEFINITION_THM]);

val Abs_def =
 Define
  `Abs s (rep:'a->zfset) =
    @abs. (!a. abs(rep a) = a) /\ !r. r In s = (rep(abs r) = r)`;

val Abs =
 store_thm
  ("Abs",
   ``!s (rep:'a->zfset).
     SET_TYPE s rep
     ==>
     (!a. Abs s rep(rep a) = a) /\ !r. r In s = (rep(Abs s rep r) = r)``,
   RW_TAC std_ss [SET_TYPE_def,Abs_def]
    THEN SELECT_ELIM_TAC
    THEN RW_TAC std_ss []
    THEN IMP_RES_TAC ABS_THM
    THEN FULL_SIMP_TAC std_ss []
    THEN METIS_TAC[]);

val AbsOneOne =
 store_thm
  ("AbsOneOne",
   ``!s (rep:'a->zfset).
      SET_TYPE s rep
      ==>
      !x1 x2.
       x1 In s /\ x2 In s ==> ((Abs s rep x1 = Abs s rep x2) = (x1 = x2))``,
   METIS_TAC[Abs]);

val Num2num_def =
 Define
  `Num2num = Abs Num num2Num`;

val Num2num_CLAUSES =
 store_thm
  ("Num2num_CLAUSES",
   ``(!a. Num2num(num2Num a) = a) /\
     (!r. r In Num = (num2Num(Num2num r) = r))``,
   METIS_TAC[Num2num_def,Abs,numNum]);

(*---------------------------------------------------------------------------*)
(* Union of a countable sequence of sets.                                    *)
(*---------------------------------------------------------------------------*)
val _ = new_binder("Us",``:(num -> zfset) -> zfset``);

val Us_def =
 Define
  `$Us s = UU(Image (s o Num2num) Num)`;

val InUs =
 store_thm
  ("InUs",
   ``!s x. x In ($Us s) = ?n. x In s n``,
   RW_TAC std_ss [Us_def,UU_def,Image_def,o_DEF,Num2num_CLAUSES]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [METIS_TAC[],
      Q.EXISTS_TAC `s n`
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `num2Num n`
       THEN RW_TAC std_ss [Num2num_CLAUSES]]);

val UsU =
 store_thm
  ("UsU",
   ``!s1 s2. (Us n. s1 n U s2 n) = (Us n. s1 n) U (Us n. s2 n)``,
   RW_TAC std_ss [U_def,InUs,Extension_ax]
    THEN METIS_TAC[]);

val PROD_REP =
 store_thm
  ("PROD_REP",
   ``!s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      SET_TYPE (s1 # s2) (rep1 PROD rep2)``,
   SIMP_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION_THM,Prod_def,PROD_def,Spec_def]
    THEN GEN_BETA_TAC
    THEN RW_TAC std_ss [PairEq]
    THENL
     [METIS_TAC[PAIR],
      EQ_TAC
       THEN RW_TAC std_ss [PairEq]
       THEN RW_TAC std_ss [PairEq]
       THENL
        [Q.EXISTS_TAC `(x',x'')`
          THEN RW_TAC std_ss [],
         METIS_TAC[PairBound],
         METIS_TAC[PAIR],
         METIS_TAC[PAIR]]]);

(*---------------------------------------------------------------------------*)
(* Set of partial functions (single valued relations) from X to Y            *)
(*---------------------------------------------------------------------------*)
val Pfn_def =
 Define
  `Pfn X Y =
    Spec
     (Pow(X # Y))
     (\r. !x y1 y2. Pair x y1 In r /\ Pair x y2 In r ==> (y1=y2))`;

(*---------------------------------------------------------------------------*)
(* Set of functions from X to Y                                              *)
(*---------------------------------------------------------------------------*)
val Fn_def =
 Define
  `$Fn X Y =
    Spec
     (Pfn X Y)
     (\f. !x. x In X ==> ?y. y In Y /\ Pair x y In f)`;

val _ = set_fixity "->" (Infixr 400); (* Precedence may need adjusting *)
val _ = overload_on("->",``Fn``);

(*---------------------------------------------------------------------------*)
(* Application of a set-funtion to an argument.                              *)
(*---------------------------------------------------------------------------*)
val Apply_def =
 Define
  `Apply s x = @y. Pair x y In s`;

val _ = set_fixity "'" (Infixl 600); (* Precedence may need adjusting *)
val _ = overload_on("'",``Apply``);

val ApUnion =
 store_thm
  ("ApUnion",
   ``!x1 x2 v s.
      ~(x1 = x2) ==> ((s U {Pair x1 v}) ' x2 = s ' x2)``,
   RW_TAC std_ss [Apply_def,Pair_def,U_def,InSing,PairEq]);

val ApSing =
 store_thm
  ("ApSing",
   ``!x v. {Pair x v} ' x = v``,
   RW_TAC std_ss [Apply_def,Pair_def,U_def,InSing,PairEq]);

val ApPfn =
 store_thm
  ("ApPfn",
   ``!f X Y x.
      f In Pfn X Y /\ (?y. Pair x y In f)
      ==>
      !y. (f ' x = y) = Pair x y In f``,
   RW_TAC std_ss [Pfn_def,Pow_def,InProdEq,PairEq,Spec_def,Apply_def]
    THEN SELECT_ELIM_TAC
    THEN METIS_TAC[]);

val ApFn =
 store_thm
  ("ApFn",
   ``!f X Y x. f In (X -> Y) /\  x In X ==> !y. (f ' x = y) = Pair x y In f``,
   RW_TAC std_ss [Fn_def,Spec_def]
    THEN METIS_TAC[ApPfn]);

val InFn =
 store_thm
  ("InFn",
   ``!f x X Y. f In (X -> Y) /\ x In X  ==> (f ' x) In Y``,
   RW_TAC std_ss []
    THEN `!y. (f ' x = y) <=> Pair x y In f` by METIS_TAC[ApFn ]
    THEN FULL_SIMP_TAC std_ss [Pfn_def,Pow_def,Fn_def,Spec_def,InProdEq]
    THEN METIS_TAC[]);

val ExtFn =
 store_thm
  ("ExtFn",
   ``!X Y f g.
      f In (X -> Y) /\ g In (X -> Y)
      ==>
      ((f = g) = (!x. x In X ==> (f ' x = g ' x)))``,
   RW_TAC std_ss [ApFn]
    THEN `!x. x In X ==> !y. (f ' x = y) <=> Pair x y In f` by METIS_TAC[ApFn]
    THEN `!x. x In X ==> !y. (g ' x = y) <=> Pair x y In g` by METIS_TAC[ApFn]
    THEN FULL_SIMP_TAC std_ss [Extension_ax,Pow_def,InProdEq,Fn_def,Pfn_def,Spec_def]
    THEN METIS_TAC[Extension_ax]);

val FnEqThm = Q.store_thm(
"FnEqThm",
`!f g X Y. f In (X -> Y) /\ g In (X -> Y) /\ (!x. x In X ==> (f ' x = g ' x))
  ==> (f = g)`,
metis_tac [ExtFn])

(*---------------------------------------------------------------------------*)
(* RepSet(f:'a->zfset) =  the image of f as a set in zfset                   *)
(*---------------------------------------------------------------------------*)

val RepSet_def =
 Define
  `RepSet(f:'a->zfset) = @s. !y. y In s = ?x. y = f x`;

val RepSetThm =
 store_thm
  ("RepSetThm",
   ``!s (rep:'a->zfset). SET_TYPE s rep ==> (RepSet rep = s)``,
   RW_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION,RepSet_def,Extension_ax]
    THEN METIS_TAC[]);

val RepSetIn =
 store_thm
  ("RepSetIn",
   ``!s (rep:'a->zfset). SET_TYPE s rep ==> !x. rep x In RepSet rep``,
   RW_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION,RepSet_def,Extension_ax]
    THEN METIS_TAC[]);

val RepSetPROD =
 store_thm
  ("RepSetPROD",
   ``!(rep1:'a->zfset) (rep2:'b->zfset) s1 s2.
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      (RepSet(rep1 PROD rep2) = s1 # s2)``,
   METIS_TAC[PROD_REP,RepSetThm]);

val SET_TYPE_PROD =
 store_thm
  ("SET_TYPE_PROD",
   ``!s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
       SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
       ==>
       !p. (rep1 PROD rep2) p In (s1 # s2)``,
   METIS_TAC[RepSetPROD,RepSetThm,PROD_REP,SET_TYPE_In]);

(*---------------------------------------------------------------------------*)
(* Representation of function types.                                         *)
(*---------------------------------------------------------------------------*)
val FUN_def =
 Define
  `$FUN (rep1:'a->zfset) (rep2:'b->zfset) =
    \f. Spec
         (RepSet rep1 # RepSet rep2)
         (\s. ?x' y'.
               (s = Pair x' y')
               /\
               ?x y. (x' = rep1 x) /\ (y' = rep2 y) /\ (f x = y))`;

val _ = set_fixity "FUN" (Infixr 700); (* Precedence may need adjusting *)

val FUNIn =
 store_thm
  ("FUNIn",
   ``!s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2 ==>
      !f x. Pair (rep1 x) (rep2(f x)) In (rep1 FUN rep2) f``,
   RW_TAC std_ss [FUN_def,Spec_def,PairEq,InProdEq]
    THEN METIS_TAC[RepSetIn]);

val ONE_ONE_EQ =
 store_thm
  ("ONE_ONE_EQ",
   ``!f:'a->'b. ONE_ONE f = !x1 x2. (f x1 = f x2) = (x1 = x2)``,
   METIS_TAC [ONE_ONE_DEF]);

val SET_TYPE_ONE_ONE =
 store_thm
  ("SET_TYPE_ONE_ONE",
   ``!(rep:'a->zfset) s. SET_TYPE s rep ==> ONE_ONE rep``,
   METIS_TAC[SET_TYPE_def,TYPE_DEFINITION,ONE_ONE_DEF]);

val FUNSingleValued =
 store_thm
  ("FUNSingleValued",
   ``!(rep1:'a->zfset) (rep2:'b->zfset) f x y1 y2.
      ONE_ONE rep1 /\
      Pair x y1 In (rep1 FUN rep2) f /\ Pair x y2 In (rep1 FUN rep2) f
      ==>
      (y1 = y2)``,
   RW_TAC std_ss [FUN_def,ONE_ONE_DEF,PairEq,Spec_def,InProdEq]
    THEN METIS_TAC[]);

val FUN_ONE_ONE =
 store_thm
  ("FUN_ONE_ONE",
   ``!(rep1:'a->zfset)(rep2:'b->zfset) s1 s2.
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      !f g. ((rep1 FUN rep2) f = (rep1 FUN rep2) g) = (f = g)``,
   METIS_TAC[FUNIn,SET_TYPE_ONE_ONE,ONE_ONE_DEF,FUNSingleValued]);

val FUN_REP =
 store_thm
  ("FUN_REP",
   ``!s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      SET_TYPE (s1 -> s2) (rep1 FUN rep2)``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC RepSetThm
    THEN IMP_RES_TAC SET_TYPE_def
    THEN IMP_RES_TAC ABS_THM
    THEN IMP_RES_TAC FUN_ONE_ONE
    THEN IMP_RES_TAC RepSetIn
    THEN FULL_SIMP_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION]
    THEN RW_TAC std_ss []
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `abs' o (Apply x) o rep1`
       THEN RW_TAC std_ss [Extension_ax,FUN_def,Spec_def,InProdEq,Pow_def,U_def]
       THEN CONV_TAC(RHS_CONV(SIMP_CONV std_ss [GSYM Extension_ax]))
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Q.EXISTS_TAC `Fst x'` THEN Q.EXISTS_TAC `Snd x'`
          THEN FULL_SIMP_TAC std_ss [Fn_def,Pfn_def,Spec_def,Pow_def]
          THEN RES_TAC
          THEN RW_TAC std_ss []
          THEN METIS_TAC[InProdEq,Fst,Snd,PairIn],
         Q.EXISTS_TAC `Fst x'` THEN Q.EXISTS_TAC `Snd x'`
          THEN ASSUM_LIST(ASSUME_TAC o SIMP_RULE std_ss [Fn_def,Pfn_def,Spec_def,Pow_def] o el 2)
          THEN RES_TAC
          THEN RW_TAC std_ss []
          THEN METIS_TAC[InProdEq,Fst,Snd,PairIn,ApFn],
         FULL_SIMP_TAC std_ss [PairEq]
          THEN RW_TAC std_ss []
          THEN `x ' rep1 x'' In RepSet rep2` by METIS_TAC[InFn]
          THEN RES_TAC
          THEN RW_TAC std_ss []
          THEN METIS_TAC[ApFn]],
      RW_TAC std_ss [FUN_def,Pfn_def,Fn_def,Spec_def,InProdEq,Pow_def,U_def,PairEq]
       THEN METIS_TAC[]]);

val RepSetFUN =
 store_thm
  ("RepSetFUN",
   ``!(rep1:'a->zfset) (rep2:'b->zfset) s1 s2.
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      (RepSet(rep1 FUN rep2) = s1 -> s2)``,
   METIS_TAC[RepSetThm,FUN_REP]);

val SET_TYPE_FUN =
 store_thm
  ("SET_TYPE_FUN",
   ``!s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
       SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
       ==>
       !f. (rep1 FUN rep2)f In (s1 -> s2)``,
   METIS_TAC[RepSetThm,RepSetFUN,FUN_REP,SET_TYPE_In]);

val ApRep =
 store_thm
  ("ApRep",
   ``!(rep1:'a->zfset) (rep2:'b->zfset) s1 s2 f x.
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      ((rep1 FUN rep2) f ' (rep1 x) = rep2(f x))``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC FUNIn
    THEN `?y. (Pair (rep1 x) y) In ((rep1 FUN rep2)(f:'a->'b))` by METIS_TAC[]
    THEN RW_TAC std_ss [Apply_def]
    THEN METIS_TAC[SET_TYPE_ONE_ONE,FUNSingleValued,FUNIn]);

val IsRep_def =
 Define
  `IsRep(rep:'a->zfset) = ?s. SET_TYPE s rep`;

val IsRepThm =
 store_thm
  ("IsRepThm",
   ``!rep:'a->zfset. IsRep rep ==> !s. SET_TYPE s rep = (RepSet rep = s)``,
   METIS_TAC[IsRep_def,RepSetThm]);

val IsRep_SET_TYPE =
 store_thm
  ("IsRep_SET_TYPE",
   ``!rep:'a->zfset. IsRep rep ==> SET_TYPE (RepSet rep) rep``,
   METIS_TAC[IsRepThm]);

val IsRep_num2Num =
 store_thm
  ("IsRep_num2Num",
   ``IsRep num2Num``,
   RW_TAC std_ss[IsRep_def]
    THEN METIS_TAC[numNum]);

val IsRep_bool2Bool =
 store_thm
  ("IsRep_bool2Bool",
   ``IsRep bool2Bool``,
   METIS_TAC[IsRep_def,boolBool]);

val IsRep_PROD =
 store_thm
  ("IsRep_PROD",
   ``!(rep1:'a->zfset) (rep2:'b->zfset).
      IsRep rep1 ==> IsRep rep2 ==> IsRep(rep1 PROD rep2)``,
   METIS_TAC[IsRep_def,PROD_REP]);

val IsRep_FUN =
 store_thm
  ("IsRep_FUN",
   ``!(rep1:'a->zfset) (rep2:'b->zfset).
      IsRep rep1 ==> IsRep rep2 ==> IsRep(rep1 FUN rep2)``,
   METIS_TAC[IsRep_def,FUN_REP]);

val ApRepCor =
 store_thm
  ("ApRepCor",
   ``!(rep1:'a->zfset) (rep2:'b->zfset).
      IsRep rep1
      ==>
      IsRep rep2
      ==>
      !f x. (rep1 FUN rep2) f ' (rep1 x) = rep2(f x)``,
   METIS_TAC[IsRep_def,ApRep]);

(*---------------------------------------------------------------------------*)
(* Functional composition of set functions.                                  *)
(*---------------------------------------------------------------------------*)

val ComposeFn_def =
 Define
  `ComposeFn(X,Y,Z) f g =
    Spec
     (X # Z)
     (\s.
       ?x z. (s = Pair x z) /\ ?y. y In Y /\ Pair x y In g /\ Pair y z In f)`;

val Compose_def =
 Define
  `Compose(X,Y,Z) =
    Spec
     (((Y -> Z) # (X -> Y)) # (X -> Z))
     (\s. ?f g h. (s = Pair (Pair f g) h) /\  (h = ComposeFn(X,Y,Z) f g))`;

val ComposeFnType =
 store_thm
  ("ComposeFnType",
   ``!X Y Z f g.
      f In (Y -> Z) /\ g In (X -> Y) ==> ComposeFn(X,Y,Z) f g In (X -> Z)``,
      RW_TAC std_ss [ComposeFn_def,Fn_def,Pfn_def,Pow_def,PairEq,Spec_def,InProdEq]
       THEN METIS_TAC[]);

val ApComposeFn =
 store_thm
  ("ApComposeFn",
   ``!X Y Z f g.
      f In (Y -> Z) /\ g In (X -> Y)
      ==>
      !x. x In X ==> (ComposeFn(X,Y,Z) f g ' x = f ' (g ' x))``,
      RW_TAC std_ss
       [Extension_ax,ComposeFn_def,Fn_def,Pfn_def,ComposeFnType,ApFn,InProdEq,
        Spec_def,Apply_def,PairEq,Pow_def]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [GSYM Extension_ax]
       THENL
        [SELECT_ELIM_TAC
          THEN RW_TAC std_ss []
          THENL
           [SELECT_ELIM_TAC
             THEN RW_TAC std_ss []
             THENL
              [ASSUM_LIST(UNDISCH_TAC o concl o el 1)
                THEN SELECT_ELIM_TAC
                THEN METIS_TAC[],
               ASSUM_LIST(UNDISCH_TAC o concl o el 2)
                THEN SELECT_ELIM_TAC
                THEN METIS_TAC[]],
            ASSUM_LIST(UNDISCH_TAC o concl o el 1)
             THEN SELECT_ELIM_TAC
             THEN RW_TAC std_ss []
             THENL
              [METIS_TAC[],
               ASSUM_LIST(UNDISCH_TAC o concl o el 3)
                THEN SELECT_ELIM_TAC
                THEN RW_TAC std_ss []
                THEN METIS_TAC[PairEq]]],
         SELECT_ELIM_TAC
          THEN RW_TAC std_ss []
          THENL
           [ASSUM_LIST(UNDISCH_TAC o concl o el 1)
             THEN SELECT_ELIM_TAC
             THEN RW_TAC std_ss []
             THENL
              [SELECT_ELIM_TAC
                THEN METIS_TAC[],
               ASSUM_LIST(UNDISCH_TAC o concl o el 2)
                THEN SELECT_ELIM_TAC
                THEN METIS_TAC[]],
            ASSUM_LIST(UNDISCH_TAC o concl o el 6)
             THEN SELECT_ELIM_TAC
             THEN FULL_SIMP_TAC std_ss [PairEq]
             THEN RW_TAC std_ss []
             THENL
              [SELECT_ELIM_TAC
                THEN RW_TAC std_ss []
                THEN METIS_TAC[],
               ASSUM_LIST(UNDISCH_TAC o concl o el 2)
                THEN SELECT_ELIM_TAC
                THEN RW_TAC std_ss []
                THEN METIS_TAC[]]]]);

val ComposeFnAssoc =
 store_thm
  ("ComposeFnAssoc",
   ``!X Y Z W f g.
      f In (X -> Y) /\ g In (Y -> Z) /\ h In (Z -> W)
      ==>
      (ComposeFn(X,Z,W) h (ComposeFn(X,Y,Z) g f) =
       ComposeFn(X,Y,W) (ComposeFn(Y,Z,W) h g) f)``,
   RW_TAC std_ss []
    THEN `ComposeFn(X,Y,Z) g f In (X -> Z)` by METIS_TAC [ComposeFnType]
    THEN `ComposeFn(X,Z,W) h (ComposeFn(X,Y,Z) g f) In (X -> W)` by METIS_TAC [ComposeFnType]
    THEN `ComposeFn(Y,Z,W) h g In (Y -> W)` by METIS_TAC [ComposeFnType]
    THEN `ComposeFn(X,Y,W) (ComposeFn(Y,Z,W) h g) f In (X -> W)` by METIS_TAC [ComposeFnType]
    THEN `(ComposeFn (X,Z,W) h (ComposeFn (X,Y,Z) g f) =
           ComposeFn (X,Y,W) (ComposeFn (Y,Z,W) h g) f) =
          !x. x In X ==> (ComposeFn (X,Z,W) h (ComposeFn (X,Y,Z) g f) ' x =
                           ComposeFn (X,Y,W) (ComposeFn (Y,Z,W) h g) f ' x)`
          by METIS_TAC[ExtFn]
    THEN RW_TAC std_ss []
    THEN `f ' x In Y` by METIS_TAC[InFn]
    THEN RW_TAC std_ss [ApComposeFn]);

val FnType =
 store_thm
  ("FnType",
   ``!f X Y.
      (!x. x In X ==> f x In Y)
      ==>
      Spec (X # Y) (\s. ?x. s = Pair x (f x)) In (X -> Y)``,
   RW_TAC std_ss [Pfn_def,Fn_def,Pow_def,Spec_def,InProdEq,PairEq]);

(*---------------------------------------------------------------------------*)
(* Correspondence between logical functions and their graphs.                *)
(*---------------------------------------------------------------------------*)

val Graph_def =
 Define
  `Graph (X,Y) f = Spec (X # Y) (\s. ?x. (s = Pair x (f x)))`;

val HasFnType_def =
 Define
  `HasFnType f X Y = !x. x In X ==> (f x In Y)`;

val GraphAp =
 store_thm
  ("GraphAp",
   ``!X Y f x. HasFnType f X Y /\ x In X ==> (Graph(X,Y) f ' x = f x)``,
   RW_TAC std_ss [HasFnType_def,Graph_def]
    THEN IMP_RES_TAC FnType
    THEN `!y. (Spec (X # Y) (\s. ?x. s = Pair x (f x)) ' x = y) <=>
              Pair x y In Spec (X # Y) (\s. ?x. s = Pair x (f x))`
          by METIS_TAC[ApFn]
    THEN RW_TAC std_ss [InProdEq,Spec_def,PairEq]);

val PairFn =
 store_thm
  ("PairFn",
   ``!f X Y Z.
      (!x y. x In X /\ y In Y ==> f x y In Z) =
      (!xy. xy In (X # Y) ==> f(Fst xy)(Snd xy) In Z)``,
   METIS_TAC[FstType,SndType,InProd,Fst,Snd]);

val PairedFnType =
 store_thm
  ("PairedFnType",
   ``!f X Y Z.
      (!x y. x In X /\ y In Y ==> f x y In Z)
      ==>
      Spec ((X # Y) # Z) (\s. ?x y. (s = Pair (Pair x y) (f x y))) In ((X # Y) -> Z)``,
   RW_TAC std_ss [Pfn_def,Fn_def,Pow_def,Spec_def,InProdEq,PairEq]
    THEN FULL_SIMP_TAC std_ss [PairEq]);

val ComposeType =
 store_thm
  ("ComposeType",
   ``!X Y Z. Compose(X,Y,Z) In (((Y -> Z) # (X -> Y)) -> (X -> Z))``,
   RW_TAC std_ss [Compose_def]
    THEN METIS_TAC[PairedFnType,ComposeFnType]);

val ComposeComposeFn =
 store_thm
  ("ComposeComposeFn",
   ``!X Y Z f g.
      g In (X->Y) /\ f In (Y->Z)
      ==>
      (Compose(X,Y,Z) ' (Pair f g) = ComposeFn(X,Y,Z) f g)``,
   RW_TAC std_ss []
    THEN `ComposeFn(X,Y,Z) f g In (X -> Z)` by METIS_TAC[ComposeFnType]
    THEN `Pair f g In ((Y -> Z) # (X -> Y))` by METIS_TAC[ComposeType,ApFn,InProd]
    THEN `Compose (X,Y,Z) In (((Y -> Z) # X -> Y) -> (X -> Z))` by METIS_TAC[ComposeType]
    THEN `!y. (Compose (X,Y,Z) ' Pair f g = y) <=> Pair (Pair f g) y In Compose (X,Y,Z)`
          by METIS_TAC[ApFn]
    THEN RW_TAC std_ss [Compose_def,Spec_def,InProdEq,PairEq]);

(*---------------------------------------------------------------------------*)
(* Identity set function.                                                    *)
(*---------------------------------------------------------------------------*)

val IdFn_def =
 Define
  `IdFn X = Spec (X # X) (\s. ?x. s = Pair x x)`;

val IdFnPfnType =
 store_thm
  ("IdFnPfnType",
   ``!X. IdFn X In Pfn X X``,
   RW_TAC std_ss [Pfn_def,IdFn_def,PairEq,Pow_def,InProdEq,Spec_def]);

val IdFnType =
 store_thm
  ("IdFnType",
   ``!X. IdFn X In (X -> X)``,
   RW_TAC std_ss [IdFn_def,Fn_def,Pfn_def,PairEq,Pow_def,InProdEq,Spec_def]);

val IdFnApLemma =
 store_thm
  ("IdFnApLemma",
   ``!x X. x In X ==> (Pair x x In IdFn X)``,
   RW_TAC std_ss [IdFn_def,Fn_def,Pfn_def,PairEq,Pow_def,InProdEq,Spec_def]);

val IdFnAp =
 store_thm
  ("IdFnAp",
   ``!X x. x In X ==> (IdFn X ' x = x)``,
   METIS_TAC[IdFnApLemma,IdFnPfnType,ApPfn]);

val ComposeFnId1 = Q.store_thm(
"ComposeFnId1",
`!f X Y Z. (Y = X) /\ f In (Y -> Z) ==> (ComposeFn (X,Y,Z) f (IdFn Y) = f)`,
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Z`] >>
qspec_then `X` assume_tac IdFnType >>
conj_tac >- srw_tac [][ComposeFnType] >>
qspecl_then [`X`,`X`,`Z`,`f`,`IdFn X`] mp_tac ApComposeFn >>
srw_tac [][] >>
metis_tac [IdFnAp,InFn])

val ComposeFnId2 = Q.store_thm(
"ComposeFnId2",
`!f X Y Z. (Y = Z) /\ f In (X -> Y) ==> (ComposeFn (X,Y,Z) (IdFn Y) f = f)`,
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Y`] >>
qspec_then `Y` assume_tac IdFnType >>
conj_tac >- srw_tac [][ComposeFnType] >>
qspecl_then [`X`,`Y`,`Y`,`IdFn Y`,`f`] mp_tac ApComposeFn >>
srw_tac [][] >>
match_mp_tac IdFnAp >>
match_mp_tac InFn >>
qexists_tac `X` >> srw_tac [][])

val GraphFn_def =
 Define
  `GraphFn X f = Spec (X # Image f X) (\s. ?x. s = Pair x (f x))`;

val GraphFnImageType =
 store_thm
  ("GraphFnImageType",
   ``!X f. GraphFn X f In (X -> Image f X)``,
   RW_TAC std_ss [GraphFn_def,Fn_def,Pfn_def,Pow_def,Spec_def,InProdEq,PairEq,Image_def]
    THEN METIS_TAC[]);

val HasFnTypeImageSubset =
 store_thm
  ("HasFnTypeImageSubset",
   ``!f X Y. HasFnType f X Y ==> (Image f X Subset Y)``,
   METIS_TAC[HasFnType_def,Image_def,Subset_def]);

val GraphFnGraph =
 store_thm
  ("GraphFnGraph",
   ``!f X Y. HasFnType f X Y ==> (GraphFn X f Subset Graph(X,Y)f)``,
   RW_TAC std_ss [HasFnType_def,Image_def,Subset_def,GraphFn_def,Graph_def,Spec_def,InProdEq]
    THEN FULL_SIMP_TAC std_ss [PairEq]);

val GraphFnType =
 store_thm
  ("GraphFnType",
   ``!f X Y. HasFnType f X Y ==> GraphFn X f In (X -> Y)``,
   RW_TAC std_ss
    [HasFnType_def,Image_def,Subset_def,GraphFn_def,Graph_def,
     Spec_def,InProdEq,Fn_def,Pfn_def,Pow_def,PairEq]
    THEN FULL_SIMP_TAC std_ss [PairEq]
    THEN METIS_TAC[]);

(*---------------------------------------------------------------------------*)
(* GraphFnTypeCor =                                                          *)
(* |- !f X Y. (!x. x In X ==> (f x) In Y) ==> (GraphFn X f) In (X -> Y)      *)
(*---------------------------------------------------------------------------*)
val GraphFnTypeCor =
 save_thm
  ("GraphFnTypeCor",
   REWRITE_RULE[HasFnType_def]GraphFnType);

val GraphGraphFn =
 store_thm
  ("GraphGraphFn",
   ``!f X. GraphFn X f = Graph(X, Image f X) f``,
  REWRITE_TAC[GraphFn_def,Graph_def]);

val HasFnTypeImage =
 store_thm
  ("HasFnTypeImage",
   ``!f X. HasFnType f X (Image f X)``,
   METIS_TAC[HasFnType_def,Image_def]);

val GraphFnAp =
 store_thm
  ("GraphFnAp",
   ``!X f x. x In X ==> (GraphFn X f ' x = f x)``,
   METIS_TAC[GraphGraphFn,HasFnTypeImage,GraphAp]);

val IdFn_eq_GraphFnI = Q.store_thm(
"IdFn_eq_GraphFnI",
`∀x. IdFn x = GraphFn x I`,
srw_tac [][] >> match_mp_tac FnEqThm >>
map_every qexists_tac [`x`,`x`] >>
srw_tac [][IdFnType] >- (
  match_mp_tac GraphFnType >>
  srw_tac [][HasFnType_def] ) >>
srw_tac [][IdFnAp,GraphFnAp]);

val GraphFnExt = Q.store_thm(
"GraphFnExt",
`∀X f Y g. (X = Y) ∧ (∀x. x In X ⇒ (f x = g x)) ⇒ (GraphFn X f = GraphFn Y g)`,
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Image g X`] >>
srw_tac [][GraphFnAp] >>
match_mp_tac GraphFnType >>
srw_tac [][HasFnType_def] >>
metis_tac [Image_def]);

val ComposeGraphFns = Q.store_thm(
"ComposeGraphFns",
`∀X Y Z f g. HasFnType f X Y ∧ HasFnType g Y Z ⇒
  (ComposeFn (X,Y,Z) (GraphFn Y g) (GraphFn X f) = GraphFn X (g o f))`,
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Z`] >>
srw_tac [][GraphFnType,ComposeFnType,ApComposeFn,GraphFnAp] >- (
  match_mp_tac GraphFnType >>
  fsrw_tac [][HasFnType_def] ) >>
match_mp_tac GraphFnAp >>
fsrw_tac [][HasFnType_def]);

(*---------------------------------------------------------------------------*)
(* Restrictions of functions and binary operators to subtypes.               *)
(*---------------------------------------------------------------------------*)
val Rs_def =
 Define
  `Rs f X = GraphFn X (Apply f)`;

val Rs2_def =
 Define
  `Rs2 binop X = GraphFn X (\x. GraphFn X (Apply (Apply binop x)))`;

val SubType_def =
 Define
  `SubType X pred = Spec X (\s. pred ' s = True)`;

val SubType1Lemma =
 store_thm
  ("SubType1Lemma",
   ``!X f p.
      f In (X ->X)
      ==>
      p In (X -> Bool)
      ==>
      (!x. x In X ==> (p ' x = True) ==> (p ' (f ' x) = True))
      ==>
      HasFnType
       (Apply f)
       (Spec X (\s. p ' s = True)) (Spec X (\s. p ' s = True))``,
   RW_TAC std_ss [SubType_def,HasFnType_def,Spec_def]
    THEN METIS_TAC[InFn]);

val SubType1 =
 store_thm
  ("SubType1",
   ``!X f p.
      f In (X ->X)
      ==>
      p In (X -> Bool)
      ==>
      (!x. x In X ==> (p ' x = True) ==> (p ' (f ' x) = True))
      ==>
      Rs f (SubType X p) In (SubType X p -> SubType X p)``,
   METIS_TAC[Rs_def,SubType_def,HasFnType_def,Spec_def,SubType1Lemma,GraphFnType]);

val SubType2Lemma1 =
 store_thm
  ("SubType2Lemma1",
   ``!X binop p.
      binop In (X -> (X -> X) )
      ==>
      p In (X -> Bool)
      ==>
      (!x y.
         x In X ==>
         y In X ==>
         (p ' x = True) ==>
         (p ' y = True) ==>
         (p ' ((binop ' x) ' y) = True))
      ==>
      x In Spec X (\s. p ' s = True)
      ==>
      HasFnType
       (Apply(binop ' x))
       (Spec X (\s. p ' s = True))
       (Spec X (\s. p ' s = True))``,
   RW_TAC std_ss [SubType_def,HasFnType_def,Spec_def]
    THEN METIS_TAC[InFn]);

val SubType2Lemma2 =
 store_thm
  ("SubType2Lemma2",
   ``!X binop p.
      binop In (X -> (X -> X) )
      ==>
      p In (X -> Bool)
      ==>
      (!x y.
        x In X ==>
        y In X ==> (p ' x = True) ==> (p ' y = True) ==> (p ' ((binop ' x) ' y) = True))
      ==>
      HasFnType
       (\x. GraphFn (Spec X (\s. p ' s = True)) (Apply(binop ' x)))
       (Spec X (\s. p ' s = True))
       ((Spec X (\s. p ' s = True)) -> (Spec X (\s. p ' s = True)))``,
   RW_TAC std_ss [SubType_def,HasFnType_def]
    THEN METIS_TAC[SubType2Lemma1,GraphFnType]);

val SubType2 =
 store_thm
  ("SubType2",
   ``!X binop p.
      binop In (X -> (X -> X) )
      ==>
      p In (X -> Bool)
      ==>
      (!x y.
        x In X ==>
        y In X ==> (p ' x = True) ==> (p ' y = True) ==> (p ' ((binop ' x) ' y) = True))
      ==>
      Rs2 binop (SubType X p) In (SubType X p -> (SubType X p -> SubType X p))``,
   RW_TAC std_ss [Rs2_def,SubType_def,HasFnType_def,Spec_def]
    THEN METIS_TAC[SubType2Lemma2,GraphFnType]);

(*---------------------------------------------------------------------------*)
(* The equality function on a set.                                           *)
(*---------------------------------------------------------------------------*)
val Eq_def =
 Define
  `Eq X = GraphFn X (\x. GraphFn X (\y. bool2Bool(x = y)))`;

val EqAp =
 store_thm
  ("EqAp",
   ``!X x y. x In X ==> y In X ==> (((Eq X ' x) ' y) = bool2Bool(x = y))``,
   RW_TAC std_ss [Eq_def,GraphFnAp]);

val ApEq =
 store_thm
  ("ApEq",
   ``!X x y. x In X ==> y In X ==> ((x = y) = (((Eq X ' x) ' y) = True))``,
   RW_TAC std_ss [Eq_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]);

(*---------------------------------------------------------------------------*)
(* Boolean operations as sets.                                               *)
(*---------------------------------------------------------------------------*)
val Imp_def =
 Define
  `Imp = GraphFn
          Bool
          (\x. GraphFn Bool (\y. bool2Bool((x = True) ==> (y = True))))`;

val ImpAp =
 store_thm
  ("ImpAp",
   ``!x y. x In Bool
           ==>
           y In Bool
           ==>
           (((Imp ' x) ' y) = bool2Bool((x=True) ==> (y=True)))``,
   RW_TAC std_ss [Imp_def,GraphFnAp]);

val ApImp =
 store_thm
  ("ApImp",
   ``!x y. x In Bool
           ==>
           y In Bool
           ==>
           (((x=True) ==> (y=True)) = (((Imp ' x) ' y) = True))``,
   RW_TAC std_ss [Imp_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]);

val And_def =
 Define
  `And = GraphFn
          Bool
          (\x. GraphFn Bool (\y. bool2Bool((x = True) /\ (y = True))))`;

val AndAp =
 store_thm
  ("AndAp",
   ``!x y. x In Bool
           ==>
           y In Bool
           ==>
           (((And ' x) ' y) = bool2Bool((x=True) /\ (y=True)))``,
   RW_TAC std_ss [And_def,GraphFnAp]);

val ApAnd =
 store_thm
  ("ApAnd",
   ``!x y. x In Bool
           ==>
           y In Bool
           ==>
           (((x=True) /\ (y=True)) = (((And ' x) ' y) = True))``,
   RW_TAC std_ss [And_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]);

val Or_def =
 Define
  `Or = GraphFn
         Bool
         (\x. GraphFn Bool (\y. bool2Bool((x = True) \/ (y = True))))`;

val OrAp =
 store_thm
  ("OrAp",
   ``!x y. x In Bool
           ==>
           y In Bool
           ==>
           (((Or ' x) ' y) = bool2Bool((x=True) \/ (y=True)))``,
   RW_TAC std_ss [Or_def,GraphFnAp]);

val ApOr =
 store_thm
  ("ApOr",
   ``!x y. x In Bool
           ==>
           y In Bool
           ==>
           (((x=True) \/ (y=True)) = (((Or ' x) ' y) = True))``,
   RW_TAC std_ss [Or_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]);

val Not_def =
 Define
  `Not = GraphFn Bool (\x. bool2Bool(~(x = True)))`;

val NotAp =
 store_thm
  ("NotAp",
   ``!x. x In Bool ==> ((Not ' x) = bool2Bool(~(x = True)))``,
   RW_TAC std_ss [Not_def,GraphFnAp]);

val ApNot =
 store_thm
  ("ApNot",
   ``!x. x In Bool ==> ((~(x = True)) = ((Not ' x) = True))``,
   RW_TAC std_ss [Not_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]);


(*---------------------------------------------------------------------------*)
(* Quantifiers as sets.                                                      *)
(*---------------------------------------------------------------------------*)
val Forall_def =
 Define
  `Forall X =
    GraphFn (X -> Bool) (\f. bool2Bool(!x. x In X ==> (f ' x = True)))`;

val ForallAp =
 store_thm
  ("ForallAp",
   ``!f X. f In (X -> Bool)
           ==>
           ((Forall X ' f) = bool2Bool !x. x In X ==> (f ' x = True))``,
   RW_TAC std_ss [Forall_def,GraphFnAp]);

val ApForall =
 store_thm
  ("ApForall",
   ``!f X. f In (X -> Bool)
           ==>
           ((!x. x In X ==> (f ' x = True)) = ((Forall X ' f) = True))``,
   RW_TAC std_ss [Forall_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]);

val Exists_def =
 Define
  `Exists X =
    GraphFn (X -> Bool) (\f. bool2Bool(?x. x In X /\ (f ' x = True)))`;

val ExistsAp =
 store_thm
  ("ExistsAp",
   ``!f X. f In (X -> Bool)
           ==>
           ((Exists X ' f) = bool2Bool ?x. x In X /\ (f ' x = True))``,
   RW_TAC std_ss [Exists_def,GraphFnAp]);

val ApExists =
 store_thm
  ("ApExists",
   ``!f X. f In (X -> Bool)
           ==>
           ((?x. x In X /\ (f ' x = True)) = ((Exists X ' f) = True))``,
   RW_TAC std_ss [Exists_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]);

val Choose_def =
 Define
  `Choose X = GraphFn (X -> Bool) (\f. @x. x In X /\ (f ' x = True))`;

val ChooseAp =
 store_thm
  ("ChooseAp",
   ``!f X. f In (X -> Bool)
           ==>
           (Choose X ' f = @x. x In X /\ (f ' x = True))``,
   RW_TAC std_ss [Choose_def,GraphFnAp]);

val ApChoose =
 store_thm
  ("ApChoose",
   ``!f X. f In (X -> Bool)
           ==>
           ((@x. x In X /\ (f ' x = True)) = Choose X ' f)``,
   RW_TAC std_ss [Choose_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]);

val _ = export_theory();
