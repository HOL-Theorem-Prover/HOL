
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

Theory zfset
Ancestors
  zfset_axioms pred_set pair combin
Libs
  pred_setLib pairLib

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)


val _ = ParseExtras.temp_loose_equality()

(*---------------------------------------------------------------------------*)
(* Hack to hide constant ``W``, where: |- W = (\f x. f x x)                  *)
(*---------------------------------------------------------------------------*)
val _ = hide "W";

Theorem ImageId:
     !s. Image (\x. x) s = s
Proof
   RW_TAC std_ss [Extension_ax,Image_def]
QED

(*---------------------------------------------------------------------------*)
(* The Axiom of Choice                                                       *)
(*---------------------------------------------------------------------------*)
Theorem Choice:
    ?f. !s. ~(s = Empty) ==> f s In s
Proof
  Q.EXISTS_TAC `\s.@x. x In s`
   THEN BETA_TAC
   THEN REWRITE_TAC[GSYM NotEmpty]
   THEN REPEAT GEN_TAC
   THEN DISCH_TAC
   THEN POP_ASSUM(ACCEPT_TAC o SELECT_RULE)
QED

(*---------------------------------------------------------------------------*)
(* Definition of an inhabited (i.e. non-empty) set.                          *)
(*---------------------------------------------------------------------------*)
Definition Inhab_def:
   Inhab X = ?x. x In X
End

(*---------------------------------------------------------------------------*)
(* Singleton = |- !x y. y In (Sing x) = (y = x)                              *)
(*---------------------------------------------------------------------------*)
Definition SetCons_def:
   SetCons x s = Singleton x U s
End

val _ = overload_on("EMPTY", ``Empty``);
val _ = overload_on("INSERT",``SetCons``);

Theorem InSetCons:
     !x s t. x In (SetCons s t) = ((x = s) \/ x In t)
Proof
   METIS_TAC[SetCons_def,Extension_ax,U_def,Singleton_def]
QED

Theorem InSing:
     !x y. x In {y} = (x = y)
Proof
   METIS_TAC[Extension_ax,U_def,Singleton_def,InSetCons,Empty_def]
QED

Theorem SingNotEmpty:
     !x. ~({x} = {}) /\ ~({} = {x})
Proof
   METIS_TAC[Extension_ax,InSing,Empty_def]
QED

Theorem InDouble:
     !x x1 x2. x In {x1;x2} = ((x = x1) \/ (x = x2))
Proof
   METIS_TAC[Extension_ax,U_def,Singleton_def,InSetCons,Empty_def]
QED

Theorem DoubleNotEmpty:
     !x y. ~({x;y} = {}) /\ ~({} = {x;y})
Proof
   METIS_TAC[Extension_ax,InDouble,Empty_def]
QED

Theorem SingEq:
     !x1 x2. ({x1} = {x2}) = (x1 = x2)
Proof
   METIS_TAC[Extension_ax,InSing]
QED

Theorem NotInSelf:
     !x. ~(x In x)
Proof
   METIS_TAC[SingNotEmpty,InSing,Foundation_ax,Intersect_def,Empty_def]
QED

Theorem InRefl:
     !x y. x In y ==> ~(y In x)
Proof
   METIS_TAC[Foundation_ax,InDouble,DoubleNotEmpty,Intersect_def,Empty_def]
QED

Theorem DoubleRefl:
     !x. {x;x} = {x}
Proof
  METIS_TAC[Extension_ax,InSing,InDouble]
QED

Theorem SingDoubleEq:
     !x x1 x2. ({x} = {x1;x2}) = (x = x1) /\ (x = x2)
Proof
   METIS_TAC[Extension_ax,InSing,InDouble]
QED

Theorem DoubleCancel:
     !x x1 x2. ({x;x1} = {x;x2}) = (x1 = x2)
Proof
   METIS_TAC[Extension_ax,InDouble]
QED

Definition Pair_def:
   Pair x y = {{x}; {x;y}}
End

Theorem PairEqLemma1:
     !x x1 x2. ~(x1 = x2) ==> ~({x} = {x1;x2})
Proof
   METIS_TAC[Pair_def,Extension_ax,InSing,InDouble]
QED

Theorem PairEq:
     !x1 x2 y1 y2. (Pair x1 y1 = Pair x2 y2) = (x1 = x2) /\ (y1 = y2)
Proof
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
      THEN METIS_TAC[DoubleRefl,SingDoubleEq,SingEq,InSing,InDouble]]
QED

Definition Fst_def:
   Fst p = @x. ?y. p = Pair x y
End

Definition Snd_def:
   Snd p = @y. ?x. p = Pair x y
End

val FstLemma =
 prove
  (``!x. (@x'. ?y'. Pair x y = Pair x' y') = x``,
   RW_TAC std_ss [PairEq]);

Theorem Fst:
     !x y. Fst(Pair x y) = x
Proof
   METIS_TAC[Fst_def,FstLemma]
QED

val SndLemma =
 prove
  (``!y. (@y'. ?x'. Pair x y = Pair x' y') = y``,
   RW_TAC std_ss [PairEq]);

Theorem Snd:
     !x y. Snd(Pair x y) = y
Proof
   METIS_TAC[Snd_def,SndLemma]
QED

Theorem SingletonThm:
     !x. Singleton x = {x}
Proof
   METIS_TAC[Extension_ax,InSing,Singleton_def]
QED

Theorem NotSuc:
     !x. ~(Suc x = {}) /\ ~({} = Suc x)
Proof
  METIS_TAC[SingletonThm,Extension_ax,U_def,InSing,Empty_def,Suc_def]
QED

Theorem InvSucEq:
     !x y. (Suc x = Suc y) = (x = y)
Proof
  RW_TAC std_ss [Suc_def,Extension_ax,U_def,InSing,Singleton_def]
   THEN METIS_TAC[InRefl]
QED

(*---------------------------------------------------------------------------*)
(* InfSet = |- {} In InfSet /\ (!x. x In InfSet ==> (Suc x) In InfSet)       *)
(*---------------------------------------------------------------------------*)
val InfSet_def = new_specification("InfSet_def", ["InfSet"], Infinity_ax);

(*---------------------------------------------------------------------------*)
(* |- SET_TYPE s (rep:ty->zfset)                                             *)
(*                                                                           *)
(* If s is in bijection with ty.                                             *)
(*---------------------------------------------------------------------------*)
Definition SET_TYPE_def:
   SET_TYPE s (rep:'a->zfset) = TYPE_DEFINITION (\x. x In s) rep
End

Theorem SET_TYPE_In:
     !s (rep:'a->zfset). SET_TYPE s rep ==> !x. rep x In s
Proof
   RW_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION]
    THEN POP_ASSUM(ASSUME_TAC o SPEC ``(rep:'a->zfset)x``)
    THEN METIS_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* Truth values.                                                             *)
(*---------------------------------------------------------------------------*)

Definition False_def:
   False = {}
End

Definition True_def:
   True = {{}}
End

Definition Bool_def:
   Bool = {False;True}
End

Theorem Bool_CLAUSES:
     ~(True = False) /\ ~(False = True)
Proof
  REWRITE_TAC[True_def,False_def,SingNotEmpty]
QED

Theorem InhabBool:
     Inhab Bool
Proof
   METIS_TAC[Inhab_def,Bool_def,InDouble]
QED

Definition bool2Bool_def:
   bool2Bool b = if b then True else False
End

Theorem bool2BoolEqTrue:
     !b. (bool2Bool b = True) = b
Proof
   METIS_TAC[bool2Bool_def,Bool_CLAUSES]
QED

Theorem bool2BoolEqFalse:
     !b. (bool2Bool b = False) = ~b
Proof
   METIS_TAC[bool2Bool_def,Bool_CLAUSES]
QED

Theorem bool2BoolEq:
     !b1 b2. (bool2Bool b1 = bool2Bool b2) = (b1 = b2)
Proof
   METIS_TAC[bool2Bool_def,Bool_CLAUSES]
QED

Theorem TrueInBool:
     True In Bool
Proof
  REWRITE_TAC[True_def,Bool_def,InSetCons]
QED

Theorem FalseInBool:
     False In Bool
Proof
  REWRITE_TAC[True_def,Bool_def,InSetCons]
QED

Theorem boolBool:
     SET_TYPE Bool bool2Bool
Proof
   RW_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION,bool2BoolEq,Bool_def,bool2Bool_def,InDouble]
    THEN METIS_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* Proof that Von Neumann numbers are isomorphic to HOL's numbers.           *)
(*---------------------------------------------------------------------------*)
Definition num2Num_def:
   (num2Num 0 = {}) /\
   (num2Num(SUC n) = Suc(num2Num n))
End

Theorem num2NumInf:
     !n. num2Num n In InfSet
Proof
  Induct
   THEN RW_TAC std_ss [num2Num_def,InfSet_def]
QED

(*---------------------------------------------------------------------------*)
(* Von Neumann numbers.                                                      *)
(*---------------------------------------------------------------------------*)

Definition Num_def:
   Num = Spec InfSet (\s. ?n. s = num2Num n)
End

Theorem InhabNum:
     Inhab Num
Proof
   RW_TAC std_ss [Inhab_def]
    THEN EXISTS_TAC ``num2Num 0``
    THEN RW_TAC std_ss [Num_def,Spec_def]
    THEN METIS_TAC[num2NumInf]
QED

Theorem num2NumSucNotEmpty:
     !n.  num2Num 0 <> num2Num (SUC n)
Proof
   Induct
    THEN RW_TAC std_ss [NotSuc,num2Num_def,InvSucEq]
QED

Theorem num2NumInfset:
     !n. num2Num n In InfSet
Proof
   Induct
    THEN RW_TAC std_ss [NotSuc,num2Num_def,InvSucEq,InfSet_def]
QED

Theorem numNum:
     SET_TYPE Num num2Num
Proof
   SIMP_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION]
    THEN CONJ_TAC
    THENL
     [Induct THEN Induct
       THEN RW_TAC std_ss [NotSuc,num2Num_def,InvSucEq],
      RW_TAC std_ss [Num_def,Spec_def]
       THEN METIS_TAC[num2NumInfset]]
QED

(*---------------------------------------------------------------------------*)
(* Representation of product types.                                          *)
(*---------------------------------------------------------------------------*)

Definition PROD_def:
   $PROD (rep1:'a->zfset) (rep2:'b->zfset) = \(x1,x2). Pair(rep1 x1)(rep2 x2)
End

val _ = set_fixity "PROD" (Infixr 400); (* Precedence may need adjusting *)

Theorem PairPROD:
     !(rep1:'a->zfset) (rep2:'b->zfset) x1 x2.
    Pair (rep1 x1) (rep2 x2) = (rep1 PROD rep2)(x1,x2)
Proof
  RW_TAC std_ss [PROD_def]
QED

(*---------------------------------------------------------------------------*)
(* Cartesian product of sets.                                                *)
(*---------------------------------------------------------------------------*)

Definition Prod_def:
   $Prod s1 s2 =
     Spec
      (Pow(Pow(s1 U s2)))
      (\s. ?x1 x2. (s = Pair x1 x2) /\ x1 In s1 /\ x2 In s2)
End

val _ = set_fixity "#" (Infixr 400); (* Precedence may need adjusting *)

val _ = overload_on("#", ``$Prod``);

Theorem PairBound:
     !x1 x2 s1 s2. x1 In s1 /\ x2 In s2 ==> Pair x1 x2 In Pow(Pow(s1 U s2))
Proof
   RW_TAC std_ss [Pair_def,Pow_def,U_def,InDouble,InSing]
    THEN FULL_SIMP_TAC std_ss [InSing,InDouble]
QED

Theorem InProd:
     !x1 x2 s1 s2. x1 In s1 /\ x2 In s2 = Pair x1 x2 In (s1 # s2)
Proof
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss[Pair_def,InSing,InDouble]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss[Pair_def,InSing,InDouble]
    THEN RW_TAC std_ss []
QED

Theorem InProdEq:
     !z s1 s2 x1 x2.
       z In (s1 # s2) = ?x1 x2. x1 In s1 /\ x2 In s2 /\ (z = Pair x1 x2)
Proof
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss[Pair_def,InSing,InDouble]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss[Pair_def,InSing,InDouble]
    THEN RW_TAC std_ss []
    THEN METIS_TAC[]
QED

Theorem FstType:
     !p X Y. p In (X # Y) ==> (Fst p) In X
Proof
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN RW_TAC std_ss [Fst]
QED

Theorem SndType:
     !p X Y. p In (X # Y) ==> (Snd p) In Y
Proof
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN RW_TAC std_ss [Snd]
QED

Theorem PairIn:
     !p. p In (X # Y) ==> (Pair(Fst p)(Snd p) = p)
Proof
   RW_TAC std_ss [Prod_def,Spec_def,Pow_def,U_def,PairEq]
    THEN RW_TAC std_ss [PairEq,Fst,Snd]
QED

Theorem EmptyProd:
 ∀x. ({} # x = {}) ∧ (x # {} = {})
Proof
srw_tac [][Extension_ax,Empty_def,InProdEq]
QED
val _ = export_rewrites["EmptyProd"];

Theorem ProdEmpty:
 ∀x y. (x # y = {}) = ((x = {}) \/ (y = {}))
Proof
srw_tac [][EQ_IMP_THM] >> srw_tac [][] >>
spose_not_then strip_assume_tac >>
fsrw_tac [][GSYM NotEmpty] >>
metis_tac [InProd,Empty_def]
QED

Theorem ProdEq:
 !x1 x2 y1 y2. (x1 # y1 = x2 # y2) = ((x1 # y1 = {}) /\ (x2 # y2 = {})) \/ ((x1 = x2) /\ (y1 = y2))
Proof
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
PROVE_TAC [PairEq]
QED

Theorem ABS_THM:
     !P rep.
      TYPE_DEFINITION P rep
      ==>
      (?abs. (!a. abs(rep a) = a) /\ (!r. P r = (rep(abs r) = r)))
Proof
   METIS_TAC[TYPE_DEFINITION_THM]
QED

Definition Abs_def:
   Abs s (rep:'a->zfset) =
    @abs. (!a. abs(rep a) = a) /\ !r. r In s = (rep(abs r) = r)
End

Theorem Abs:
     !s (rep:'a->zfset).
     SET_TYPE s rep
     ==>
     (!a. Abs s rep(rep a) = a) /\ !r. r In s = (rep(Abs s rep r) = r)
Proof
   RW_TAC std_ss [SET_TYPE_def,Abs_def]
    THEN SELECT_ELIM_TAC
    THEN RW_TAC std_ss []
    THEN IMP_RES_TAC ABS_THM
    THEN FULL_SIMP_TAC std_ss []
    THEN METIS_TAC[]
QED

Theorem AbsOneOne:
     !s (rep:'a->zfset).
      SET_TYPE s rep
      ==>
      !x1 x2.
       x1 In s /\ x2 In s ==> ((Abs s rep x1 = Abs s rep x2) = (x1 = x2))
Proof
   METIS_TAC[Abs]
QED

Definition Num2num_def:
   Num2num = Abs Num num2Num
End

Theorem Num2num_CLAUSES:
     (!a. Num2num(num2Num a) = a) /\
     (!r. r In Num = (num2Num(Num2num r) = r))
Proof
   METIS_TAC[Num2num_def,Abs,numNum]
QED

(*---------------------------------------------------------------------------*)
(* Union of a countable sequence of sets.                                    *)
(*---------------------------------------------------------------------------*)
val _ = new_binder("Us",``:(num -> zfset) -> zfset``);

Definition Us_def:
   $Us s = UU(Image (s o Num2num) Num)
End

Theorem InUs:
     !s x. x In ($Us s) = ?n. x In s n
Proof
   RW_TAC std_ss [Us_def,UU_def,Image_def,o_DEF,Num2num_CLAUSES]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [METIS_TAC[],
      Q.EXISTS_TAC `s n`
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `num2Num n`
       THEN RW_TAC std_ss [Num2num_CLAUSES]]
QED

Theorem UsU:
     !s1 s2. (Us n. s1 n U s2 n) = (Us n. s1 n) U (Us n. s2 n)
Proof
   RW_TAC std_ss [U_def,InUs,Extension_ax]
    THEN METIS_TAC[]
QED

Theorem PROD_REP:
     !s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      SET_TYPE (s1 # s2) (rep1 PROD rep2)
Proof
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
         METIS_TAC[PAIR]]]
QED

(*---------------------------------------------------------------------------*)
(* Set of partial functions (single valued relations) from X to Y            *)
(*---------------------------------------------------------------------------*)
Definition Pfn_def:
   Pfn X Y =
    Spec
     (Pow(X # Y))
     (\r. !x y1 y2. Pair x y1 In r /\ Pair x y2 In r ==> (y1=y2))
End

(*---------------------------------------------------------------------------*)
(* Set of functions from X to Y                                              *)
(*---------------------------------------------------------------------------*)
Definition Fn_def:
   $Fn X Y =
    Spec
     (Pfn X Y)
     (\f. !x. x In X ==> ?y. y In Y /\ Pair x y In f)
End

val _ = set_fixity "->" (Infixr 400); (* Precedence may need adjusting *)
val _ = overload_on("->",``Fn``);

(*---------------------------------------------------------------------------*)
(* Application of a set-funtion to an argument.                              *)
(*---------------------------------------------------------------------------*)
Definition Apply_def:
   Apply s x = @y. Pair x y In s
End

val _ = set_fixity "'" (Infixl 600); (* Precedence may need adjusting *)
val _ = overload_on("'",``Apply``);

Theorem ApUnion:
     !x1 x2 v s.
      ~(x1 = x2) ==> ((s U {Pair x1 v}) ' x2 = s ' x2)
Proof
   RW_TAC std_ss [Apply_def,Pair_def,U_def,InSing,PairEq]
QED

Theorem ApSing:
     !x v. {Pair x v} ' x = v
Proof
   RW_TAC std_ss [Apply_def,Pair_def,U_def,InSing,PairEq]
QED

Theorem ApPfn:
     !f X Y x.
      f In Pfn X Y /\ (?y. Pair x y In f)
      ==>
      !y. (f ' x = y) = Pair x y In f
Proof
   RW_TAC std_ss [Pfn_def,Pow_def,InProdEq,PairEq,Spec_def,Apply_def]
    THEN SELECT_ELIM_TAC
    THEN METIS_TAC[]
QED

Theorem ApFn:
     !f X Y x. f In (X -> Y) /\  x In X ==> !y. (f ' x = y) = Pair x y In f
Proof
   RW_TAC std_ss [Fn_def,Spec_def]
    THEN METIS_TAC[ApPfn]
QED

Theorem InFn:
     !f x X Y. f In (X -> Y) /\ x In X  ==> (f ' x) In Y
Proof
   RW_TAC std_ss []
    THEN `!y. (f ' x = y) <=> Pair x y In f` by METIS_TAC[ApFn ]
    THEN FULL_SIMP_TAC std_ss [Pfn_def,Pow_def,Fn_def,Spec_def,InProdEq]
    THEN METIS_TAC[]
QED

Theorem ExtFn:
     !X Y f g.
      f In (X -> Y) /\ g In (X -> Y)
      ==>
      ((f = g) = (!x. x In X ==> (f ' x = g ' x)))
Proof
   RW_TAC std_ss [ApFn]
    THEN `!x. x In X ==> !y. (f ' x = y) <=> Pair x y In f` by METIS_TAC[ApFn]
    THEN `!x. x In X ==> !y. (g ' x = y) <=> Pair x y In g` by METIS_TAC[ApFn]
    THEN FULL_SIMP_TAC std_ss [Extension_ax,Pow_def,InProdEq,Fn_def,Pfn_def,Spec_def]
    THEN METIS_TAC[Extension_ax]
QED

Theorem FnEqThm:
 !f g X Y. f In (X -> Y) /\ g In (X -> Y) /\ (!x. x In X ==> (f ' x = g ' x))
  ==> (f = g)
Proof
metis_tac [ExtFn]
QED

(*---------------------------------------------------------------------------*)
(* RepSet(f:'a->zfset) =  the image of f as a set in zfset                   *)
(*---------------------------------------------------------------------------*)

Definition RepSet_def:
   RepSet(f:'a->zfset) = @s. !y. y In s = ?x. y = f x
End

Theorem RepSetThm:
     !s (rep:'a->zfset). SET_TYPE s rep ==> (RepSet rep = s)
Proof
   RW_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION,RepSet_def,Extension_ax]
    THEN METIS_TAC[]
QED

Theorem RepSetIn:
     !s (rep:'a->zfset). SET_TYPE s rep ==> !x. rep x In RepSet rep
Proof
   RW_TAC std_ss [SET_TYPE_def,TYPE_DEFINITION,RepSet_def,Extension_ax]
    THEN METIS_TAC[]
QED

Theorem RepSetPROD:
     !(rep1:'a->zfset) (rep2:'b->zfset) s1 s2.
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      (RepSet(rep1 PROD rep2) = s1 # s2)
Proof
   METIS_TAC[PROD_REP,RepSetThm]
QED

Theorem SET_TYPE_PROD:
     !s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
       SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
       ==>
       !p. (rep1 PROD rep2) p In (s1 # s2)
Proof
   METIS_TAC[RepSetPROD,RepSetThm,PROD_REP,SET_TYPE_In]
QED

(*---------------------------------------------------------------------------*)
(* Representation of function types.                                         *)
(*---------------------------------------------------------------------------*)
Definition FUN_def:
   $FUN (rep1:'a->zfset) (rep2:'b->zfset) =
    \f. Spec
         (RepSet rep1 # RepSet rep2)
         (\s. ?x' y'.
               (s = Pair x' y')
               /\
               ?x y. (x' = rep1 x) /\ (y' = rep2 y) /\ (f x = y))
End

val _ = set_fixity "FUN" (Infixr 700); (* Precedence may need adjusting *)

Theorem FUNIn:
     !s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2 ==>
      !f x. Pair (rep1 x) (rep2(f x)) In (rep1 FUN rep2) f
Proof
   RW_TAC std_ss [FUN_def,Spec_def,PairEq,InProdEq]
    THEN METIS_TAC[RepSetIn]
QED

Theorem ONE_ONE_EQ:
     !f:'a->'b. ONE_ONE f = !x1 x2. (f x1 = f x2) = (x1 = x2)
Proof
   METIS_TAC [ONE_ONE_DEF]
QED

Theorem SET_TYPE_ONE_ONE:
     !(rep:'a->zfset) s. SET_TYPE s rep ==> ONE_ONE rep
Proof
   METIS_TAC[SET_TYPE_def,TYPE_DEFINITION,ONE_ONE_DEF]
QED

Theorem FUNSingleValued:
     !(rep1:'a->zfset) (rep2:'b->zfset) f x y1 y2.
      ONE_ONE rep1 /\
      Pair x y1 In (rep1 FUN rep2) f /\ Pair x y2 In (rep1 FUN rep2) f
      ==>
      (y1 = y2)
Proof
   RW_TAC std_ss [FUN_def,ONE_ONE_DEF,PairEq,Spec_def,InProdEq]
    THEN METIS_TAC[]
QED

Theorem FUN_ONE_ONE:
     !(rep1:'a->zfset)(rep2:'b->zfset) s1 s2.
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      !f g. ((rep1 FUN rep2) f = (rep1 FUN rep2) g) = (f = g)
Proof
   METIS_TAC[FUNIn,SET_TYPE_ONE_ONE,ONE_ONE_DEF,FUNSingleValued]
QED

Theorem FUN_REP:
     !s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      SET_TYPE (s1 -> s2) (rep1 FUN rep2)
Proof
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
       THEN METIS_TAC[]]
QED

Theorem RepSetFUN:
     !(rep1:'a->zfset) (rep2:'b->zfset) s1 s2.
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      (RepSet(rep1 FUN rep2) = s1 -> s2)
Proof
   METIS_TAC[RepSetThm,FUN_REP]
QED

Theorem SET_TYPE_FUN:
     !s1 s2 (rep1:'a->zfset) (rep2:'b->zfset).
       SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
       ==>
       !f. (rep1 FUN rep2)f In (s1 -> s2)
Proof
   METIS_TAC[RepSetThm,RepSetFUN,FUN_REP,SET_TYPE_In]
QED

Theorem ApRep:
     !(rep1:'a->zfset) (rep2:'b->zfset) s1 s2 f x.
      SET_TYPE s1 rep1 /\ SET_TYPE s2 rep2
      ==>
      ((rep1 FUN rep2) f ' (rep1 x) = rep2(f x))
Proof
   RW_TAC std_ss []
    THEN IMP_RES_TAC FUNIn
    THEN `?y. (Pair (rep1 x) y) In ((rep1 FUN rep2)(f:'a->'b))` by METIS_TAC[]
    THEN RW_TAC std_ss [Apply_def]
    THEN METIS_TAC[SET_TYPE_ONE_ONE,FUNSingleValued,FUNIn]
QED

Definition IsRep_def:
   IsRep(rep:'a->zfset) = ?s. SET_TYPE s rep
End

Theorem IsRepThm:
     !rep:'a->zfset. IsRep rep ==> !s. SET_TYPE s rep = (RepSet rep = s)
Proof
   METIS_TAC[IsRep_def,RepSetThm]
QED

Theorem IsRep_SET_TYPE:
     !rep:'a->zfset. IsRep rep ==> SET_TYPE (RepSet rep) rep
Proof
   METIS_TAC[IsRepThm]
QED

Theorem IsRep_num2Num:
     IsRep num2Num
Proof
   RW_TAC std_ss[IsRep_def]
    THEN METIS_TAC[numNum]
QED

Theorem IsRep_bool2Bool:
     IsRep bool2Bool
Proof
   METIS_TAC[IsRep_def,boolBool]
QED

Theorem IsRep_PROD:
     !(rep1:'a->zfset) (rep2:'b->zfset).
      IsRep rep1 ==> IsRep rep2 ==> IsRep(rep1 PROD rep2)
Proof
   METIS_TAC[IsRep_def,PROD_REP]
QED

Theorem IsRep_FUN:
     !(rep1:'a->zfset) (rep2:'b->zfset).
      IsRep rep1 ==> IsRep rep2 ==> IsRep(rep1 FUN rep2)
Proof
   METIS_TAC[IsRep_def,FUN_REP]
QED

Theorem ApRepCor:
     !(rep1:'a->zfset) (rep2:'b->zfset).
      IsRep rep1
      ==>
      IsRep rep2
      ==>
      !f x. (rep1 FUN rep2) f ' (rep1 x) = rep2(f x)
Proof
   METIS_TAC[IsRep_def,ApRep]
QED

(*---------------------------------------------------------------------------*)
(* Functional composition of set functions.                                  *)
(*---------------------------------------------------------------------------*)

Definition ComposeFn_def:
   ComposeFn(X,Y,Z) f g =
    Spec
     (X # Z)
     (\s.
       ?x z. (s = Pair x z) /\ ?y. y In Y /\ Pair x y In g /\ Pair y z In f)
End

Definition Compose_def:
   Compose(X,Y,Z) =
    Spec
     (((Y -> Z) # (X -> Y)) # (X -> Z))
     (\s. ?f g h. (s = Pair (Pair f g) h) /\  (h = ComposeFn(X,Y,Z) f g))
End

Theorem ComposeFnType:
     !X Y Z f g.
      f In (Y -> Z) /\ g In (X -> Y) ==> ComposeFn(X,Y,Z) f g In (X -> Z)
Proof
      RW_TAC std_ss [ComposeFn_def,Fn_def,Pfn_def,Pow_def,PairEq,Spec_def,InProdEq]
       THEN METIS_TAC[]
QED

Theorem ApComposeFn:
     !X Y Z f g.
      f In (Y -> Z) /\ g In (X -> Y)
      ==>
      !x. x In X ==> (ComposeFn(X,Y,Z) f g ' x = f ' (g ' x))
Proof
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
                THEN METIS_TAC[]]]]
QED

Theorem ComposeFnAssoc:
     !X Y Z W f g.
      f In (X -> Y) /\ g In (Y -> Z) /\ h In (Z -> W)
      ==>
      (ComposeFn(X,Z,W) h (ComposeFn(X,Y,Z) g f) =
       ComposeFn(X,Y,W) (ComposeFn(Y,Z,W) h g) f)
Proof
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
    THEN RW_TAC std_ss [ApComposeFn]
QED

Theorem FnType:
     !f X Y.
      (!x. x In X ==> f x In Y)
      ==>
      Spec (X # Y) (\s. ?x. s = Pair x (f x)) In (X -> Y)
Proof
   RW_TAC std_ss [Pfn_def,Fn_def,Pow_def,Spec_def,InProdEq,PairEq]
QED

(*---------------------------------------------------------------------------*)
(* Correspondence between logical functions and their graphs.                *)
(*---------------------------------------------------------------------------*)

Definition Graph_def:
   Graph (X,Y) f = Spec (X # Y) (\s. ?x. (s = Pair x (f x)))
End

Definition HasFnType_def:
   HasFnType f X Y = !x. x In X ==> (f x In Y)
End

Theorem GraphAp:
     !X Y f x. HasFnType f X Y /\ x In X ==> (Graph(X,Y) f ' x = f x)
Proof
   RW_TAC std_ss [HasFnType_def,Graph_def]
    THEN IMP_RES_TAC FnType
    THEN `!y. (Spec (X # Y) (\s. ?x. s = Pair x (f x)) ' x = y) <=>
              Pair x y In Spec (X # Y) (\s. ?x. s = Pair x (f x))`
          by METIS_TAC[ApFn]
    THEN RW_TAC std_ss [InProdEq,Spec_def,PairEq]
QED

Theorem PairFn:
     !f X Y Z.
      (!x y. x In X /\ y In Y ==> f x y In Z) =
      (!xy. xy In (X # Y) ==> f(Fst xy)(Snd xy) In Z)
Proof
   METIS_TAC[FstType,SndType,InProd,Fst,Snd]
QED

Theorem PairedFnType:
     !f X Y Z.
      (!x y. x In X /\ y In Y ==> f x y In Z)
      ==>
      Spec ((X # Y) # Z) (\s. ?x y. (s = Pair (Pair x y) (f x y))) In ((X # Y) -> Z)
Proof
   RW_TAC std_ss [Pfn_def,Fn_def,Pow_def,Spec_def,InProdEq,PairEq]
    THEN FULL_SIMP_TAC std_ss [PairEq]
QED

Theorem ComposeType:
     !X Y Z. Compose(X,Y,Z) In (((Y -> Z) # (X -> Y)) -> (X -> Z))
Proof
   RW_TAC std_ss [Compose_def]
    THEN METIS_TAC[PairedFnType,ComposeFnType]
QED

Theorem ComposeComposeFn:
     !X Y Z f g.
      g In (X->Y) /\ f In (Y->Z)
      ==>
      (Compose(X,Y,Z) ' (Pair f g) = ComposeFn(X,Y,Z) f g)
Proof
   RW_TAC std_ss []
    THEN `ComposeFn(X,Y,Z) f g In (X -> Z)` by METIS_TAC[ComposeFnType]
    THEN `Pair f g In ((Y -> Z) # (X -> Y))` by METIS_TAC[ComposeType,ApFn,InProd]
    THEN `Compose (X,Y,Z) In (((Y -> Z) # X -> Y) -> (X -> Z))` by METIS_TAC[ComposeType]
    THEN `!y. (Compose (X,Y,Z) ' Pair f g = y) <=> Pair (Pair f g) y In Compose (X,Y,Z)`
          by METIS_TAC[ApFn]
    THEN RW_TAC std_ss [Compose_def,Spec_def,InProdEq,PairEq]
QED

(*---------------------------------------------------------------------------*)
(* Identity set function.                                                    *)
(*---------------------------------------------------------------------------*)

Definition IdFn_def:
   IdFn X = Spec (X # X) (\s. ?x. s = Pair x x)
End

Theorem IdFnPfnType:
     !X. IdFn X In Pfn X X
Proof
   RW_TAC std_ss [Pfn_def,IdFn_def,PairEq,Pow_def,InProdEq,Spec_def]
QED

Theorem IdFnType:
     !X. IdFn X In (X -> X)
Proof
   RW_TAC std_ss [IdFn_def,Fn_def,Pfn_def,PairEq,Pow_def,InProdEq,Spec_def]
QED

Theorem IdFnApLemma:
     !x X. x In X ==> (Pair x x In IdFn X)
Proof
   RW_TAC std_ss [IdFn_def,Fn_def,Pfn_def,PairEq,Pow_def,InProdEq,Spec_def]
QED

Theorem IdFnAp:
     !X x. x In X ==> (IdFn X ' x = x)
Proof
   METIS_TAC[IdFnApLemma,IdFnPfnType,ApPfn]
QED

Theorem ComposeFnId1:
 !f X Y Z. (Y = X) /\ f In (Y -> Z) ==> (ComposeFn (X,Y,Z) f (IdFn Y) = f)
Proof
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Z`] >>
qspec_then `X` assume_tac IdFnType >>
conj_tac >- srw_tac [][ComposeFnType] >>
qspecl_then [`X`,`X`,`Z`,`f`,`IdFn X`] mp_tac ApComposeFn >>
srw_tac [][] >>
metis_tac [IdFnAp,InFn]
QED

Theorem ComposeFnId2:
 !f X Y Z. (Y = Z) /\ f In (X -> Y) ==> (ComposeFn (X,Y,Z) (IdFn Y) f = f)
Proof
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Y`] >>
qspec_then `Y` assume_tac IdFnType >>
conj_tac >- srw_tac [][ComposeFnType] >>
qspecl_then [`X`,`Y`,`Y`,`IdFn Y`,`f`] mp_tac ApComposeFn >>
srw_tac [][] >>
match_mp_tac IdFnAp >>
match_mp_tac InFn >>
qexists_tac `X` >> srw_tac [][]
QED

Definition GraphFn_def:
   GraphFn X f = Spec (X # Image f X) (\s. ?x. s = Pair x (f x))
End

Theorem GraphFnImageType:
     !X f. GraphFn X f In (X -> Image f X)
Proof
   RW_TAC std_ss [GraphFn_def,Fn_def,Pfn_def,Pow_def,Spec_def,InProdEq,PairEq,Image_def]
    THEN METIS_TAC[]
QED

Theorem HasFnTypeImageSubset:
     !f X Y. HasFnType f X Y ==> (Image f X Subset Y)
Proof
   METIS_TAC[HasFnType_def,Image_def,Subset_def]
QED

Theorem GraphFnGraph:
     !f X Y. HasFnType f X Y ==> (GraphFn X f Subset Graph(X,Y)f)
Proof
   RW_TAC std_ss [HasFnType_def,Image_def,Subset_def,GraphFn_def,Graph_def,Spec_def,InProdEq]
    THEN FULL_SIMP_TAC std_ss [PairEq]
QED

Theorem GraphFnType:
     !f X Y. HasFnType f X Y ==> GraphFn X f In (X -> Y)
Proof
   RW_TAC std_ss
    [HasFnType_def,Image_def,Subset_def,GraphFn_def,Graph_def,
     Spec_def,InProdEq,Fn_def,Pfn_def,Pow_def,PairEq]
    THEN FULL_SIMP_TAC std_ss [PairEq]
    THEN METIS_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* GraphFnTypeCor =                                                          *)
(* |- !f X Y. (!x. x In X ==> (f x) In Y) ==> (GraphFn X f) In (X -> Y)      *)
(*---------------------------------------------------------------------------*)
val GraphFnTypeCor =
 save_thm
  ("GraphFnTypeCor",
   REWRITE_RULE[HasFnType_def]GraphFnType);

Theorem GraphGraphFn:
     !f X. GraphFn X f = Graph(X, Image f X) f
Proof
  REWRITE_TAC[GraphFn_def,Graph_def]
QED

Theorem HasFnTypeImage:
     !f X. HasFnType f X (Image f X)
Proof
   METIS_TAC[HasFnType_def,Image_def]
QED

Theorem GraphFnAp:
     !X f x. x In X ==> (GraphFn X f ' x = f x)
Proof
   METIS_TAC[GraphGraphFn,HasFnTypeImage,GraphAp]
QED

Theorem IdFn_eq_GraphFnI:
 ∀x. IdFn x = GraphFn x I
Proof
srw_tac [][] >> match_mp_tac FnEqThm >>
map_every qexists_tac [`x`,`x`] >>
srw_tac [][IdFnType] >- (
  match_mp_tac GraphFnType >>
  srw_tac [][HasFnType_def] ) >>
srw_tac [][IdFnAp,GraphFnAp]
QED

Theorem GraphFnExt:
 ∀X f Y g. (X = Y) ∧ (∀x. x In X ⇒ (f x = g x)) ⇒ (GraphFn X f = GraphFn Y g)
Proof
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Image g X`] >>
srw_tac [][GraphFnAp] >>
match_mp_tac GraphFnType >>
srw_tac [][HasFnType_def] >>
metis_tac [Image_def]
QED

Theorem ComposeGraphFns:
 ∀X Y Z f g. HasFnType f X Y ∧ HasFnType g Y Z ⇒
  (ComposeFn (X,Y,Z) (GraphFn Y g) (GraphFn X f) = GraphFn X (g o f))
Proof
srw_tac [][] >>
match_mp_tac FnEqThm >>
map_every qexists_tac [`X`,`Z`] >>
srw_tac [][GraphFnType,ComposeFnType,ApComposeFn,GraphFnAp] >- (
  match_mp_tac GraphFnType >>
  fsrw_tac [][HasFnType_def] ) >>
match_mp_tac GraphFnAp >>
fsrw_tac [][HasFnType_def]
QED

(*---------------------------------------------------------------------------*)
(* Restrictions of functions and binary operators to subtypes.               *)
(*---------------------------------------------------------------------------*)
Definition Rs_def:
   Rs f X = GraphFn X (Apply f)
End

Definition Rs2_def:
   Rs2 binop X = GraphFn X (\x. GraphFn X (Apply (Apply binop x)))
End

Definition SubType_def:
   SubType X pred = Spec X (\s. pred ' s = True)
End

Theorem SubType1Lemma:
     !X f p.
      f In (X ->X)
      ==>
      p In (X -> Bool)
      ==>
      (!x. x In X ==> (p ' x = True) ==> (p ' (f ' x) = True))
      ==>
      HasFnType
       (Apply f)
       (Spec X (\s. p ' s = True)) (Spec X (\s. p ' s = True))
Proof
   RW_TAC std_ss [SubType_def,HasFnType_def,Spec_def]
    THEN METIS_TAC[InFn]
QED

Theorem SubType1:
     !X f p.
      f In (X ->X)
      ==>
      p In (X -> Bool)
      ==>
      (!x. x In X ==> (p ' x = True) ==> (p ' (f ' x) = True))
      ==>
      Rs f (SubType X p) In (SubType X p -> SubType X p)
Proof
   METIS_TAC[Rs_def,SubType_def,HasFnType_def,Spec_def,SubType1Lemma,GraphFnType]
QED

Theorem SubType2Lemma1:
     !X binop p.
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
       (Spec X (\s. p ' s = True))
Proof
   RW_TAC std_ss [SubType_def,HasFnType_def,Spec_def]
    THEN METIS_TAC[InFn]
QED

Theorem SubType2Lemma2:
     !X binop p.
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
       ((Spec X (\s. p ' s = True)) -> (Spec X (\s. p ' s = True)))
Proof
   RW_TAC std_ss [SubType_def,HasFnType_def]
    THEN METIS_TAC[SubType2Lemma1,GraphFnType]
QED

Theorem SubType2:
     !X binop p.
      binop In (X -> (X -> X) )
      ==>
      p In (X -> Bool)
      ==>
      (!x y.
        x In X ==>
        y In X ==> (p ' x = True) ==> (p ' y = True) ==> (p ' ((binop ' x) ' y) = True))
      ==>
      Rs2 binop (SubType X p) In (SubType X p -> (SubType X p -> SubType X p))
Proof
   RW_TAC std_ss [Rs2_def,SubType_def,HasFnType_def,Spec_def]
    THEN METIS_TAC[SubType2Lemma2,GraphFnType]
QED

(*---------------------------------------------------------------------------*)
(* The equality function on a set.                                           *)
(*---------------------------------------------------------------------------*)
Definition Eq_def:
   Eq X = GraphFn X (\x. GraphFn X (\y. bool2Bool(x = y)))
End

Theorem EqAp:
     !X x y. x In X ==> y In X ==> (((Eq X ' x) ' y) = bool2Bool(x = y))
Proof
   RW_TAC std_ss [Eq_def,GraphFnAp]
QED

Theorem ApEq:
     !X x y. x In X ==> y In X ==> ((x = y) = (((Eq X ' x) ' y) = True))
Proof
   RW_TAC std_ss [Eq_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]
QED

(*---------------------------------------------------------------------------*)
(* Boolean operations as sets.                                               *)
(*---------------------------------------------------------------------------*)
Definition Imp_def:
   Imp = GraphFn
          Bool
          (\x. GraphFn Bool (\y. bool2Bool((x = True) ==> (y = True))))
End

Theorem ImpAp:
     !x y. x In Bool
           ==>
           y In Bool
           ==>
           (((Imp ' x) ' y) = bool2Bool((x=True) ==> (y=True)))
Proof
   RW_TAC std_ss [Imp_def,GraphFnAp]
QED

Theorem ApImp:
     !x y. x In Bool
           ==>
           y In Bool
           ==>
           (((x=True) ==> (y=True)) = (((Imp ' x) ' y) = True))
Proof
   RW_TAC std_ss [Imp_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]
QED

Definition And_def:
   And = GraphFn
          Bool
          (\x. GraphFn Bool (\y. bool2Bool((x = True) /\ (y = True))))
End

Theorem AndAp:
     !x y. x In Bool
           ==>
           y In Bool
           ==>
           (((And ' x) ' y) = bool2Bool((x=True) /\ (y=True)))
Proof
   RW_TAC std_ss [And_def,GraphFnAp]
QED

Theorem ApAnd:
     !x y. x In Bool
           ==>
           y In Bool
           ==>
           (((x=True) /\ (y=True)) = (((And ' x) ' y) = True))
Proof
   RW_TAC std_ss [And_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]
QED

Definition Or_def:
   Or = GraphFn
         Bool
         (\x. GraphFn Bool (\y. bool2Bool((x = True) \/ (y = True))))
End

Theorem OrAp:
     !x y. x In Bool
           ==>
           y In Bool
           ==>
           (((Or ' x) ' y) = bool2Bool((x=True) \/ (y=True)))
Proof
   RW_TAC std_ss [Or_def,GraphFnAp]
QED

Theorem ApOr:
     !x y. x In Bool
           ==>
           y In Bool
           ==>
           (((x=True) \/ (y=True)) = (((Or ' x) ' y) = True))
Proof
   RW_TAC std_ss [Or_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]
QED

Definition Not_def:
   Not = GraphFn Bool (\x. bool2Bool(~(x = True)))
End

Theorem NotAp:
     !x. x In Bool ==> ((Not ' x) = bool2Bool(~(x = True)))
Proof
   RW_TAC std_ss [Not_def,GraphFnAp]
QED

Theorem ApNot:
     !x. x In Bool ==> ((~(x = True)) = ((Not ' x) = True))
Proof
   RW_TAC std_ss [Not_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]
QED


(*---------------------------------------------------------------------------*)
(* Quantifiers as sets.                                                      *)
(*---------------------------------------------------------------------------*)
Definition Forall_def:
   Forall X =
    GraphFn (X -> Bool) (\f. bool2Bool(!x. x In X ==> (f ' x = True)))
End

Theorem ForallAp:
     !f X. f In (X -> Bool)
           ==>
           ((Forall X ' f) = bool2Bool !x. x In X ==> (f ' x = True))
Proof
   RW_TAC std_ss [Forall_def,GraphFnAp]
QED

Theorem ApForall:
     !f X. f In (X -> Bool)
           ==>
           ((!x. x In X ==> (f ' x = True)) = ((Forall X ' f) = True))
Proof
   RW_TAC std_ss [Forall_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]
QED

Definition Exists_def:
   Exists X =
    GraphFn (X -> Bool) (\f. bool2Bool(?x. x In X /\ (f ' x = True)))
End

Theorem ExistsAp:
     !f X. f In (X -> Bool)
           ==>
           ((Exists X ' f) = bool2Bool ?x. x In X /\ (f ' x = True))
Proof
   RW_TAC std_ss [Exists_def,GraphFnAp]
QED

Theorem ApExists:
     !f X. f In (X -> Bool)
           ==>
           ((?x. x In X /\ (f ' x = True)) = ((Exists X ' f) = True))
Proof
   RW_TAC std_ss [Exists_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]
QED

Definition Choose_def:
   Choose X = GraphFn (X -> Bool) (\f. @x. x In X /\ (f ' x = True))
End

Theorem ChooseAp:
     !f X. f In (X -> Bool)
           ==>
           (Choose X ' f = @x. x In X /\ (f ' x = True))
Proof
   RW_TAC std_ss [Choose_def,GraphFnAp]
QED

Theorem ApChoose:
     !f X. f In (X -> Bool)
           ==>
           ((@x. x In X /\ (f ' x = True)) = Choose X ' f)
Proof
   RW_TAC std_ss [Choose_def,GraphFnAp,bool2Bool_def,Bool_CLAUSES]
QED
