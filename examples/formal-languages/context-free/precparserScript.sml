open HolKernel Parse boolLib bossLib;

open optionTheory listTheory

open lcsymtacs

(* simple (infixes + function application via juxtaposition) precedence
   parser

   This is all that is needed to handle the precedence parsing done by
   SML, where one can assume that handling of parentheses has already
   been done, and there are only binary infixes to worry about.

*)

val _ = new_theory "precparser";

val _ = ParseExtras.tight_equality()

val bool_case_eq = prove_case_eq_thm{
  case_def= TypeBase.case_def_of ``:bool``,
  nchotomy = TypeBase.nchotomy_of ``:bool``
};

val option_case_eq = prove_case_eq_thm{
  case_def= option_case_def,
  nchotomy = option_CASES
               |> ONCE_REWRITE_RULE [DISJ_COMM]
};

val sum_case_eq = prove_case_eq_thm {
  case_def = sumTheory.sum_case_def,
  nchotomy = sumTheory.sum_CASES
};

val list_case_eq = prove_case_eq_thm{
  case_def = listTheory.list_case_def,
  nchotomy = listTheory.list_CASES
};


val _ = Datatype`tokrel = Reduce | Shift`

val tokrel_case_eq = prove_case_eq_thm {
  case_def = theorem "tokrel_case_def",
  nchotomy = theorem "tokrel_nchotomy"
};

val _ = Datatype`
  pMachine = <| rules : 'tok # 'tok -> tokrel option ; (* stk tok , strm tok *)
                reduce : 'trm -> 'tok -> 'trm -> 'trm option ;
                lift : 'tok -> 'trm ;
                isOp : 'tok -> bool ;
                mkApp : 'trm -> 'trm -> 'trm option |>
`;


(* stack is list of tokens + terms *)
val precparse1_def = Define`
  precparse1 pM (stk, strm) =
     case strm of
         [] =>
           (case stk of
               INR tm2 :: INL opn :: INR tm1 :: rest =>
                 OPTION_MAP (λr. (INR r :: rest, [])) (pM.reduce tm1 opn tm2)
             | _ => NONE)
       | tok :: strm_rest =>
         if pM.isOp tok then
           case stk of
               INR tm2 :: INL opn :: INR tm1 :: stk_rest =>
               (case pM.rules (opn, tok) of
                    SOME Shift => SOME(INL tok :: stk, strm_rest)
                  | SOME Reduce =>
                      OPTION_MAP (λr. (INR r :: stk_rest, tok :: strm_rest))
                                 (pM.reduce tm1 opn tm2)
                  | NONE => NONE)
             | [INR tm] => SOME([INL tok; INR tm], strm_rest)
             | _ => NONE
         else
           case stk of
               [] => SOME([INR (pM.lift tok)], strm_rest)
             | INR ftm :: stk_rest =>
                 OPTION_MAP (λr. (INR r :: stk_rest, strm_rest))
                            (pM.mkApp ftm (pM.lift tok))
             | INL _ :: _ => SOME(INR (pM.lift tok) :: stk, strm_rest)
`;

val wfStk_def = Define`
  (wfStk [] ⇔ T) ∧
  (wfStk [INR _] ⇔ T) ∧
  (wfStk [INL _] ⇔ F) ∧
  (wfStk (INL _ :: INR tm :: rest) ⇔ wfStk (INR tm :: rest)) ∧
  (wfStk (INR _ :: INL t :: rest) ⇔ wfStk (INL t :: rest)) ∧
  (wfStk _ ⇔ F)
`;
val _ = export_rewrites ["wfStk_def"]

val wfStk_ignores_hdvalues = store_thm(
  "wfStk_ignores_hdvalues[simp]",
  ``wfStk (INL l::t) = wfStk (INL ARB :: t) ∧
    wfStk (INR r::t) = wfStk (INR ARB :: t)``,
  Cases_on `t` >> simp[] >> rename1 `wfStk (INL ARB :: el2 :: tl)` >>
  Cases_on `el2` >> simp[]);

val precparse1_preserves_wfStk = store_thm(
  "precparse1_preserves_wfStk",
  ``wfStk stk0 ∧ precparse1 pM (stk0, strm0) = SOME (stk, strm) ⇒
    wfStk stk``,
  Cases_on `strm0` >> Cases_on `stk0` >>
  dsimp[precparse1_def, list_case_eq, sum_case_eq, bool_case_eq,
        option_case_eq, tokrel_case_eq] >>
  rw[] >> fs[]);

val LT_SUC = store_thm(
  "LT_SUC",
  ``x < SUC y ⇔ (x = 0) ∨ ∃m. x = SUC m ∧ m < y``,
  Cases_on `x` >> simp[]);

val wfStk_ALT = store_thm(
  "wfStk_ALT",
  ``wfStk l ⇔ (l ≠ [] ⇒ ∀opn. LAST l ≠ INL opn) ∧
              (∀i. i + 1 < LENGTH l ⇒ ISR (EL i l) ≠ ISR (EL (i + 1) l))``,
  Induct_on `l` >> simp[] >> Cases >> simp[] >> rename1 `wfStk (_ :: stk)` >>
  Cases_on `stk` >> simp[] >> fs[] >> rename1 `wfStk (_ :: el2 :: stk)` >>
  Cases_on `el2` >> simp[] >- (disj2_tac >> qexists_tac `0` >> simp[]) >>
  simp[DECIDE ``x + 1 < SUC y ⇔ x < y``] >>
  dsimp[LT_SUC, DECIDE ``x + 1 = SUC x``])

val precparse1_reduces = store_thm(
  "precparse1_reduces",
  ``precparse1 pM (stk0,strm0) = SOME (stk,strm) ⇒
      LENGTH strm < LENGTH strm0 ∨ strm = strm0 ∧ LENGTH stk < LENGTH stk0``,
  Cases_on `strm0` >> Cases_on `stk0` >>
  dsimp[precparse1_def, list_case_eq, sum_case_eq, bool_case_eq,
        option_case_eq, tokrel_case_eq] >> rw[] >> simp[]);

val isFinal_def = Define`
  (isFinal ([INR _],[]) ⇔ T) ∧
  (isFinal _ ⇔ F)
`;
val _ = export_rewrites ["isFinal_def"]


val precparse_def = tDefine "precparse" `
  precparse pM (stk0,strm0) =
     if isFinal (stk0,strm0) then SOME (OUTR (HD stk0))
     else
       case precparse1 pM (stk0, strm0) of
           NONE => NONE
         | SOME (stk, strm) => precparse pM (stk, strm)
` (WF_REL_TAC
    `inv_image (measure LENGTH LEX measure LENGTH) (λ(_,y,z). (z,y))` >>
   metis_tac[precparse1_reduces]);

(* test case
local open stringTheory finite_mapTheory in end
val _ = Datatype`ast = Plus ast ast | Times ast ast | App ast ast | C char`
val fm = ``FLOOKUP (FEMPTY |+ ((#"+",#"*"), Shift) |+ ((#"*",#"+"), Reduce)
                      |+ ((#"+",#"+"), Reduce) |+ ((#"*",#"*"), Reduce))``

val isOp = ``λc. c = #"*" ∨ c = #"+"``
val reduce = ``λtm1 c tm2. if c = #"*" then SOME (Times tm1 tm2)
                           else SOME (Plus tm1 tm2)``
val lift = ``C``

val m = ``<| rules :=  ^fm ;
             reduce := ^reduce ;
             lift := C;
             isOp := ^isOp;
             mkApp := λt1 t2. SOME (App t1 t2) |>``

EVAL ``precparse ^m ([],"3*fx*7+9")``;
EVAL ``precparse ^m ([],"3+fx*7+9")``;
EVAL ``precparse ^m ([],"fxy")``;
EVAL ``precparse ^m ([],"x*2")``;
EVAL ``precparse ^m ([],"3++7")`` (* fails *);
*)

val _ = export_theory();
