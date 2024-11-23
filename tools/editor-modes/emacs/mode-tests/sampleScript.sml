open foobar

val _ = new_theory "foobar";

Theorem foo0 = TRUTH
Theorem foo = TRUTH

Theorem bar: x = x
Proof simp[]
QED

Type x = “:bool”

Definition foo:
  foo x = x + 2
End

Theorem foo:
  x = x
Proof
  all_tac
QED

Definition bar:
  bar x y ⇔
  ∀z.
    x + z < y + z ∧ let a = 2 * x ;
                        b = 3 * z
                    in
                      a * b ≤ x
End

Theorem baz:
  x ∧ let
        a = b;
        c = d;
      in
        x ⇒ a ∧
            c
Proof
  some_tactic
QED

Theorem ifindent1:
  p = if x = 3 then
        10
      else
        14
Proof
  another_tactic ‘quotation arg’
QED

Theorem ifindent2:
  p = if x = 3 then
        10
      else if x = 10 then
        14
      else 16
Proof
  another_tactic ‘quotation arg’
QED

Theorem caseindent1:
  p ⇒ case x of
      | y =>
          z + y + long expression
      | a => something
Proof
  tactic
QED

Theorem caseindent2:
  p ⇒ case x of
        y =>
          z + y + long expression
      | a => something
      | b => last thing ∧
             something
Proof
  tactic
QED

Theorem doindent1:
  do
    x <- e1;
    y <- e2;
  od
Proof
  foo
QED

Theorem first_suffices_by_indent:
  some_asm ∧ p ⇒
  some_goal
Proof
  ‘a long ∧ statement of a ∧ simple subgoal’
    suffices_by atactic >>
  finishing_tactic
QED

Theorem first_by_indent:
  some_goal
Proof
  ‘some other goal’
    by atactic >>
  finishing_tactic
QED

Theorem later_suffices_by_by_indent:
  some_goal
Proof
  tac1 >>
  ‘goal’
    suffices_by foo >>
  ‘goal2’ suffices_by
    bar >>
  ‘goal3’
    by foo >>
  ‘goal4’ by
    foo >>
  finisher
  >> ‘goal4’
    by foobar >>
  ‘goal5’
    by (‘subgoal1’
          suffices_by tac >>
        ‘subgoal2’
          by another_tac) >>
  finisher
QED

Theorem alpha_qfier_and_blashthen:
  (LEAST n. p ∧ q n ⇒
            r n)
  =
  10
Proof
  tac \\
  tac2
QED

(* escaped_alpha_qfier *)
val t =  “P $some ∧ x < y ∧
          Q”;

(* escaped symbol qfier *)
val t = “P $@ ∧
         q”

Theorem eval_op_later:
  eval_op f vs s = (res,t) ⇒ s ≤ t
Proof
  fs [eval_op_def, AllCaseEqs(),fail_def,return_def] \\ rw[]
  \\ fs[later_refl] \\ fs[later_def]
  \\ Cases_on ‘s.input’ \\ fs[forward_def,greater_def]
QED

Theorem ceqnat_behaviour[betasimp]:
  ceqnat @@ church n @@ church m -n->* cB (n = m)
Proof
  SIMP_TAC (bsrw_ss()) [ceqnat_def] THEN
  Q.ID_SPEC_TAC ‘m’ THEN Induct_on ‘n’ THEN1
   SIMP_TAC (bsrw_ss()) [] THEN
  ASM_SIMP_TAC (bsrw_ss()) [] THEN
  Cases_on ‘m’ THEN SRW_TAC [][]
QED

Theorem testTHENL:
  foo
Proof
  tact1 THENL [
    tac1 >-
     foo,
    tac2
  ] >>
  foo
QED

Theorem morelet_indent:
  let x = 2 in p x ∧ y
Proof
  tac
QED

Theorem eliot_let_indent:
  foo x =
  let
    a = b
  in
    z
Proof
  tac
QED

Definition foo:
  foo x =
  case x of
    NONE => 3
  | SOME z => 4
End

Theorem term_quantifiers:
  Q1 (\x. big long
              expression x) /\
  Q2 (\ x. big long
               expression x) /\
  P1 (λy. big longer
              expression y) /\
  P2 (λ y. big longer
               expression y) /\
  p (@n. something long
                   on n) /\
  p (@ n. something long
                    on n) /\
  R (LEAST n. yea another long
                  expression on n) /\
  R' (some(m,n). yea another long
                     expression on mn)
Proof
  tact1 >> tac2
QED

Theorem EXISTS_i2mw[local]:
  !x. mw_ok (SND x) /\ ~(x = (T,[])) ==> ?y. x = i2mw y
Proof
  Cases \\ SIMP_TAC std_ss [Excl "lift_disj_eq"] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC mw_ok_IMP_EXISTS_n2mw THEN1
   (Q.EXISTS_TAC ‘(& n)’ \\ ASM_SIMP_TAC std_ss [i2mw_def,n2mw_11]
    \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ intLib.COOPER_TAC)
  \\ ‘~(n = 0)’ by METIS_TAC [n2mw_def]
  \\ Q.EXISTS_TAC ‘if q then -(& n) else (& n)’ \\ POP_ASSUM MP_TAC
  \\ Cases_on ‘q’ \\ FULL_SIMP_TAC std_ss [i2mw_def,n2mw_11]
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ intLib.COOPER_TAC
QED

Datatype:
  foo = C1 num | C2
End

Theorem foo = blah

Inductive foob:
[~rule1:] foob 0 ∧
[~suc:]
  (∀n. foob n ⇒ foob (SUC n)) ∧
[last:]
  (l. foob (HD l) ==> foob (LAST l))
End

(* issue tested here is that |>, should be seen as two tokens, not one *)
Theorem foo:
  P (s with <| fld1 := foo.other_fld |>,
     second_component)  ∧
  Q (s with fld1 := foo_bar,
     second_component) ∧
  R (s with <| fld := foo_bar |>,
     fld)
Proof
  tactic
QED

val q = ‘inv (2r pow (e + 1)) < inv (2r pow e)’

(* Theorem broken:
  foo
Proof
  tac
QED *)

Inductive foob2:
[~rule1:] foob2 0 ∧
[suc[simp,compute]:]
  (∀n. foob n ⇒ foob (SUC n)) ∧
[last:]
  (l. foob (HD l) ==> foob (LAST l))
End

Definition foo:
  foo x = λy z. y + z
End


CoInductive reln:
[~rule:] ∀x. reln (f x)
[rule2:] ∀y. reln (y 3)
End

val _ = export_theory()
