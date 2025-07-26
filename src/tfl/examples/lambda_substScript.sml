(*===========================================================================*)
(*       Substitution in the name-carrying lambda calculus                   *)
(*===========================================================================*)
Theory lambda_subst
Ancestors
  prim_rec arithmetic pred_set
Libs
  stringLib pred_setLib pairLib


(*---------------------------------------------------------------------------
    Type of lambda terms
 ---------------------------------------------------------------------------*)

Datatype:
 term = Var string
      | Comb term term
      | Abs string term
End

(*---------------------------------------------------------------------------
    The system-generated size definition doesn't work well for subst
    since variable renaming can increase the size of a term when variable
    name length is included in the size calculation. Thus we use a size
    definition in which variables have zero size.
 ---------------------------------------------------------------------------*)

Definition size_def:
  size (Var _) = 0 ∧
  size (Comb M N) = size M + size N + 1 ∧
  size (Abs _ M) = size M + 1
End

Theorem size_less[simp]:
  size M < size(Comb M N) ∧
  size N < size(Comb M N) ∧
  size M < size(Abs v M)
Proof
  rw[size_def]
QED

(*---------------------------------------------------------------------------
     Delete an element from a list at most once.
 ---------------------------------------------------------------------------*)

Definition del1_def:
  del1 x [] = [] /\
  del1 x (h::t) = if x=h then t else h::del1 x t
End

(*---------------------------------------------------------------------------
      Free variables of a term, accumulator style.
 ---------------------------------------------------------------------------*)

Definition fv_def:
  fv (Var x) A    = (if MEM x A then A else x::A) ∧
  fv (Comb M N) A = fv M (fv N A) ∧
  fv (Abs v M) A  = if MEM v A then fv M A else del1 v (fv M A)
End

(*---------------------------------------------------------------------------
       Stick a prime on the end of a string.
 ---------------------------------------------------------------------------*)

Definition prime_def:
  prime s = STRCAT s "'"
End

Theorem strlen_prime[simp]:
  STRLEN (prime s) = 1 + STRLEN s
Proof
 rw[prime_def]
QED

(*---------------------------------------------------------------------------
     Rename a string so that it isn't a member of a list. The function
     terminates because the set of strings in L that are >= in length
     to x strictly decreases with each recursive call.
 ---------------------------------------------------------------------------*)

Definition variant_def:
  variant x L = if MEM x L then variant (prime x) L else x
Termination
  WF_REL_TAC ‘measure (λ(x,L). CARD {s | MEM s L /\ LENGTH x ≤ LENGTH s})’ >>
  rw[] >>
  irule CARD_PSUBSET >> conj_tac
  >- rw[GSPEC_AND] >>
  rw[PSUBSET_MEMBER,SUBSET_DEF] >>
  first_x_assum (irule_at Any) >>
  decide_tac
End

Theorem variant_not_in:
  ∀x L. variant x L ∉ set L
Proof
  recInduct variant_ind >> rw [] >> rw[Once variant_def]
QED

(*---------------------------------------------------------------------------
     Make subst x Q M parse and print like [x |-> Q]M
 ---------------------------------------------------------------------------*)

val _ =
  add_rule {term_name = "subst",
      fixity = Parse.Closefix,
      pp_elements = [TOK "[", TM, HardSpace 1, TOK "|->", BreakSpace(1,0),
                             TM, TOK "]"],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase, (PP.CONSISTENT, 2))};

(*---------------------------------------------------------------------------
     Capture-avoiding substitution of terms for variables
 ---------------------------------------------------------------------------*)

val subst_defn =
 Hol_defn
  "subst"
  ‘[x |-> Q] (Var v) = (if x=v then Q else Var v) ∧
   [x |-> Q] (Comb M N) = Comb ([x |-> Q] M) ([x |-> Q] N) ∧
   [x |-> Q] (Abs v M)  =
      (if x=v then Abs v M else
        if MEM x (fv M []) /\ MEM v (fv Q [])   (* capture would happen *)
        then let v' = variant v (fv M (fv Q []))
             in Abs v' ([x |-> Q] ([v |-> Var v'] M))
        else Abs v ([x |-> Q] M))’

(*---------------------------------------------------------------------------
   Instantiate and simplify the auxiliary eqns and induction theorem
  ---------------------------------------------------------------------------*)

val [aux_ind, var_eqn, comb_eqn, abs_eqn] =
  Defn.instantiate_aux subst_defn
        “measure (size o SND o SND)”
        (SIMP_RULE arith_ss [] o SRULE[]);

Overload substFn[local] = “subst_tupled_aux (measure (size ∘ SND ∘ SND))”

(*---------------------------------------------------------------------------
   In the Abs case of subst, there can be a variable renaming before
   substitution continues. Variable renaming won't change the size of
   the term, which is key for termination.
  ---------------------------------------------------------------------------*)

Theorem variable_renaming_size:
  ∀v Q M w. (Q = Var w) ⇒ size (substFn (v,Q,M)) = size M
Proof
  recInduct aux_ind >> rw[]
  >- rw[var_eqn, size_def]
  >- rw[comb_eqn,size_def]
  >- (rw[abs_eqn] >> gvs[] >> rw[size_def])
QED

Theorem unexpand_measure[local]:
  (\x x'. size (SND (SND x)) < size (SND (SND x'))) =
  measure (size o SND o (SND:string#term#term->term#term))
Proof
  rw[FUN_EQ_THM, measure_def]
QED

(*---------------------------------------------------------------------------
   Prove termination and thereby obtain final equations and induction thm
 ---------------------------------------------------------------------------*)

val (def,ind) =
Defn.tprove (subst_defn,
  WF_REL_TAC `measure (size o SND o SND)` >> simp [] >>
  (* now Abs case ...  *)
  rw [size_def, unexpand_measure, DECIDE ``x < y + 1 <=> x <= y``] >>
  rpt (pop_assum kall_tac) >>
  (* Change argument to be about equality of term size and
     generalize "variant" invocation away *)
  ‘∀v w. size (substFn (v,Var w,M)) = size M’ suffices_by
      metis_tac[LESS_OR_EQ] >>
  metis_tac[variable_renaming_size]
 );

Theorem subst_def = def;
Theorem subst_ind = ind;


(*---------------------------------------------------------------------------
    Applications of subst can be evaluated in the logic with EVAL
 ---------------------------------------------------------------------------*)

val th =
  EVAL “["z" |-> Var"a"]
        (Abs "a'" (Abs "a" (Comb (Var "a'") (Var "z"))))”;

