(*
UOK  Formalises (an improvement of) the main result in:
UOK  "Solving Problems with Finite Test Sets"
UOK    by Cristian S. Calude, Helmut Jürgensen, Shane Legg
UOK
UOK  namely:
UOK    Every first-order formula (in prenex normal form) over the natural numbers is
UOK    "solved" by a single instance.
UOK
UOK    Given a formula f in prenex normal form
UOK
UOK       f := Qx1.Qx2....Qxs. P(x1,...,xs) (each Q in {∀,∃}),
UOK
UOK    a "test instance" (n1,...,ns) is a valuation such that
UOK
UOK      f is true iff P(n1,...,ns) is true
UOK
UOK    The main result proved here is that every formula has a test instance.
UOK
UOK  Thus, every first-order formula can be decided by checking a single instance.
UOK  This sounds surprising at first, until you realise what is not shown: how to
UOK  construct the test instance.
UOK
UOK  The result in the paper is weaker:
UOK    Rather than a single instance, they show solvability by a finite test set.
UOK    A "test set" is a set T of instances such that
UOK       f is true iff f is true over T
UOK    where "f is true over T" means f is true when the quantifiers are relativised
UOK    to the domains represented by T.
UOK
UOK  We prove their result as a corollary.
*)
Theory finite_test_set
Ancestors
  combin list rich_list pred_set divides
Libs
  boolSimps mp_then


val _ = temp_tight_equality();

(*
  Since we only care about prenex normal formulae, we design our datatypes to
  represent these directly. First, quantifier-free formulae with de Bruijn
  variables and a single Sheffer connective.
*)

(* Function "symbols" carry their semantics to avoid pointless naming. *)
Datatype:
  term = Var num | Fun (num list -> num) (term list)
End

(* Similarly predicate symbols carry their semantics *)
Datatype:
  prop = Pred (num list -> bool) (term list) | Nand prop prop
End

(* Note: this makes the language rather more expressive than desired.
   We usually want f in (Fun f) and (Pred f) to be decidable.
   However, this does not sabotage our main results: if these expressive
   formulae are solvable, then in particular so are the less expressive ones. *)

(* Semantics of quantifier-free formulae *)

val val_term_def = tDefine"val_term"`
  val_term env (Var n) = EL n env ∧
  val_term env (Fun f ts) = f (MAP (val_term env) ts)`
(WF_REL_TAC`measure (term_size o SND)` \\ Induct \\ EVAL_TAC
 \\ rw[] \\ res_tac \\ rw[]);
val _ = export_rewrites["val_term_def"];

Definition val_prop_def:
  val_prop env (Pred f ts) = f (MAP (val_term env) ts) ∧
  val_prop env (Nand p1 p2) = ¬(val_prop env p1 ∧ val_prop env p2)
End
val _ = export_rewrites["val_prop_def"];

(* Now we add quantifiers *)

Datatype:
  quan = Forall | Exists
End

val _ = type_abbrev("form",``:quan list # prop``);

val val_form_aux_def = tDefine"val_form_aux"`
  val_form_aux ([],p) env = val_prop env p ∧
  val_form_aux (Forall::qs,p) env = (∀n. val_form_aux (qs,p) (n::env)) ∧
  val_form_aux (Exists::qs,p) env = (∃n. val_form_aux (qs,p) (n::env))`
(WF_REL_TAC`measure (LENGTH o FST o FST)` \\ rw[]);
val _ = export_rewrites["val_form_aux_def"];

Definition val_form_def:
  val_form (qs,p) = val_form_aux (qs,p) []
End

(* A test of expressiveness: Goldbach's conjecture can be represented *)
Definition Goldbach_statement_def:
  Goldbach_statement ⇔
    ∀n. 2 < n ∧ EVEN n ⇒ ∃p1 p2. prime p1 ∧ prime p2 ∧ n = p1 + p2
End

(* This is unnecessary: everything could be built into the predicates themselves *)
val _ = overload_on("Or",``λp1 p2. Nand (Nand p1 p1) (Nand p2 p2)``);

Theorem Goldbach_Pi1:
   ∃p. (* it would be nice to also say that p is decidable: this is true,
          but the theory to express this fact isn't around to my knowledge *)
       val_form ([Forall],p) ⇔ Goldbach_statement
Proof
  qexists_tac`
    Or (Pred ((λn. ¬(2 < n ∧ EVEN n)) o HD) [Var 0])
       (Pred ((λn. ∃p1 p2. prime p1 ∧ prime p2 ∧ n = p1 + p2) o HD) [Var 0])`
  \\ rw[val_form_def,Goldbach_statement_def]
  \\ metis_tac[]
QED

(* Solvability by a single instance *)

(*
  env is a test instance for f [= (qs,p)] if
  f is true ⇔ p[env] is true
*)
Definition test_inst_def:
  test_inst env (qs,p) ⇔
    (LENGTH env = LENGTH qs) ∧
    (val_form (qs,p) ⇔ val_prop env p)
End

Definition solvable_def:
  solvable f ⇔ ∃env. test_inst env f
End

(* Non-constructive definition of test instances *)

Definition nu_def:
  nu env Forall qs p =
    (if val_form_aux (Forall::qs,p) env then 0
     else LEAST m. ¬val_form_aux (qs,p) (m::env)) ∧
  nu env Exists qs p =
    (if ¬val_form_aux (Exists::qs,p) env then 0
     else LEAST m. val_form_aux (qs,p) (m::env))
End

Definition mk_test_inst_def:
  mk_test_inst env [] p = env ∧
  mk_test_inst env (q::qs) p =
    mk_test_inst ((nu env q qs p)::env) qs p
End

Theorem LENGTH_mk_test_inst[simp]:
   ∀qs env p. LENGTH (mk_test_inst env qs p) = LENGTH env + LENGTH qs
Proof
  Induct \\ rw[mk_test_inst_def] \\ rw[]
QED

Theorem mk_test_inst_acc:
   ∀qs env. ∃env'. mk_test_inst env qs p = env'++env
Proof
  Induct
  \\ rw[mk_test_inst_def]
  \\ metis_tac[CONS_APPEND,APPEND_ASSOC]
QED

Theorem val_mk_test_inst:
   ∀qs0 env qs1 p.
     (val_form_aux (qs1,p) (DROP (LENGTH qs1) (mk_test_inst env (qs0 ++ qs1) p))
      ⇔
      val_form_aux (qs0 ++ qs1,p) env)
Proof
  Induct \\ rw[mk_test_inst_def]
  >- (
    qspecl_then[`qs1`,`env`]strip_assume_tac mk_test_inst_acc
    \\ qspecl_then[`qs1`,`env`,`p`]mp_tac LENGTH_mk_test_inst
    \\ pop_assum SUBST_ALL_TAC
    \\ rw[DROP_APPEND,DROP_LENGTH_NIL_rwt] )
  \\ qmatch_goalsub_rename_tac`nu env q`
  \\ Cases_on`q` \\ rw[]
  \\ rw[nu_def]
  \\ numLib.LEAST_ELIM_TAC
  \\ metis_tac[]
QED

(* The main result *)

Theorem all_solvable:
   ∀f. solvable f
Proof
  rw[solvable_def]
  \\ Cases_on`f`
  \\ qmatch_goalsub_rename_tac`(qs,p)`
  \\ qexists_tac`mk_test_inst [] qs p`
  \\ rw[test_inst_def]
  \\ qspecl_then[`qs`,`[]`,`[]`,`p`]mp_tac val_mk_test_inst
  \\ rw[val_form_def]
QED

(* Solvability by test sets (as in the paper) *)

(* relativising a formula *)

Definition val_form_rel_def:
  val_form_rel [] ([],p) env = val_prop env p ∧
  val_form_rel (d::ds) (Forall::qs,p) env = (∀n::d. val_form_rel ds (qs,p) (n::env)) ∧
  val_form_rel (d::ds) (Exists::qs,p) env = (∃n::d. val_form_rel ds (qs,p) (n::env))
End
val _ = export_rewrites["val_form_rel_def"];

Theorem val_form_iff_val_form_rel:
   val_form (qs,p) ⇔ val_form_rel (REPLICATE (LENGTH qs) UNIV) (qs,p) []
Proof
  rw[val_form_def]
  \\ qspec_tac(`[]:num list`,`env`)
  \\ qid_spec_tac`qs`
  \\ Induct \\ rw[]
  \\ qmatch_goalsub_rename_tac`q::qs`
  \\ Cases_on`q` \\ fs[RES_FORALL_THM,RES_EXISTS_THM]
QED

(* A test set is a domain relativised to which a formula's truth is preserved *)

Definition test_set_def:
  test_set ds (qs,p) ⇔
    (LENGTH ds = LENGTH qs) ∧
    (val_form (qs,p) ⇔ val_form_rel ds (qs,p) [])
End

(*
  We are representing test sets as a list of domains for the quantifiers.
  Here is how to retrieve the corresponding subset of the Cartesian product
  N^(LENGTH qs) (represented as a list rather than actual tuples)
*)
Definition domains_to_set_def:
   domains_to_set ds = { ms | LIST_REL (IN) ms ds }
End

(* Finitely solvable = has a finite test set *)
Definition finitely_solvable_def:
  finitely_solvable q ⇔
  ∃ds. test_set ds q ∧ FINITE (domains_to_set ds)
End

Theorem FINITE_domains_to_set:
   FINITE (domains_to_set ds) ⇔ (EVERY FINITE ds ∨ EXISTS ((=){}) ds)
Proof
  rw[domains_to_set_def]
  \\ Induct_on`ds` \\ rw[]
  \\ qmatch_abbrev_tac`FINITE s ⇔ _`
  \\ qmatch_goalsub_rename_tac`FINITE d ∧ EVERY FINITE ds`
  \\ qmatch_assum_abbrev_tac`FINITE ms ⇔ EVERY FINITE ds ∨ _`
  \\ `BIJ (λls. (HD ls, TL ls)) s (d × ms)`
  by (
    simp[BIJ_IFF_INV]
    \\ conj_tac >- (
      simp[Abbr`s`,Abbr`ms`,PULL_EXISTS] )
    \\ qexists_tac`λp. (FST p :: SND p)`
    \\ simp[Abbr`s`,Abbr`ms`,PULL_EXISTS] )
  \\ Cases_on`d = ∅` \\ fs[]
  \\ `ms = ∅ ⇔ EXISTS ((=){}) ds`
  by (
    simp[Abbr`ms`]
    \\ simp[EXTENSION]
    \\ simp[EXISTS_MEM,LIST_REL_EL_EQN,MEM_EL]
    \\ metis_tac[NOT_IN_EMPTY,CHOICE_DEF,EL_MAP,LENGTH_MAP] )
  \\ metis_tac[FINITE_BIJ,FINITE_CROSS_EQ,BIJ_INV]
QED

Theorem test_inst_test_set:
   test_inst env f ⇔ test_set (MAP (λm. {m}) (REVERSE env)) f
Proof
  Cases_on`f` \\ rw[test_inst_def,test_set_def]
  \\ qmatch_goalsub_rename_tac`val_form (qs,p)`
  \\ Cases_on`LENGTH env = LENGTH qs` \\ fs[]
  \\ AP_TERM_TAC
  \\ pop_assum mp_tac
  \\ Q.ISPEC_THEN`env`(SUBST_ALL_TAC o SYM) REVERSE_REVERSE
  \\ qspec_tac(`REVERSE env`,`env`) \\ simp[] \\ gen_tac
  \\ `val_prop (REVERSE env) = val_prop (REVERSE env ++ [])` by simp[]
  \\ pop_assum SUBST_ALL_TAC
  \\ qspec_tac(`[] : num list`,`env0`)
  \\ map_every qid_spec_tac [`qs`,`env`]
  \\ Induct \\ rw[]
  \\ Cases_on`qs` \\ fs[]
  \\ qmatch_goalsub_rename_tac`q::qs,p`
  \\ qmatch_goalsub_rename_tac`{m}`
  \\ first_x_assum(qspecl_then[`qs`,`[m] ++ env0`]mp_tac)
  \\ Cases_on`q` \\ fs[RES_FORALL_THM,RES_EXISTS_THM]
QED

Theorem all_finitely_solvable:
   ∀f. finitely_solvable f
Proof
  rw[finitely_solvable_def]
  \\ qspec_then`f`mp_tac all_solvable
  \\ rw[solvable_def]
  \\ fs[test_inst_test_set]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[FINITE_domains_to_set,EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

