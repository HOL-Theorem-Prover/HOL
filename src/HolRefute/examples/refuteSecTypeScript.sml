(* HolRefute by case study: Volpano-Smith security typing, adapted from the
   security-type-system case study in the Nitpick ITP 2010 and LPAR 2010
   papers and recast here as an executable checker. *)

Theory refuteSecType
Libs
  Refute

Datatype:
  vname = Pub | Sec
End

Datatype:
  aexp = Num num | Var vname | Add aexp aexp
End

Datatype:
  bexp = Leq aexp aexp
End

Datatype:
  com = Skip | Asgn vname aexp | CSeq com com | CIf bexp com com
End

Definition aval_def:
  aval st (Num n) = n /\
  aval st (Var v) = st v /\
  aval st (Add a b) = aval st a + aval st b
End

Definition bval_def:
  bval st (Leq a b) <=> aval st a <= aval st b
End

(* The fragment is while-free on purpose: evaluation remains total and
   executable, while the implicit-flow bug lives entirely in CIf. *)

Definition cval_def:
  cval Skip st = st /\
  cval (Asgn v a) st = (\w. if w = v then aval st a else st w) /\
  cval (CSeq c1 c2) st = cval c2 (cval c1 st) /\
  cval (CIf b c1 c2) st =
    if bval st b then cval c1 st else cval c2 st
End

Definition high_def:
  high Pub = F /\
  high Sec = T
End

Definition ahigh_def:
  ahigh (Num n) = F /\
  ahigh (Var v) = high v /\
  ahigh (Add a b) = (ahigh a \/ ahigh b)
End

Definition bhigh_def:
  bhigh (Leq a b) = (ahigh a \/ ahigh b)
End

Definition low_eq_def:
  low_eq s t <=> s Pub = t Pub
End

Definition csec0_def:
  csec0 ctx Skip = T /\
  csec0 ctx (Asgn v a) = ((ahigh a \/ ctx) ==> high v) /\
  csec0 ctx (CSeq c1 c2) = (csec0 ctx c1 /\ csec0 ctx c2) /\
  csec0 ctx (CIf b c1 c2) = (csec0 ctx c1 /\ csec0 ctx c2)
End

Definition csec_def:
  csec ctx Skip = T /\
  csec ctx (Asgn v a) = ((ahigh a \/ ctx) ==> high v) /\
  csec ctx (CSeq c1 c2) = (csec ctx c1 /\ csec ctx c2) /\
  csec ctx (CIf b c1 c2) =
    (csec (ctx \/ bhigh b) c1 /\ csec (ctx \/ bhigh b) c2)
End

(* The diagnostic tactic is followed by cheat in deliberately false
   conjectures so that the counterexample remains visible in the build. *)

Theorem accepted_programs_do_not_leak:
  csec0 F c /\ low_eq s t ==> low_eq (cval c s) (cval c t)
Proof
  REFUTE_TAC >> cheat
QED

Theorem low_expressions_agree[local]:
  ~ahigh a /\ low_eq s t ==> aval s a = aval t a
Proof
  Induct_on `a`
  >- simp [ahigh_def, aval_def]
  >- (Cases_on `v` >> simp [ahigh_def, high_def, low_eq_def, aval_def])
  >> simp [ahigh_def, aval_def]
QED

Theorem low_guards_agree[local]:
  ~bhigh b /\ low_eq s t ==> bval s b = bval t b
Proof
  Cases_on `b` >>
  simp [bhigh_def, bval_def] >>
  metis_tac [low_expressions_agree]
QED

Theorem high_context_confinement[local]:
  csec T c ==> !s. cval c s Pub = s Pub
Proof
  Induct_on `c`
  >- simp [csec_def, cval_def]
  >- (Cases_on `v` >> simp [csec_def, cval_def, high_def])
  >- simp [csec_def, cval_def]
  >> simp [csec_def, cval_def] >>
  rpt strip_tac >>
  Cases_on `bval s b` >> simp []
QED

Theorem fixed_checker_sound_characterisation[local]:
  ((!c ctx s t.
      csec ctx c /\ low_eq s t ==> low_eq (cval c s) (cval c t)) <=>
   !v : vname. v = Pub \/ v = Sec)
Proof
  eq_tac
  >- (rpt strip_tac >> Cases_on `v` >> simp [])
  >> strip_tac >> pop_assum kall_tac >>
  Induct_on `c`
  >- simp [csec_def, cval_def]
  >- (Cases_on `v`
      >- (simp [csec_def, cval_def, high_def, low_eq_def] >>
          metis_tac [low_expressions_agree, low_eq_def])
      >> simp [csec_def, cval_def, high_def, low_eq_def])
  >- (simp [csec_def, cval_def] >> metis_tac [])
  >> rpt gen_tac >> strip_tac >>
  Cases_on `bhigh b`
  >- (fs [csec_def] >>
      Cases_on `bval s b` >> Cases_on `bval t b` >>
      fs [cval_def, low_eq_def] >>
      metis_tac [high_context_confinement])
  >> `bval s b = bval t b` by
       metis_tac [low_guards_agree] >>
  Cases_on `bval s b` >> Cases_on `bval t b` >>
  fs [csec_def, cval_def] >> metis_tac []
QED

(* QuickCheck runs on the soundness statement itself, so a bounded search
   reports what it covered rather than a proof; the local characterization
   above carries the command induction that proves it. *)

Theorem the_fixed_checker_is_sound:
  !c ctx s t.
    csec ctx c /\ low_eq s t ==> low_eq (cval c s) (cval c t)
Proof
  QUICKCHECK_TAC >>
  rewrite_tac [fixed_checker_sound_characterisation] >>
  Cases >> simp []
QED
