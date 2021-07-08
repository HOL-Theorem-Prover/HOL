open HolKernel boolLib bossLib Parse BasicProvers
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory listTheory rich_listTheory
open integerTheory int_arithTheory
open wordsLib bitstringLib intLib

val _ = new_theory "l3_equivalence_lemmas";
val _ = set_grammar_ancestry ["arm8_step", "arm8", "armv86a_termination"];

val _ = wordsLib.output_words_as_bin();
val _ = wordsLib.guess_lengths();

val _ = numLib.prefer_num();
val _ = intLib.deprecate_int()

val _ = Globals.show_assums := false;

(******************************************************************************)

Theorem bools_of_nat_aux_length:
  ∀ len n acc.
    len ≥ 0
  ⇒ LENGTH (bools_of_nat_aux len n acc) = (Num len) + LENGTH acc
Proof
  recInduct sail2_valuesAuxiliaryTheory.bools_of_nat_aux_ind_rw >>
  rw[] >> gvs[INT_NOT_LE] >> Cases_on `len = 0` >>
  rw[Once sail2_valuesAuxiliaryTheory.bools_of_nat_aux_rw]
  >- ARITH_TAC >>
  `0 < len ∧ len - 1 ≥ 0` by ARITH_TAC >>
  first_x_assum drule >> disch_then drule >> gvs[] >> strip_tac >>
  ARITH_TAC
QED

(*
Theorem bools_of_nat_aux_def:
  ∀ len n acc.
    len ≥ 0
  ⇒ bools_of_nat_aux len n acc =
      (λl. DROP (LENGTH l - Num len) l) (PAD_LEFT F (Num len) (n2v n)) ++ acc
Proof
  ho_match_mp_tac sail2_valuesAuxiliaryTheory.bools_of_nat_aux_ind_rw >>
  rw[] >> gvs[INT_NOT_LE] >> Cases_on `len = 0` >>
  rw[Once sail2_valuesAuxiliaryTheory.bools_of_nat_aux_rw]
  >- gvs[PAD_LEFT, DROP_LENGTH_NIL]
  >- (
    last_x_assum kall_tac >> CCONTR_TAC >> pop_assum kall_tac >>
    COOPER_TAC
    ) >>
  `0 < len ∧ len - 1 ≥ 0` by ARITH_TAC >>
  first_x_assum drule_all >> gvs[] >> strip_tac >>


Theorem bools_of_nat_def:
  ∀ len n.
    bools_of_nat (&len) n =
      (λl. DROP (LENGTH l - len) l) (PAD_LEFT F len (n2v n))
Proof
  Induct >>
  rw[Once LIST_EQ_REWRITE] >>
  gvs[sail2_valuesTheory.bools_of_nat_def,
     Once sail2_valuesAuxiliaryTheory.bools_of_nat_aux_rw]
  >- (

    )


Theorem add_one_bool_ignore_overflow_aux_def:


Theorem l3_asl_AddWithCarry:
  ∀x y carry_b carry_v.
    flag_rel carry_b carry_v
  ⇒ armv86a$AddWithCarry x y carry_v =
     (I ## (λ(a,b,c,d).v2w [a;b;c;d])) (arm8$AddWithCarry (x, y, carry_b))
Proof
  rw[flag_rel_def] >>
  gvs[armv86aTheory.AddWithCarry_def, AddWithCarry_def] >>

  gvs[word_msb_def] >>

  armv86a$AddWithCarry
  arm8$AddWithCarry


*)

(******************************************************************************)

val _ = export_theory ();
