signature ILTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BLK : thm
    val CJ : thm
    val CTL_STRUCTURE_TY_DEF : thm
    val CTL_STRUCTURE_case_def : thm
    val CTL_STRUCTURE_repfns : thm
    val CTL_STRUCTURE_size_def : thm
    val DOPER_TY_DEF : thm
    val DOPER_case_def : thm
    val DOPER_repfns : thm
    val DOPER_size_def : thm
    val IL0_def : thm
    val IL10_def : thm
    val IL11_def : thm
    val IL12_def : thm
    val IL13_def : thm
    val IL14_def : thm
    val IL15_def : thm
    val IL16_def : thm
    val IL17_def : thm
    val IL18_def : thm
    val IL19_def : thm
    val IL1_def : thm
    val IL20_def : thm
    val IL21_def : thm
    val IL2_def : thm
    val IL3_def : thm
    val IL4_def : thm
    val IL5_def : thm
    val IL6_def : thm
    val IL7_def : thm
    val IL8_def : thm
    val IL9_def : thm
    val MADD : thm
    val MAND : thm
    val MASR : thm
    val MC : thm
    val MEOR : thm
    val MEXP_TY_DEF : thm
    val MEXP_case_def : thm
    val MEXP_repfns : thm
    val MEXP_size_def : thm
    val MLDR : thm
    val MLSL : thm
    val MLSR : thm
    val MMOV : thm
    val MMUL : thm
    val MORR : thm
    val MPOP : thm
    val MPUSH : thm
    val MR : thm
    val MREG_BIJ : thm
    val MREG_TY_DEF : thm
    val MREG_case : thm
    val MREG_size_def : thm
    val MROR : thm
    val MRSB : thm
    val MSTR : thm
    val MSUB : thm
    val R0 : thm
    val R1 : thm
    val R10 : thm
    val R11 : thm
    val R12 : thm
    val R13 : thm
    val R14 : thm
    val R2 : thm
    val R3 : thm
    val R4 : thm
    val R5 : thm
    val R6 : thm
    val R7 : thm
    val R8 : thm
    val R9 : thm
    val SC : thm
    val TR : thm
    val WELL_FORMED_SUB_def : thm
    val WELL_FORMED_def : thm
    val eval_il_cond_def : thm
    val from_reg_index_def : thm
    val index_of_reg_def : thm
    val mdecode_def : thm
    val popL_def : thm
    val pushL_def : thm
    val run_arm_def : thm
    val run_ir_def : thm
    val toEXP_def : thm
    val toMEM_def : thm
    val toREG_def : thm
    val translate_assignment_def : thm
    val translate_condition_def : thm
    val translate_primitive_def : thm

  (*  Theorems  *)
    val BLOCK_IS_WELL_FORMED : thm
    val CTL_STRUCTURE_11 : thm
    val CTL_STRUCTURE_Axiom : thm
    val CTL_STRUCTURE_case_cong : thm
    val CTL_STRUCTURE_distinct : thm
    val CTL_STRUCTURE_induction : thm
    val CTL_STRUCTURE_nchotomy : thm
    val DOPER_11 : thm
    val DOPER_Axiom : thm
    val DOPER_case_cong : thm
    val DOPER_distinct : thm
    val DOPER_induction : thm
    val DOPER_nchotomy : thm
    val HOARE_CJ_IR : thm
    val HOARE_SC_IR : thm
    val HOARE_TR_IR : thm
    val IR_CJ_IS_WELL_FORMED : thm
    val IR_SC_IS_WELL_FORMED : thm
    val IR_SEMANTICS_BLK : thm
    val IR_SEMANTICS_CJ : thm
    val IR_SEMANTICS_SC : thm
    val IR_SEMANTICS_TR : thm
    val IR_TR_IS_WELL_FORMED : thm
    val MEXP_11 : thm
    val MEXP_Axiom : thm
    val MEXP_case_cong : thm
    val MEXP_distinct : thm
    val MEXP_induction : thm
    val MEXP_nchotomy : thm
    val MREG2num_11 : thm
    val MREG2num_ONTO : thm
    val MREG2num_num2MREG : thm
    val MREG2num_thm : thm
    val MREG_Axiom : thm
    val MREG_EQ_MREG : thm
    val MREG_case_cong : thm
    val MREG_case_def : thm
    val MREG_distinct : thm
    val MREG_induction : thm
    val MREG_nchotomy : thm
    val SEMANTICS_OF_IR : thm
    val STATEMENT_IS_WELL_FORMED : thm
    val TRANSLATE_ASSIGMENT_CORRECT : thm
    val TRANSLATE_ASSIGMENT_CORRECT_2 : thm
    val UPLOAD_LEM_2 : thm
    val WELL_FORMED_SUB_thm : thm
    val WELL_FORMED_thm : thm
    val datatype_CTL_STRUCTURE : thm
    val datatype_DOPER : thm
    val datatype_MEXP : thm
    val datatype_MREG : thm
    val from_reg_index_thm : thm
    val num2MREG_11 : thm
    val num2MREG_MREG2num : thm
    val num2MREG_ONTO : thm
    val num2MREG_thm : thm
    val translate_def : thm
    val translate_ind : thm

  val IL_grammars : type_grammar.grammar * term_grammar.grammar


(*
   [ARMComposition] Parent theory of "IL"

   [BLK]  Definition

      |- BLK = IL18

   [CJ]  Definition

      |- CJ = IL20

   [CTL_STRUCTURE_TY_DEF]  Definition

      |- ?rep.
           TYPE_DEFINITION
             (\a0'.
                !'CTL_STRUCTURE'.
                  (!a0'.
                     (?a. a0' = (\a. CONSTR 0 (a,@v. T) (\n. BOTTOM)) a) \/
                     (?a0 a1.
                        (a0' =
                         (\a0 a1.
                            CONSTR (SUC 0) ((@v. T),@v. T)
                              (FCONS a0 (FCONS a1 (\n. BOTTOM)))) a0 a1) /\
                        'CTL_STRUCTURE' a0 /\ 'CTL_STRUCTURE' a1) \/
                     (?a0 a1 a2.
                        (a0' =
                         (\a0 a1 a2.
                            CONSTR (SUC (SUC 0)) ((@v. T),a0)
                              (FCONS a1 (FCONS a2 (\n. BOTTOM)))) a0 a1 a2) /\
                        'CTL_STRUCTURE' a1 /\ 'CTL_STRUCTURE' a2) \/
                     (?a0 a1.
                        (a0' =
                         (\a0 a1.
                            CONSTR (SUC (SUC (SUC 0))) ((@v. T),a0)
                              (FCONS a1 (\n. BOTTOM))) a0 a1) /\
                        'CTL_STRUCTURE' a1) ==>
                     'CTL_STRUCTURE' a0') ==>
                  'CTL_STRUCTURE' a0') rep

   [CTL_STRUCTURE_case_def]  Definition

      |- (!f f1 f2 f3 a. CTL_STRUCTURE_case f f1 f2 f3 (BLK a) = f a) /\
         (!f f1 f2 f3 a0 a1. CTL_STRUCTURE_case f f1 f2 f3 (SC a0 a1) = f1 a0 a1) /\
         (!f f1 f2 f3 a0 a1 a2.
            CTL_STRUCTURE_case f f1 f2 f3 (CJ a0 a1 a2) = f2 a0 a1 a2) /\
         !f f1 f2 f3 a0 a1. CTL_STRUCTURE_case f f1 f2 f3 (TR a0 a1) = f3 a0 a1

   [CTL_STRUCTURE_repfns]  Definition

      |- (!a. mk_CTL_STRUCTURE (dest_CTL_STRUCTURE a) = a) /\
         !r.
           (\a0'.
              !'CTL_STRUCTURE'.
                (!a0'.
                   (?a. a0' = (\a. CONSTR 0 (a,@v. T) (\n. BOTTOM)) a) \/
                   (?a0 a1.
                      (a0' =
                       (\a0 a1.
                          CONSTR (SUC 0) ((@v. T),@v. T)
                            (FCONS a0 (FCONS a1 (\n. BOTTOM)))) a0 a1) /\
                      'CTL_STRUCTURE' a0 /\ 'CTL_STRUCTURE' a1) \/
                   (?a0 a1 a2.
                      (a0' =
                       (\a0 a1 a2.
                          CONSTR (SUC (SUC 0)) ((@v. T),a0)
                            (FCONS a1 (FCONS a2 (\n. BOTTOM)))) a0 a1 a2) /\
                      'CTL_STRUCTURE' a1 /\ 'CTL_STRUCTURE' a2) \/
                   (?a0 a1.
                      (a0' =
                       (\a0 a1.
                          CONSTR (SUC (SUC (SUC 0))) ((@v. T),a0)
                            (FCONS a1 (\n. BOTTOM))) a0 a1) /\
                      'CTL_STRUCTURE' a1) ==>
                   'CTL_STRUCTURE' a0') ==>
                'CTL_STRUCTURE' a0') r =
           (dest_CTL_STRUCTURE (mk_CTL_STRUCTURE r) = r)

   [CTL_STRUCTURE_size_def]  Definition

      |- (!a. CTL_STRUCTURE_size (BLK a) = 1 + list_size DOPER_size a) /\
         (!a0 a1.
            CTL_STRUCTURE_size (SC a0 a1) =
            1 + (CTL_STRUCTURE_size a0 + CTL_STRUCTURE_size a1)) /\
         (!a0 a1 a2.
            CTL_STRUCTURE_size (CJ a0 a1 a2) =
            1 +
            ((\(x,y). MREG_size x + (\(x,y). COND_size x + MEXP_size y) y) a0 +
             (CTL_STRUCTURE_size a1 + CTL_STRUCTURE_size a2))) /\
         !a0 a1.
           CTL_STRUCTURE_size (TR a0 a1) =
           1 +
           ((\(x,y). MREG_size x + (\(x,y). COND_size x + MEXP_size y) y) a0 +
            CTL_STRUCTURE_size a1)

   [DOPER_TY_DEF]  Definition

      |- ?rep.
           TYPE_DEFINITION
             (\a0'.
                !'DOPER'.
                  (!a0'.
                     (?a0 a1.
                        a0' =
                        (\a0 a1.
                           CONSTR 0
                             (a0,a1,(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1) \/
                     (?a0 a1.
                        a0' =
                        (\a0 a1.
                           CONSTR (SUC 0)
                             (a1,a0,(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1) \/
                     (?a0 a1.
                        a0' =
                        (\a0 a1.
                           CONSTR (SUC (SUC 0))
                             (a0,(@v. T),a1,(@v. T),(@v. T),(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR (SUC (SUC (SUC 0)))
                             (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR (SUC (SUC (SUC (SUC 0))))
                             (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR (SUC (SUC (SUC (SUC (SUC 0)))))
                             (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR (SUC (SUC (SUC (SUC (SUC (SUC 0))))))
                             (a0,(@v. T),(@v. T),a1,a2,(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))
                             (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))
                             (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR
                             (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))
                             (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))
                             (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC (SUC (SUC (SUC (SUC 0)))))))))))
                             (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC (SUC (SUC 0))))))))))))
                             (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1 a2.
                        a0' =
                        (\a0 a1 a2.
                           CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              (SUC
                                                                 (SUC 0)))))))))))))
                             (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T)
                             (\n. BOTTOM)) a0 a1 a2) \/
                     (?a0 a1.
                        a0' =
                        (\a0 a1.
                           CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              (SUC
                                                                 (SUC
                                                                    (SUC
                                                                       0))))))))))))))
                             ((@v. T),(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),a0,a1)
                             (\n. BOTTOM)) a0 a1) \/
                     (?a0 a1.
                        a0' =
                        (\a0 a1.
                           CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              (SUC
                                                                 (SUC
                                                                    (SUC
                                                                       (SUC
                                                                          0)))))))))))))))
                             ((@v. T),(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),a0,a1)
                             (\n. BOTTOM)) a0 a1) ==>
                     'DOPER' a0') ==>
                  'DOPER' a0') rep

   [DOPER_case_def]  Definition

      |- (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MLDR a0 a1) =
            f a0 a1) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MSTR a0 a1) =
            f1 a0 a1) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MMOV a0 a1) =
            f2 a0 a1) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MADD a0 a1 a2) =
            f3 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MSUB a0 a1 a2) =
            f4 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MRSB a0 a1 a2) =
            f5 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MMUL a0 a1 a2) =
            f6 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MAND a0 a1 a2) =
            f7 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MORR a0 a1 a2) =
            f8 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MEOR a0 a1 a2) =
            f9 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MLSL a0 a1 a2) =
            f10 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MLSR a0 a1 a2) =
            f11 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MASR a0 a1 a2) =
            f12 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1 a2.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MROR a0 a1 a2) =
            f13 a0 a1 a2) /\
         (!f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1.
            DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
              (MPUSH a0 a1) =
            f14 a0 a1) /\
         !f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 a0 a1.
           DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
             (MPOP a0 a1) =
           f15 a0 a1

   [DOPER_repfns]  Definition

      |- (!a. mk_DOPER (dest_DOPER a) = a) /\
         !r.
           (\a0'.
              !'DOPER'.
                (!a0'.
                   (?a0 a1.
                      a0' =
                      (\a0 a1.
                         CONSTR 0
                           (a0,a1,(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1) \/
                   (?a0 a1.
                      a0' =
                      (\a0 a1.
                         CONSTR (SUC 0)
                           (a1,a0,(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1) \/
                   (?a0 a1.
                      a0' =
                      (\a0 a1.
                         CONSTR (SUC (SUC 0))
                           (a0,(@v. T),a1,(@v. T),(@v. T),(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR (SUC (SUC (SUC 0)))
                           (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR (SUC (SUC (SUC (SUC 0))))
                           (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR (SUC (SUC (SUC (SUC (SUC 0)))))
                           (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR (SUC (SUC (SUC (SUC (SUC (SUC 0))))))
                           (a0,(@v. T),(@v. T),a1,a2,(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))
                           (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))
                           (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR
                           (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))
                           (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR
                           (SUC
                              (SUC
                                 (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))
                           (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR
                           (SUC
                              (SUC
                                 (SUC
                                    (SUC
                                       (SUC
                                          (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))))
                           (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR
                           (SUC
                              (SUC
                                 (SUC
                                    (SUC
                                       (SUC
                                          (SUC
                                             (SUC
                                                (SUC
                                                   (SUC (SUC (SUC (SUC 0))))))))))))
                           (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1 a2.
                      a0' =
                      (\a0 a1 a2.
                         CONSTR
                           (SUC
                              (SUC
                                 (SUC
                                    (SUC
                                       (SUC
                                          (SUC
                                             (SUC
                                                (SUC
                                                   (SUC
                                                      (SUC
                                                         (SUC
                                                            (SUC (SUC 0)))))))))))))
                           (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T)
                           (\n. BOTTOM)) a0 a1 a2) \/
                   (?a0 a1.
                      a0' =
                      (\a0 a1.
                         CONSTR
                           (SUC
                              (SUC
                                 (SUC
                                    (SUC
                                       (SUC
                                          (SUC
                                             (SUC
                                                (SUC
                                                   (SUC
                                                      (SUC
                                                         (SUC
                                                            (SUC
                                                               (SUC
                                                                  (SUC
                                                                     0))))))))))))))
                           ((@v. T),(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),a0,a1)
                           (\n. BOTTOM)) a0 a1) \/
                   (?a0 a1.
                      a0' =
                      (\a0 a1.
                         CONSTR
                           (SUC
                              (SUC
                                 (SUC
                                    (SUC
                                       (SUC
                                          (SUC
                                             (SUC
                                                (SUC
                                                   (SUC
                                                      (SUC
                                                         (SUC
                                                            (SUC
                                                               (SUC
                                                                  (SUC
                                                                     (SUC
                                                                        0)))))))))))))))
                           ((@v. T),(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),a0,a1)
                           (\n. BOTTOM)) a0 a1) ==>
                   'DOPER' a0') ==>
                'DOPER' a0') r =
           (dest_DOPER (mk_DOPER r) = r)

   [DOPER_size_def]  Definition

      |- (!a0 a1.
            DOPER_size (MLDR a0 a1) =
            1 + (MREG_size a0 + (\(x,y). (\x. x) x + OFFSET_size y) a1)) /\
         (!a0 a1.
            DOPER_size (MSTR a0 a1) =
            1 + ((\(x,y). (\x. x) x + OFFSET_size y) a0 + MREG_size a1)) /\
         (!a0 a1. DOPER_size (MMOV a0 a1) = 1 + (MREG_size a0 + MEXP_size a1)) /\
         (!a0 a1 a2.
            DOPER_size (MADD a0 a1 a2) =
            1 + (MREG_size a0 + (MREG_size a1 + MEXP_size a2))) /\
         (!a0 a1 a2.
            DOPER_size (MSUB a0 a1 a2) =
            1 + (MREG_size a0 + (MREG_size a1 + MEXP_size a2))) /\
         (!a0 a1 a2.
            DOPER_size (MRSB a0 a1 a2) =
            1 + (MREG_size a0 + (MREG_size a1 + MEXP_size a2))) /\
         (!a0 a1 a2.
            DOPER_size (MMUL a0 a1 a2) =
            1 + (MREG_size a0 + (MREG_size a1 + MREG_size a2))) /\
         (!a0 a1 a2.
            DOPER_size (MAND a0 a1 a2) =
            1 + (MREG_size a0 + (MREG_size a1 + MEXP_size a2))) /\
         (!a0 a1 a2.
            DOPER_size (MORR a0 a1 a2) =
            1 + (MREG_size a0 + (MREG_size a1 + MEXP_size a2))) /\
         (!a0 a1 a2.
            DOPER_size (MEOR a0 a1 a2) =
            1 + (MREG_size a0 + (MREG_size a1 + MEXP_size a2))) /\
         (!a0 a1 a2.
            DOPER_size (MLSL a0 a1 a2) = 1 + (MREG_size a0 + MREG_size a1)) /\
         (!a0 a1 a2.
            DOPER_size (MLSR a0 a1 a2) = 1 + (MREG_size a0 + MREG_size a1)) /\
         (!a0 a1 a2.
            DOPER_size (MASR a0 a1 a2) = 1 + (MREG_size a0 + MREG_size a1)) /\
         (!a0 a1 a2.
            DOPER_size (MROR a0 a1 a2) = 1 + (MREG_size a0 + MREG_size a1)) /\
         (!a0 a1. DOPER_size (MPUSH a0 a1) = 1 + (a0 + list_size (\x. x) a1)) /\
         !a0 a1. DOPER_size (MPOP a0 a1) = 1 + (a0 + list_size (\x. x) a1)

   [IL0_def]  Definition

      |- IL0 = (\a. mk_MEXP ((\a. CONSTR 0 (a,(@v. T),@v. T) (\n. BOTTOM)) a))

   [IL10_def]  Definition

      |- IL10 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))
                    (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL11_def]  Definition

      |- IL11 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))
                    (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL12_def]  Definition

      |- IL12 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR
                    (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))
                    (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL13_def]  Definition

      |- IL13 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR
                    (SUC
                       (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))))
                    (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL14_def]  Definition

      |- IL14 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR
                    (SUC
                       (SUC
                          (SUC
                             (SUC
                                (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))))
                    (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL15_def]  Definition

      |- IL15 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR
                    (SUC
                       (SUC
                          (SUC
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))))))
                    (a0,(@v. T),(@v. T),a1,(@v. T),a2,(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL16_def]  Definition

      |- IL16 =
         (\a0 a1.
            mk_DOPER
              ((\a0 a1.
                  CONSTR
                    (SUC
                       (SUC
                          (SUC
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC (SUC (SUC (SUC 0))))))))))))))
                    ((@v. T),(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),a0,a1)
                    (\n. BOTTOM)) a0 a1))

   [IL17_def]  Definition

      |- IL17 =
         (\a0 a1.
            mk_DOPER
              ((\a0 a1.
                  CONSTR
                    (SUC
                       (SUC
                          (SUC
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC (SUC 0)))))))))))))))
                    ((@v. T),(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),a0,a1)
                    (\n. BOTTOM)) a0 a1))

   [IL18_def]  Definition

      |- IL18 = (\a. mk_CTL_STRUCTURE ((\a. CONSTR 0 (a,@v. T) (\n. BOTTOM)) a))

   [IL19_def]  Definition

      |- IL19 =
         (\a0 a1.
            mk_CTL_STRUCTURE
              ((\a0 a1.
                  CONSTR (SUC 0) ((@v. T),@v. T) (FCONS a0 (FCONS a1 (\n. BOTTOM))))
                 (dest_CTL_STRUCTURE a0) (dest_CTL_STRUCTURE a1)))

   [IL1_def]  Definition

      |- IL1 =
         (\a0 a1.
            mk_MEXP ((\a0 a1. CONSTR (SUC 0) ((@v. T),a0,a1) (\n. BOTTOM)) a0 a1))

   [IL20_def]  Definition

      |- IL20 =
         (\a0 a1 a2.
            mk_CTL_STRUCTURE
              ((\a0 a1 a2.
                  CONSTR (SUC (SUC 0)) ((@v. T),a0)
                    (FCONS a1 (FCONS a2 (\n. BOTTOM)))) a0 (dest_CTL_STRUCTURE a1)
                 (dest_CTL_STRUCTURE a2)))

   [IL21_def]  Definition

      |- IL21 =
         (\a0 a1.
            mk_CTL_STRUCTURE
              ((\a0 a1.
                  CONSTR (SUC (SUC (SUC 0))) ((@v. T),a0) (FCONS a1 (\n. BOTTOM))) a0
                 (dest_CTL_STRUCTURE a1)))

   [IL2_def]  Definition

      |- IL2 =
         (\a0 a1.
            mk_DOPER
              ((\a0 a1.
                  CONSTR 0 (a0,a1,(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),@v. T)
                    (\n. BOTTOM)) a0 a1))

   [IL3_def]  Definition

      |- IL3 =
         (\a0 a1.
            mk_DOPER
              ((\a0 a1.
                  CONSTR (SUC 0)
                    (a1,a0,(@v. T),(@v. T),(@v. T),(@v. T),(@v. T),@v. T)
                    (\n. BOTTOM)) a0 a1))

   [IL4_def]  Definition

      |- IL4 =
         (\a0 a1.
            mk_DOPER
              ((\a0 a1.
                  CONSTR (SUC (SUC 0))
                    (a0,(@v. T),a1,(@v. T),(@v. T),(@v. T),(@v. T),@v. T)
                    (\n. BOTTOM)) a0 a1))

   [IL5_def]  Definition

      |- IL5 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR (SUC (SUC (SUC 0)))
                    (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL6_def]  Definition

      |- IL6 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR (SUC (SUC (SUC (SUC 0))))
                    (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL7_def]  Definition

      |- IL7 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR (SUC (SUC (SUC (SUC (SUC 0)))))
                    (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL8_def]  Definition

      |- IL8 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR (SUC (SUC (SUC (SUC (SUC (SUC 0))))))
                    (a0,(@v. T),(@v. T),a1,a2,(@v. T),(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [IL9_def]  Definition

      |- IL9 =
         (\a0 a1 a2.
            mk_DOPER
              ((\a0 a1 a2.
                  CONSTR (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))
                    (a0,(@v. T),a2,a1,(@v. T),(@v. T),(@v. T),@v. T) (\n. BOTTOM)) a0
                 a1 a2))

   [MADD]  Definition

      |- MADD = IL5

   [MAND]  Definition

      |- MAND = IL9

   [MASR]  Definition

      |- MASR = IL14

   [MC]  Definition

      |- MC = IL1

   [MEOR]  Definition

      |- MEOR = IL11

   [MEXP_TY_DEF]  Definition

      |- ?rep.
           TYPE_DEFINITION
             (\a0'.
                !'MEXP'.
                  (!a0'.
                     (?a. a0' = (\a. CONSTR 0 (a,(@v. T),@v. T) (\n. BOTTOM)) a) \/
                     (?a0 a1.
                        a0' =
                        (\a0 a1. CONSTR (SUC 0) ((@v. T),a0,a1) (\n. BOTTOM)) a0
                          a1) ==>
                     'MEXP' a0') ==>
                  'MEXP' a0') rep

   [MEXP_case_def]  Definition

      |- (!f f1 a. MEXP_case f f1 (MR a) = f a) /\
         !f f1 a0 a1. MEXP_case f f1 (MC a0 a1) = f1 a0 a1

   [MEXP_repfns]  Definition

      |- (!a. mk_MEXP (dest_MEXP a) = a) /\
         !r.
           (\a0'.
              !'MEXP'.
                (!a0'.
                   (?a. a0' = (\a. CONSTR 0 (a,(@v. T),@v. T) (\n. BOTTOM)) a) \/
                   (?a0 a1.
                      a0' =
                      (\a0 a1. CONSTR (SUC 0) ((@v. T),a0,a1) (\n. BOTTOM)) a0
                        a1) ==>
                   'MEXP' a0') ==>
                'MEXP' a0') r =
           (dest_MEXP (mk_MEXP r) = r)

   [MEXP_size_def]  Definition

      |- (!a. MEXP_size (MR a) = 1 + MREG_size a) /\ !a0 a1. MEXP_size (MC a0 a1) = 1

   [MLDR]  Definition

      |- MLDR = IL2

   [MLSL]  Definition

      |- MLSL = IL12

   [MLSR]  Definition

      |- MLSR = IL13

   [MMOV]  Definition

      |- MMOV = IL4

   [MMUL]  Definition

      |- MMUL = IL8

   [MORR]  Definition

      |- MORR = IL10

   [MPOP]  Definition

      |- MPOP = IL17

   [MPUSH]  Definition

      |- MPUSH = IL16

   [MR]  Definition

      |- MR = IL0

   [MREG_BIJ]  Definition

      |- (!a. num2MREG (MREG2num a) = a) /\
         !r. (\n. n < 15) r = (MREG2num (num2MREG r) = r)

   [MREG_TY_DEF]  Definition

      |- ?rep. TYPE_DEFINITION (\n. n < 15) rep

   [MREG_case]  Definition

      |- !v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 x.
           (case x of
               R0 -> v0
            || R1 -> v1
            || R2 -> v2
            || R3 -> v3
            || R4 -> v4
            || R5 -> v5
            || R6 -> v6
            || R7 -> v7
            || R8 -> v8
            || R9 -> v9
            || R10 -> v10
            || R11 -> v11
            || R12 -> v12
            || R13 -> v13
            || R14 -> v14) =
           (\m.
              (if m < 7 then
                 (if m < 3 then
                    (if m < 1 then v0 else (if m = 1 then v1 else v2))
                  else
                    (if m < 4 then
                       v3
                     else
                       (if m < 5 then v4 else (if m = 5 then v5 else v6))))
               else
                 (if m < 10 then
                    (if m < 8 then v7 else (if m = 8 then v8 else v9))
                  else
                    (if m < 12 then
                       (if m = 10 then v10 else v11)
                     else
                       (if m < 13 then v12 else (if m = 13 then v13 else v14))))))
             (MREG2num x)

   [MREG_size_def]  Definition

      |- !x. MREG_size x = 0

   [MROR]  Definition

      |- MROR = IL15

   [MRSB]  Definition

      |- MRSB = IL7

   [MSTR]  Definition

      |- MSTR = IL3

   [MSUB]  Definition

      |- MSUB = IL6

   [R0]  Definition

      |- R0 = num2MREG 0

   [R1]  Definition

      |- R1 = num2MREG 1

   [R10]  Definition

      |- R10 = num2MREG 10

   [R11]  Definition

      |- R11 = num2MREG 11

   [R12]  Definition

      |- R12 = num2MREG 12

   [R13]  Definition

      |- R13 = num2MREG 13

   [R14]  Definition

      |- R14 = num2MREG 14

   [R2]  Definition

      |- R2 = num2MREG 2

   [R3]  Definition

      |- R3 = num2MREG 3

   [R4]  Definition

      |- R4 = num2MREG 4

   [R5]  Definition

      |- R5 = num2MREG 5

   [R6]  Definition

      |- R6 = num2MREG 6

   [R7]  Definition

      |- R7 = num2MREG 7

   [R8]  Definition

      |- R8 = num2MREG 8

   [R9]  Definition

      |- R9 = num2MREG 9

   [SC]  Definition

      |- SC = IL19

   [TR]  Definition

      |- TR = IL21

   [WELL_FORMED_SUB_def]  Definition

      |- (!stmL. WELL_FORMED_SUB (BLK stmL) = T) /\
         (!S1 S2. WELL_FORMED_SUB (SC S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
         (!cond S1 S2.
            WELL_FORMED_SUB (CJ cond S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
         !cond S1.
           WELL_FORMED_SUB (TR cond S1) =
           WELL_FORMED S1 /\ WF_TR (translate_condition cond,translate S1)

   [WELL_FORMED_def]  Definition

      |- (!stmL. WELL_FORMED (BLK stmL) = well_formed (translate (BLK stmL))) /\
         (!S1 S2.
            WELL_FORMED (SC S1 S2) =
            well_formed (translate (SC S1 S2)) /\ WELL_FORMED S1 /\
            WELL_FORMED S2) /\
         (!cond S1 S2.
            WELL_FORMED (CJ cond S1 S2) =
            well_formed (translate (CJ cond S1 S2)) /\ WELL_FORMED S1 /\
            WELL_FORMED S2) /\
         !cond S1.
           WELL_FORMED (TR cond S1) =
           well_formed (translate (TR cond S1)) /\ WELL_FORMED S1 /\
           WF_TR (translate_condition cond,translate S1)

   [eval_il_cond_def]  Definition

      |- !cond. eval_il_cond cond = eval_cond (translate_condition cond)

   [from_reg_index_def]  Definition

      |- !i.
           from_reg_index i =
           (if i = 0 then
              R0
            else
              (if i = 1 then
                 R1
               else
                 (if i = 2 then
                    R2
                  else
                    (if i = 3 then
                       R3
                     else
                       (if i = 4 then
                          R4
                        else
                          (if i = 5 then
                             R5
                           else
                             (if i = 6 then
                                R6
                              else
                                (if i = 7 then
                                   R7
                                 else
                                   (if i = 8 then
                                      R8
                                    else
                                      (if i = 9 then
                                         R9
                                       else
                                         (if i = 10 then
                                            R10
                                          else
                                            (if i = 11 then
                                               R11
                                             else
                                               (if i = 12 then
                                                  R12
                                                else
                                                  (if i = 13 then
                                                     R13
                                                   else
                                                     R14))))))))))))))

   [index_of_reg_def]  Definition

      |- (index_of_reg R0 = 0) /\ (index_of_reg R1 = 1) /\ (index_of_reg R2 = 2) /\
         (index_of_reg R3 = 3) /\ (index_of_reg R4 = 4) /\ (index_of_reg R5 = 5) /\
         (index_of_reg R6 = 6) /\ (index_of_reg R7 = 7) /\ (index_of_reg R8 = 8) /\
         (index_of_reg R9 = 9) /\ (index_of_reg R10 = 10) /\
         (index_of_reg R11 = 11) /\ (index_of_reg R12 = 12) /\
         (index_of_reg R13 = 13) /\ (index_of_reg R14 = 14)

   [mdecode_def]  Definition

      |- (!st dst src.
            mdecode st (MLDR dst src) =
            write st (toREG dst) (read st (toMEM src))) /\
         (!st dst src.
            mdecode st (MSTR dst src) =
            write st (toMEM dst) (read st (toREG src))) /\
         (!st dst src.
            mdecode st (MMOV dst src) =
            write st (toREG dst) (read st (toEXP src))) /\
         (!st dst src1 src2.
            mdecode st (MADD dst src1 src2) =
            write st (toREG dst) (read st (toREG src1) + read st (toEXP src2))) /\
         (!st dst src1 src2.
            mdecode st (MSUB dst src1 src2) =
            write st (toREG dst) (read st (toREG src1) - read st (toEXP src2))) /\
         (!st dst src1 src2.
            mdecode st (MRSB dst src1 src2) =
            write st (toREG dst) (read st (toEXP src2) - read st (toREG src1))) /\
         (!st dst src1 src2_reg.
            mdecode st (MMUL dst src1 src2_reg) =
            write st (toREG dst)
              (read st (toREG src1) * read st (toREG src2_reg))) /\
         (!st dst src1 src2.
            mdecode st (MAND dst src1 src2) =
            write st (toREG dst) (read st (toREG src1) && read st (toEXP src2))) /\
         (!st dst src1 src2.
            mdecode st (MORR dst src1 src2) =
            write st (toREG dst) (read st (toREG src1) !! read st (toEXP src2))) /\
         (!st dst src1 src2.
            mdecode st (MEOR dst src1 src2) =
            write st (toREG dst) (read st (toREG src1) ?? read st (toEXP src2))) /\
         (!st dst src2_reg src2_num.
            mdecode st (MLSL dst src2_reg src2_num) =
            write st (toREG dst) (read st (toREG src2_reg) << w2n src2_num)) /\
         (!st dst src2_reg src2_num.
            mdecode st (MLSR dst src2_reg src2_num) =
            write st (toREG dst) (read st (toREG src2_reg) >>> w2n src2_num)) /\
         (!st dst src2_reg src2_num.
            mdecode st (MASR dst src2_reg src2_num) =
            write st (toREG dst) (read st (toREG src2_reg) >> w2n src2_num)) /\
         (!st dst src2_reg src2_num.
            mdecode st (MROR dst src2_reg src2_num) =
            write st (toREG dst) (read st (toREG src2_reg) #>> w2n src2_num)) /\
         (!st dst' srcL. mdecode st (MPUSH dst' srcL) = pushL st dst' srcL) /\
         !st dst' srcL. mdecode st (MPOP dst' srcL) = popL st dst' srcL

   [popL_def]  Definition

      |- !st baseR regL.
           popL st baseR regL =
           write
             (FST
                (FOLDL
                   (\(st1,i) reg.
                      (write st1 reg (read st (MEM (baseR,POS (i + 1)))),i + 1))
                   (st,0) (MAP REG regL))) (REG baseR)
             (read st (REG baseR) + n2w (LENGTH regL))

   [pushL_def]  Definition

      |- !st baseR regL.
           pushL st baseR regL =
           write
             (FST
                (FOLDL
                   (\(st1,i) reg.
                      (write st1 (MEM (baseR,NEG i)) (read st reg),i + 1)) (st,0)
                   (REVERSE (MAP REG regL)))) (REG baseR)
             (read st (REG baseR) - n2w (LENGTH regL))

   [run_arm_def]  Definition

      |- !arm pc cpsr st pcS.
           run_arm arm ((pc,cpsr,st),pcS) =
           runTo (upload arm (\i. ARB) pc) (pc + LENGTH arm) ((pc,cpsr,st),pcS)

   [run_ir_def]  Definition

      |- !ir st. run_ir ir st = get_st (run_arm (translate ir) ((0,0w,st),{}))

   [toEXP_def]  Definition

      |- (!r. toEXP (MR r) = toREG r) /\
         !shift c. toEXP (MC shift c) = WCONST (w2w c #>> (2 * w2n shift))

   [toMEM_def]  Definition

      |- !base offset. toMEM (base,offset) = MEM (base,offset)

   [toREG_def]  Definition

      |- !r. toREG r = REG (index_of_reg r)

   [translate_assignment_def]  Definition

      |- (!dst src.
            translate_assignment (MMOV dst src) =
            ((MOV,NONE,F),SOME (toREG dst),[toEXP src],NONE)) /\
         (!dst src1 src2.
            translate_assignment (MADD dst src1 src2) =
            ((ADD,NONE,F),SOME (toREG dst),[toREG src1; toEXP src2],NONE)) /\
         (!dst src1 src2.
            translate_assignment (MSUB dst src1 src2) =
            ((SUB,NONE,F),SOME (toREG dst),[toREG src1; toEXP src2],NONE)) /\
         (!dst src1 src2.
            translate_assignment (MRSB dst src1 src2) =
            ((RSB,NONE,F),SOME (toREG dst),[toREG src1; toEXP src2],NONE)) /\
         (!dst src1 src2_reg.
            translate_assignment (MMUL dst src1 src2_reg) =
            ((MUL,NONE,F),SOME (toREG dst),[toREG src1; toREG src2_reg],NONE)) /\
         (!dst src1 src2.
            translate_assignment (MAND dst src1 src2) =
            ((AND,NONE,F),SOME (toREG dst),[toREG src1; toEXP src2],NONE)) /\
         (!dst src1 src2.
            translate_assignment (MORR dst src1 src2) =
            ((ORR,NONE,F),SOME (toREG dst),[toREG src1; toEXP src2],NONE)) /\
         (!dst src1 src2.
            translate_assignment (MEOR dst src1 src2) =
            ((EOR,NONE,F),SOME (toREG dst),[toREG src1; toEXP src2],NONE)) /\
         (!dst src2_reg src2_num.
            translate_assignment (MLSL dst src2_reg src2_num) =
            ((LSL,NONE,F),SOME (toREG dst),[toREG src2_reg; WCONST (w2w src2_num)],
             NONE)) /\
         (!dst src2_reg src2_num.
            translate_assignment (MLSR dst src2_reg src2_num) =
            ((LSR,NONE,F),SOME (toREG dst),[toREG src2_reg; WCONST (w2w src2_num)],
             NONE)) /\
         (!dst src2_reg src2_num.
            translate_assignment (MASR dst src2_reg src2_num) =
            ((ASR,NONE,F),SOME (toREG dst),[toREG src2_reg; WCONST (w2w src2_num)],
             NONE)) /\
         (!dst src2_reg src2_num.
            translate_assignment (MROR dst src2_reg src2_num) =
            ((ROR,NONE,F),SOME (toREG dst),[toREG src2_reg; WCONST (w2w src2_num)],
             NONE)) /\
         (!dst src.
            translate_assignment (MLDR dst src) =
            ((LDR,NONE,F),SOME (toREG dst),[toMEM src],NONE)) /\
         (!dst src.
            translate_assignment (MSTR dst src) =
            ((STR,NONE,F),SOME (toREG src),[toMEM dst],NONE)) /\
         (!dst srcL.
            translate_assignment (MPUSH dst srcL) =
            ((STMFD,NONE,F),SOME (WREG dst),MAP REG srcL,NONE)) /\
         !dst srcL.
           translate_assignment (MPOP dst srcL) =
           ((LDMFD,NONE,F),SOME (WREG dst),MAP REG srcL,NONE)

   [translate_condition_def]  Definition

      |- !r c e. translate_condition (r,c,e) = (toREG r,c,toEXP e)

   [translate_primitive_def]  Definition

      |- translate =
         WFREC
           (@R.
              WF R /\ (!stm stmL. R (BLK stmL) (BLK (stm::stmL))) /\
              (!S1 S2. R S2 (SC S1 S2)) /\ (!S2 S1. R S1 (SC S1 S2)) /\
              (!Sfalse cond Strue. R Strue (CJ cond Strue Sfalse)) /\
              (!Strue cond Sfalse. R Sfalse (CJ cond Strue Sfalse)) /\
              !cond Sbody. R Sbody (TR cond Sbody))
           (\translate a.
              case a of
                 BLK [] -> I []
              || BLK (stm::stmL) ->
                   I (translate_assignment stm::translate (BLK stmL))
              || SC S1 S2 -> I (mk_SC (translate S1) (translate S2))
              || CJ cond Strue Sfalse ->
                   I
                     (mk_CJ (translate_condition cond) (translate Strue)
                        (translate Sfalse))
              || TR cond' Sbody ->
                   I (mk_TR (translate_condition cond') (translate Sbody)))

   [BLOCK_IS_WELL_FORMED]  Theorem

      |- !stmL. WELL_FORMED (BLK stmL)

   [CTL_STRUCTURE_11]  Theorem

      |- (!a a'. (BLK a = BLK a') = (a = a')) /\
         (!a0 a1 a0' a1'. (SC a0 a1 = SC a0' a1') = (a0 = a0') /\ (a1 = a1')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (CJ a0 a1 a2 = CJ a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         !a0 a1 a0' a1'. (TR a0 a1 = TR a0' a1') = (a0 = a0') /\ (a1 = a1')

   [CTL_STRUCTURE_Axiom]  Theorem

      |- !f0 f1 f2 f3.
           ?fn.
             (!a. fn (BLK a) = f0 a) /\
             (!a0 a1. fn (SC a0 a1) = f1 a0 a1 (fn a0) (fn a1)) /\
             (!a0 a1 a2. fn (CJ a0 a1 a2) = f2 a0 a1 a2 (fn a1) (fn a2)) /\
             !a0 a1. fn (TR a0 a1) = f3 a0 a1 (fn a1)

   [CTL_STRUCTURE_case_cong]  Theorem

      |- !M M' f f1 f2 f3.
           (M = M') /\ (!a. (M' = BLK a) ==> (f a = f' a)) /\
           (!a0 a1. (M' = SC a0 a1) ==> (f1 a0 a1 = f1' a0 a1)) /\
           (!a0 a1 a2. (M' = CJ a0 a1 a2) ==> (f2 a0 a1 a2 = f2' a0 a1 a2)) /\
           (!a0 a1. (M' = TR a0 a1) ==> (f3 a0 a1 = f3' a0 a1)) ==>
           (CTL_STRUCTURE_case f f1 f2 f3 M = CTL_STRUCTURE_case f' f1' f2' f3' M')

   [CTL_STRUCTURE_distinct]  Theorem

      |- (!a1 a0 a. ~(BLK a = SC a0 a1)) /\ (!a2 a1 a0 a. ~(BLK a = CJ a0 a1 a2)) /\
         (!a1 a0 a. ~(BLK a = TR a0 a1)) /\
         (!a2 a1' a1 a0' a0. ~(SC a0 a1 = CJ a0' a1' a2)) /\
         (!a1' a1 a0' a0. ~(SC a0 a1 = TR a0' a1')) /\
         !a2 a1' a1 a0' a0. ~(CJ a0 a1 a2 = TR a0' a1')

   [CTL_STRUCTURE_induction]  Theorem

      |- !P.
           (!l. P (BLK l)) /\ (!C C0. P C /\ P C0 ==> P (SC C C0)) /\
           (!C C0. P C /\ P C0 ==> !p. P (CJ p C C0)) /\
           (!C. P C ==> !p. P (TR p C)) ==>
           !C. P C

   [CTL_STRUCTURE_nchotomy]  Theorem

      |- !C.
           (?l. C = BLK l) \/ (?C' C0. C = SC C' C0) \/ (?p C' C0. C = CJ p C' C0) \/
           ?p C'. C = TR p C'

   [DOPER_11]  Theorem

      |- (!a0 a1 a0' a1'. (MLDR a0 a1 = MLDR a0' a1') = (a0 = a0') /\ (a1 = a1')) /\
         (!a0 a1 a0' a1'. (MSTR a0 a1 = MSTR a0' a1') = (a0 = a0') /\ (a1 = a1')) /\
         (!a0 a1 a0' a1'. (MMOV a0 a1 = MMOV a0' a1') = (a0 = a0') /\ (a1 = a1')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MADD a0 a1 a2 = MADD a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MSUB a0 a1 a2 = MSUB a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MRSB a0 a1 a2 = MRSB a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MMUL a0 a1 a2 = MMUL a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MAND a0 a1 a2 = MAND a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MORR a0 a1 a2 = MORR a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MEOR a0 a1 a2 = MEOR a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MLSL a0 a1 a2 = MLSL a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MLSR a0 a1 a2 = MLSR a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MASR a0 a1 a2 = MASR a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a2 a0' a1' a2'.
            (MROR a0 a1 a2 = MROR a0' a1' a2') =
            (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')) /\
         (!a0 a1 a0' a1'.
            (MPUSH a0 a1 = MPUSH a0' a1') = (a0 = a0') /\ (a1 = a1')) /\
         !a0 a1 a0' a1'. (MPOP a0 a1 = MPOP a0' a1') = (a0 = a0') /\ (a1 = a1')

   [DOPER_Axiom]  Theorem

      |- !f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15.
           ?fn.
             (!a0 a1. fn (MLDR a0 a1) = f0 a0 a1) /\
             (!a0 a1. fn (MSTR a0 a1) = f1 a0 a1) /\
             (!a0 a1. fn (MMOV a0 a1) = f2 a0 a1) /\
             (!a0 a1 a2. fn (MADD a0 a1 a2) = f3 a0 a1 a2) /\
             (!a0 a1 a2. fn (MSUB a0 a1 a2) = f4 a0 a1 a2) /\
             (!a0 a1 a2. fn (MRSB a0 a1 a2) = f5 a0 a1 a2) /\
             (!a0 a1 a2. fn (MMUL a0 a1 a2) = f6 a0 a1 a2) /\
             (!a0 a1 a2. fn (MAND a0 a1 a2) = f7 a0 a1 a2) /\
             (!a0 a1 a2. fn (MORR a0 a1 a2) = f8 a0 a1 a2) /\
             (!a0 a1 a2. fn (MEOR a0 a1 a2) = f9 a0 a1 a2) /\
             (!a0 a1 a2. fn (MLSL a0 a1 a2) = f10 a0 a1 a2) /\
             (!a0 a1 a2. fn (MLSR a0 a1 a2) = f11 a0 a1 a2) /\
             (!a0 a1 a2. fn (MASR a0 a1 a2) = f12 a0 a1 a2) /\
             (!a0 a1 a2. fn (MROR a0 a1 a2) = f13 a0 a1 a2) /\
             (!a0 a1. fn (MPUSH a0 a1) = f14 a0 a1) /\
             !a0 a1. fn (MPOP a0 a1) = f15 a0 a1

   [DOPER_case_cong]  Theorem

      |- !M M' f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15.
           (M = M') /\ (!a0 a1. (M' = MLDR a0 a1) ==> (f a0 a1 = f' a0 a1)) /\
           (!a0 a1. (M' = MSTR a0 a1) ==> (f1 a0 a1 = f1' a0 a1)) /\
           (!a0 a1. (M' = MMOV a0 a1) ==> (f2 a0 a1 = f2' a0 a1)) /\
           (!a0 a1 a2. (M' = MADD a0 a1 a2) ==> (f3 a0 a1 a2 = f3' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MSUB a0 a1 a2) ==> (f4 a0 a1 a2 = f4' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MRSB a0 a1 a2) ==> (f5 a0 a1 a2 = f5' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MMUL a0 a1 a2) ==> (f6 a0 a1 a2 = f6' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MAND a0 a1 a2) ==> (f7 a0 a1 a2 = f7' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MORR a0 a1 a2) ==> (f8 a0 a1 a2 = f8' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MEOR a0 a1 a2) ==> (f9 a0 a1 a2 = f9' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MLSL a0 a1 a2) ==> (f10 a0 a1 a2 = f10' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MLSR a0 a1 a2) ==> (f11 a0 a1 a2 = f11' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MASR a0 a1 a2) ==> (f12 a0 a1 a2 = f12' a0 a1 a2)) /\
           (!a0 a1 a2. (M' = MROR a0 a1 a2) ==> (f13 a0 a1 a2 = f13' a0 a1 a2)) /\
           (!a0 a1. (M' = MPUSH a0 a1) ==> (f14 a0 a1 = f14' a0 a1)) /\
           (!a0 a1. (M' = MPOP a0 a1) ==> (f15 a0 a1 = f15' a0 a1)) ==>
           (DOPER_case f f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 M =
            DOPER_case f' f1' f2' f3' f4' f5' f6' f7' f8' f9' f10' f11' f12' f13'
              f14' f15' M')

   [DOPER_distinct]  Theorem

      |- (!a1' a1 a0' a0. ~(MLDR a0 a1 = MSTR a0' a1')) /\
         (!a1' a1 a0' a0. ~(MLDR a0 a1 = MMOV a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MADD a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MSUB a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MRSB a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MMUL a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MAND a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MORR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MEOR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MLSL a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MLSR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MASR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MLDR a0 a1 = MROR a0' a1' a2)) /\
         (!a1' a1 a0' a0. ~(MLDR a0 a1 = MPUSH a0' a1')) /\
         (!a1' a1 a0' a0. ~(MLDR a0 a1 = MPOP a0' a1')) /\
         (!a1' a1 a0' a0. ~(MSTR a0 a1 = MMOV a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MADD a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MSUB a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MRSB a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MMUL a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MAND a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MORR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MEOR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MLSL a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MLSR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MASR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MSTR a0 a1 = MROR a0' a1' a2)) /\
         (!a1' a1 a0' a0. ~(MSTR a0 a1 = MPUSH a0' a1')) /\
         (!a1' a1 a0' a0. ~(MSTR a0 a1 = MPOP a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MADD a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MSUB a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MRSB a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MMUL a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MAND a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MORR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MEOR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MLSL a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MLSR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MASR a0' a1' a2)) /\
         (!a2 a1' a1 a0' a0. ~(MMOV a0 a1 = MROR a0' a1' a2)) /\
         (!a1' a1 a0' a0. ~(MMOV a0 a1 = MPUSH a0' a1')) /\
         (!a1' a1 a0' a0. ~(MMOV a0 a1 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MSUB a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MRSB a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MMUL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MAND a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MORR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MEOR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MLSL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MLSR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MASR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MADD a0 a1 a2 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MRSB a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MMUL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MAND a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MORR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MEOR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MLSL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MLSR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MASR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MSUB a0 a1 a2 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MMUL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MAND a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MORR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MEOR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MLSL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MLSR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MASR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MRSB a0 a1 a2 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MMUL a0 a1 a2 = MAND a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MMUL a0 a1 a2 = MORR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MMUL a0 a1 a2 = MEOR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MMUL a0 a1 a2 = MLSL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MMUL a0 a1 a2 = MLSR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MMUL a0 a1 a2 = MASR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MMUL a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MMUL a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MMUL a0 a1 a2 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MAND a0 a1 a2 = MORR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MAND a0 a1 a2 = MEOR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MAND a0 a1 a2 = MLSL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MAND a0 a1 a2 = MLSR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MAND a0 a1 a2 = MASR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MAND a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MAND a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MAND a0 a1 a2 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MORR a0 a1 a2 = MEOR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MORR a0 a1 a2 = MLSL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MORR a0 a1 a2 = MLSR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MORR a0 a1 a2 = MASR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MORR a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MORR a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MORR a0 a1 a2 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MEOR a0 a1 a2 = MLSL a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MEOR a0 a1 a2 = MLSR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MEOR a0 a1 a2 = MASR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MEOR a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MEOR a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MEOR a0 a1 a2 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MLSL a0 a1 a2 = MLSR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MLSL a0 a1 a2 = MASR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MLSL a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MLSL a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MLSL a0 a1 a2 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MLSR a0 a1 a2 = MASR a0' a1' a2')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MLSR a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MLSR a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MLSR a0 a1 a2 = MPOP a0' a1')) /\
         (!a2' a2 a1' a1 a0' a0. ~(MASR a0 a1 a2 = MROR a0' a1' a2')) /\
         (!a2 a1' a1 a0' a0. ~(MASR a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MASR a0 a1 a2 = MPOP a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MROR a0 a1 a2 = MPUSH a0' a1')) /\
         (!a2 a1' a1 a0' a0. ~(MROR a0 a1 a2 = MPOP a0' a1')) /\
         !a1' a1 a0' a0. ~(MPUSH a0 a1 = MPOP a0' a1')

   [DOPER_induction]  Theorem

      |- !P.
           (!M p. P (MLDR M p)) /\ (!p M. P (MSTR p M)) /\ (!M M0. P (MMOV M M0)) /\
           (!M M0 M1. P (MADD M M0 M1)) /\ (!M M0 M1. P (MSUB M M0 M1)) /\
           (!M M0 M1. P (MRSB M M0 M1)) /\ (!M M0 M1. P (MMUL M M0 M1)) /\
           (!M M0 M1. P (MAND M M0 M1)) /\ (!M M0 M1. P (MORR M M0 M1)) /\
           (!M M0 M1. P (MEOR M M0 M1)) /\ (!M M0 c. P (MLSL M M0 c)) /\
           (!M M0 c. P (MLSR M M0 c)) /\ (!M M0 c. P (MASR M M0 c)) /\
           (!M M0 c. P (MROR M M0 c)) /\ (!n l. P (MPUSH n l)) /\
           (!n l. P (MPOP n l)) ==>
           !D. P D

   [DOPER_nchotomy]  Theorem

      |- !D.
           (?M p. D = MLDR M p) \/ (?p M. D = MSTR p M) \/ (?M M0. D = MMOV M M0) \/
           (?M M0 M1. D = MADD M M0 M1) \/ (?M M0 M1. D = MSUB M M0 M1) \/
           (?M M0 M1. D = MRSB M M0 M1) \/ (?M M0 M1. D = MMUL M M0 M1) \/
           (?M M0 M1. D = MAND M M0 M1) \/ (?M M0 M1. D = MORR M M0 M1) \/
           (?M M0 M1. D = MEOR M M0 M1) \/ (?M M0 c. D = MLSL M M0 c) \/
           (?M M0 c. D = MLSR M M0 c) \/ (?M M0 c. D = MASR M M0 c) \/
           (?M M0 c. D = MROR M M0 c) \/ (?n l. D = MPUSH n l) \/ ?n l. D = MPOP n l

   [HOARE_CJ_IR]  Theorem

      |- !cond ir_t ir_f P Q R.
           WELL_FORMED ir_t /\ WELL_FORMED ir_f /\
           (!st. P st ==> Q (run_ir ir_t st)) /\
           (!st. P st ==> R (run_ir ir_f st)) ==>
           !st.
             P st ==>
             (if eval_il_cond cond st then
                Q (run_ir (CJ cond ir_t ir_f) st)
              else
                R (run_ir (CJ cond ir_t ir_f) st))

   [HOARE_SC_IR]  Theorem

      |- !ir1 ir2 P Q R T.
           WELL_FORMED ir1 /\ WELL_FORMED ir2 /\ (!st. P st ==> Q (run_ir ir1 st)) /\
           (!st. R st ==> T (run_ir ir2 st)) /\ (!st. Q st ==> R st) ==>
           !st. P st ==> T (run_ir (SC ir1 ir2) st)

   [HOARE_TR_IR]  Theorem

      |- !cond ir P.
           WELL_FORMED ir /\ WF_TR (translate_condition cond,translate ir) /\
           (!st. P st ==> P (run_ir ir st)) ==>
           !st.
             P st ==>
             P (run_ir (TR cond ir) st) /\ eval_il_cond cond (run_ir (TR cond ir) st)

   [IR_CJ_IS_WELL_FORMED]  Theorem

      |- !cond ir_t ir_f.
           WELL_FORMED ir_t /\ WELL_FORMED ir_f = WELL_FORMED (CJ cond ir_t ir_f)

   [IR_SC_IS_WELL_FORMED]  Theorem

      |- !ir1 ir2. WELL_FORMED ir1 /\ WELL_FORMED ir2 = WELL_FORMED (SC ir1 ir2)

   [IR_SEMANTICS_BLK]  Theorem

      |- (run_ir (BLK (stm::stmL)) st = run_ir (BLK stmL) (mdecode st stm)) /\
         (run_ir (BLK []) st = st)

   [IR_SEMANTICS_CJ]  Theorem

      |- WELL_FORMED ir_t /\ WELL_FORMED ir_f ==>
         (run_ir (CJ cond ir_t ir_f) st =
          (if eval_il_cond cond st then run_ir ir_t st else run_ir ir_f st))

   [IR_SEMANTICS_SC]  Theorem

      |- WELL_FORMED ir1 /\ WELL_FORMED ir2 ==>
         (run_ir (SC ir1 ir2) st = run_ir ir2 (run_ir ir1 st))

   [IR_SEMANTICS_TR]  Theorem

      |- WELL_FORMED ir /\ WF_TR (translate_condition cond,translate ir) ==>
         (run_ir (TR cond ir) st =
          WHILE (\st'. ~eval_il_cond cond st') (run_ir ir) st)

   [IR_TR_IS_WELL_FORMED]  Theorem

      |- !ir cond.
           WELL_FORMED ir /\ WF_TR (translate_condition cond,translate ir) =
           WELL_FORMED (TR cond ir)

   [MEXP_11]  Theorem

      |- (!a a'. (MR a = MR a') = (a = a')) /\
         !a0 a1 a0' a1'. (MC a0 a1 = MC a0' a1') = (a0 = a0') /\ (a1 = a1')

   [MEXP_Axiom]  Theorem

      |- !f0 f1. ?fn. (!a. fn (MR a) = f0 a) /\ !a0 a1. fn (MC a0 a1) = f1 a0 a1

   [MEXP_case_cong]  Theorem

      |- !M M' f f1.
           (M = M') /\ (!a. (M' = MR a) ==> (f a = f' a)) /\
           (!a0 a1. (M' = MC a0 a1) ==> (f1 a0 a1 = f1' a0 a1)) ==>
           (MEXP_case f f1 M = MEXP_case f' f1' M')

   [MEXP_distinct]  Theorem

      |- !a1 a0 a. ~(MR a = MC a0 a1)

   [MEXP_induction]  Theorem

      |- !P. (!M. P (MR M)) /\ (!c c0. P (MC c c0)) ==> !M. P M

   [MEXP_nchotomy]  Theorem

      |- !M. (?M'. M = MR M') \/ ?c c0. M = MC c c0

   [MREG2num_11]  Theorem

      |- !a a'. (MREG2num a = MREG2num a') = (a = a')

   [MREG2num_ONTO]  Theorem

      |- !r. r < 15 = ?a. r = MREG2num a

   [MREG2num_num2MREG]  Theorem

      |- !r. r < 15 = (MREG2num (num2MREG r) = r)

   [MREG2num_thm]  Theorem

      |- (MREG2num R0 = 0) /\ (MREG2num R1 = 1) /\ (MREG2num R2 = 2) /\
         (MREG2num R3 = 3) /\ (MREG2num R4 = 4) /\ (MREG2num R5 = 5) /\
         (MREG2num R6 = 6) /\ (MREG2num R7 = 7) /\ (MREG2num R8 = 8) /\
         (MREG2num R9 = 9) /\ (MREG2num R10 = 10) /\ (MREG2num R11 = 11) /\
         (MREG2num R12 = 12) /\ (MREG2num R13 = 13) /\ (MREG2num R14 = 14)

   [MREG_Axiom]  Theorem

      |- !x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
           ?f.
             (f R0 = x0) /\ (f R1 = x1) /\ (f R2 = x2) /\ (f R3 = x3) /\
             (f R4 = x4) /\ (f R5 = x5) /\ (f R6 = x6) /\ (f R7 = x7) /\
             (f R8 = x8) /\ (f R9 = x9) /\ (f R10 = x10) /\ (f R11 = x11) /\
             (f R12 = x12) /\ (f R13 = x13) /\ (f R14 = x14)

   [MREG_EQ_MREG]  Theorem

      |- !a a'. (a = a') = (MREG2num a = MREG2num a')

   [MREG_case_cong]  Theorem

      |- !M M' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
           (M = M') /\ ((M' = R0) ==> (v0 = v0')) /\ ((M' = R1) ==> (v1 = v1')) /\
           ((M' = R2) ==> (v2 = v2')) /\ ((M' = R3) ==> (v3 = v3')) /\
           ((M' = R4) ==> (v4 = v4')) /\ ((M' = R5) ==> (v5 = v5')) /\
           ((M' = R6) ==> (v6 = v6')) /\ ((M' = R7) ==> (v7 = v7')) /\
           ((M' = R8) ==> (v8 = v8')) /\ ((M' = R9) ==> (v9 = v9')) /\
           ((M' = R10) ==> (v10 = v10')) /\ ((M' = R11) ==> (v11 = v11')) /\
           ((M' = R12) ==> (v12 = v12')) /\ ((M' = R13) ==> (v13 = v13')) /\
           ((M' = R14) ==> (v14 = v14')) ==>
           ((case M of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            case M' of
               R0 -> v0'
            || R1 -> v1'
            || R2 -> v2'
            || R3 -> v3'
            || R4 -> v4'
            || R5 -> v5'
            || R6 -> v6'
            || R7 -> v7'
            || R8 -> v8'
            || R9 -> v9'
            || R10 -> v10'
            || R11 -> v11'
            || R12 -> v12'
            || R13 -> v13'
            || R14 -> v14')

   [MREG_case_def]  Theorem

      |- (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R0 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v0) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R1 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v1) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R2 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v2) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R3 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v3) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R4 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v4) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R5 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v5) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R6 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v6) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R7 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v7) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R8 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v8) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R9 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v9) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R10 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v10) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R11 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v11) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R12 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v12) /\
         (!v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
            (case R13 of
                R0 -> v0
             || R1 -> v1
             || R2 -> v2
             || R3 -> v3
             || R4 -> v4
             || R5 -> v5
             || R6 -> v6
             || R7 -> v7
             || R8 -> v8
             || R9 -> v9
             || R10 -> v10
             || R11 -> v11
             || R12 -> v12
             || R13 -> v13
             || R14 -> v14) =
            v13) /\
         !v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14.
           (case R14 of
               R0 -> v0
            || R1 -> v1
            || R2 -> v2
            || R3 -> v3
            || R4 -> v4
            || R5 -> v5
            || R6 -> v6
            || R7 -> v7
            || R8 -> v8
            || R9 -> v9
            || R10 -> v10
            || R11 -> v11
            || R12 -> v12
            || R13 -> v13
            || R14 -> v14) =
           v14

   [MREG_distinct]  Theorem

      |- ~(R0 = R1) /\ ~(R0 = R2) /\ ~(R0 = R3) /\ ~(R0 = R4) /\ ~(R0 = R5) /\
         ~(R0 = R6) /\ ~(R0 = R7) /\ ~(R0 = R8) /\ ~(R0 = R9) /\ ~(R0 = R10) /\
         ~(R0 = R11) /\ ~(R0 = R12) /\ ~(R0 = R13) /\ ~(R0 = R14) /\ ~(R1 = R2) /\
         ~(R1 = R3) /\ ~(R1 = R4) /\ ~(R1 = R5) /\ ~(R1 = R6) /\ ~(R1 = R7) /\
         ~(R1 = R8) /\ ~(R1 = R9) /\ ~(R1 = R10) /\ ~(R1 = R11) /\ ~(R1 = R12) /\
         ~(R1 = R13) /\ ~(R1 = R14) /\ ~(R2 = R3) /\ ~(R2 = R4) /\ ~(R2 = R5) /\
         ~(R2 = R6) /\ ~(R2 = R7) /\ ~(R2 = R8) /\ ~(R2 = R9) /\ ~(R2 = R10) /\
         ~(R2 = R11) /\ ~(R2 = R12) /\ ~(R2 = R13) /\ ~(R2 = R14) /\ ~(R3 = R4) /\
         ~(R3 = R5) /\ ~(R3 = R6) /\ ~(R3 = R7) /\ ~(R3 = R8) /\ ~(R3 = R9) /\
         ~(R3 = R10) /\ ~(R3 = R11) /\ ~(R3 = R12) /\ ~(R3 = R13) /\ ~(R3 = R14) /\
         ~(R4 = R5) /\ ~(R4 = R6) /\ ~(R4 = R7) /\ ~(R4 = R8) /\ ~(R4 = R9) /\
         ~(R4 = R10) /\ ~(R4 = R11) /\ ~(R4 = R12) /\ ~(R4 = R13) /\ ~(R4 = R14) /\
         ~(R5 = R6) /\ ~(R5 = R7) /\ ~(R5 = R8) /\ ~(R5 = R9) /\ ~(R5 = R10) /\
         ~(R5 = R11) /\ ~(R5 = R12) /\ ~(R5 = R13) /\ ~(R5 = R14) /\ ~(R6 = R7) /\
         ~(R6 = R8) /\ ~(R6 = R9) /\ ~(R6 = R10) /\ ~(R6 = R11) /\ ~(R6 = R12) /\
         ~(R6 = R13) /\ ~(R6 = R14) /\ ~(R7 = R8) /\ ~(R7 = R9) /\ ~(R7 = R10) /\
         ~(R7 = R11) /\ ~(R7 = R12) /\ ~(R7 = R13) /\ ~(R7 = R14) /\ ~(R8 = R9) /\
         ~(R8 = R10) /\ ~(R8 = R11) /\ ~(R8 = R12) /\ ~(R8 = R13) /\ ~(R8 = R14) /\
         ~(R9 = R10) /\ ~(R9 = R11) /\ ~(R9 = R12) /\ ~(R9 = R13) /\ ~(R9 = R14) /\
         ~(R10 = R11) /\ ~(R10 = R12) /\ ~(R10 = R13) /\ ~(R10 = R14) /\
         ~(R11 = R12) /\ ~(R11 = R13) /\ ~(R11 = R14) /\ ~(R12 = R13) /\
         ~(R12 = R14) /\ ~(R13 = R14)

   [MREG_induction]  Theorem

      |- !P.
           P R0 /\ P R1 /\ P R10 /\ P R11 /\ P R12 /\ P R13 /\ P R14 /\ P R2 /\
           P R3 /\ P R4 /\ P R5 /\ P R6 /\ P R7 /\ P R8 /\ P R9 ==>
           !a. P a

   [MREG_nchotomy]  Theorem

      |- !a.
           (a = R0) \/ (a = R1) \/ (a = R2) \/ (a = R3) \/ (a = R4) \/ (a = R5) \/
           (a = R6) \/ (a = R7) \/ (a = R8) \/ (a = R9) \/ (a = R10) \/ (a = R11) \/
           (a = R12) \/ (a = R13) \/ (a = R14)

   [SEMANTICS_OF_IR]  Theorem

      |- WELL_FORMED ir1 /\ WELL_FORMED ir2 ==>
         (run_ir (BLK (stm::stmL)) st = run_ir (BLK stmL) (mdecode st stm)) /\
         (run_ir (BLK []) st = st) /\
         (run_ir (SC ir1 ir2) st = run_ir ir2 (run_ir ir1 st)) /\
         (run_ir (CJ cond ir1 ir2) st =
          (if eval_il_cond cond st then run_ir ir1 st else run_ir ir2 st)) /\
         (WF_TR (translate_condition cond,translate ir1) ==>
          (run_ir (TR cond ir1) st =
           WHILE (\st'. ~eval_il_cond cond st') (run_ir ir1) st))

   [STATEMENT_IS_WELL_FORMED]  Theorem

      |- !stm. well_formed [translate_assignment stm]

   [TRANSLATE_ASSIGMENT_CORRECT]  Theorem

      |- !stm pc cpsr st.
           (SUC pc,cpsr,mdecode st stm) =
           decode_cond (pc,cpsr,st) (translate_assignment stm)

   [TRANSLATE_ASSIGMENT_CORRECT_2]  Theorem

      |- !stm s.
           decode_cond s (translate_assignment stm) =
           (SUC (FST s),FST (SND s),mdecode (SND (SND s)) stm)

   [UPLOAD_LEM_2]  Theorem

      |- !s stm iB. upload [stm] iB (FST s) (FST s) = stm

   [WELL_FORMED_SUB_thm]  Theorem

      |- !ir. WELL_FORMED ir = WELL_FORMED_SUB ir /\ well_formed (translate ir)

   [WELL_FORMED_thm]  Theorem

      |- (WELL_FORMED (BLK stmL) = T) /\
         (WELL_FORMED (SC S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
         (WELL_FORMED (CJ cond S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
         (WELL_FORMED (TR cond S1) =
          WELL_FORMED S1 /\ WF_TR (translate_condition cond,translate S1))

   [datatype_CTL_STRUCTURE]  Theorem

      |- DATATYPE (CTL_STRUCTURE BLK SC CJ TR)

   [datatype_DOPER]  Theorem

      |- DATATYPE
           (DOPER MLDR MSTR MMOV MADD MSUB MRSB MMUL MAND MORR MEOR MLSL MLSR MASR
              MROR MPUSH MPOP)

   [datatype_MEXP]  Theorem

      |- DATATYPE (MEXP MR MC)

   [datatype_MREG]  Theorem

      |- DATATYPE (MREG R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14)

   [from_reg_index_thm]  Theorem

      |- (from_reg_index 0 = R0) /\ (from_reg_index 1 = R1) /\
         (from_reg_index 2 = R2) /\ (from_reg_index 3 = R3) /\
         (from_reg_index 4 = R4) /\ (from_reg_index 5 = R5) /\
         (from_reg_index 6 = R6) /\ (from_reg_index 7 = R7) /\
         (from_reg_index 8 = R8) /\ (from_reg_index 9 = R9) /\
         (from_reg_index 10 = R10) /\ (from_reg_index 11 = R11) /\
         (from_reg_index 12 = R12) /\ (from_reg_index 13 = R13) /\
         (from_reg_index 14 = R14)

   [num2MREG_11]  Theorem

      |- !r r'. r < 15 ==> r' < 15 ==> ((num2MREG r = num2MREG r') = (r = r'))

   [num2MREG_MREG2num]  Theorem

      |- !a. num2MREG (MREG2num a) = a

   [num2MREG_ONTO]  Theorem

      |- !a. ?r. (a = num2MREG r) /\ r < 15

   [num2MREG_thm]  Theorem

      |- (num2MREG 0 = R0) /\ (num2MREG 1 = R1) /\ (num2MREG 2 = R2) /\
         (num2MREG 3 = R3) /\ (num2MREG 4 = R4) /\ (num2MREG 5 = R5) /\
         (num2MREG 6 = R6) /\ (num2MREG 7 = R7) /\ (num2MREG 8 = R8) /\
         (num2MREG 9 = R9) /\ (num2MREG 10 = R10) /\ (num2MREG 11 = R11) /\
         (num2MREG 12 = R12) /\ (num2MREG 13 = R13) /\ (num2MREG 14 = R14)

   [translate_def]  Theorem

      |- (translate (BLK (stm::stmL)) =
          translate_assignment stm::translate (BLK stmL)) /\
         (translate (BLK []) = []) /\
         (translate (SC S1 S2) = mk_SC (translate S1) (translate S2)) /\
         (translate (CJ cond Strue Sfalse) =
          mk_CJ (translate_condition cond) (translate Strue) (translate Sfalse)) /\
         (translate (TR cond Sbody) =
          mk_TR (translate_condition cond) (translate Sbody))

   [translate_ind]  Theorem

      |- !P.
           (!stm stmL. P (BLK stmL) ==> P (BLK (stm::stmL))) /\ P (BLK []) /\
           (!S1 S2. P S1 /\ P S2 ==> P (SC S1 S2)) /\
           (!cond Strue Sfalse. P Sfalse /\ P Strue ==> P (CJ cond Strue Sfalse)) /\
           (!cond Sbody. P Sbody ==> P (TR cond Sbody)) ==>
           !v. P v


*)
end
