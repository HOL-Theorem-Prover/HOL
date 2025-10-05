(* For interactive work
  quietdec := true;
  app load ["wordsLib"];
  open pairTheory wordsTheory listTheory;
  quietdec := false;
*)
Theory MARS_Data
Ancestors
  pair words


(*---------------------------------------------------------------------------*)
(* Type Definitions                                                          *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("block", ``:word32 # word32 # word32 # word32``);
val _ = type_abbrev("key",   ``:word32 # word32 # word32 # word32``);

val _ = type_abbrev("keysched",
     ``:word32 # word32 # word32 # word32 # word32 # word32 # word32 #
        word32 # word32 # word32 # word32 # word32 # word32 # word32 #
        word32 # word32 # word32 # word32 # word32 # word32 # word32 #
        word32 # word32 # word32 # word32 # word32 # word32 # word32 #
        word32 # word32 # word32 # word32 # word32 # word32 # word32 #
        word32 # word32 # word32 # word32 # word32``);

(*---------------------------------------------------------------------------*)
(* Case analysis on a block, a key schedule                                  *)
(*---------------------------------------------------------------------------*)

val FORALL_BLOCK = Q.store_thm
  ("FORALL_BLOCK",
    `(!b:block. P b) = !v0 v1 v2 v3. P (v0,v1,v2,v3)`,
    SIMP_TAC std_ss [FORALL_PROD]);

val FORALL_KEYSCHEDS = Q.prove(
 `(!x:keysched. P x) =
   !k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18
     k19 k20 k21 k22 k23 k24 k25 k26 k27 k28 k29 k30 k31 k32 k33 k34
     k35 k36 k37 k38 k39.
   P(k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,
    k19,k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,
    k35,k36,k37,k38,k39)`,
  SIMP_TAC std_ss [FORALL_PROD]);

(* --------------------------------------------------------------------------*)
(* Functions for processing keys                                             *)
(*---------------------------------------------------------------------------*)

Definition ROTKEYS_def:
  ROTKEYS
    (k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,
     k19,k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,
     k36,k37,k38,k39) =
   (k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,k20,
    k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,
    k38,k39,k0,k1) : keysched
End

Definition ROTKEYS18_def:
  ROTKEYS18
    (k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,k20,
     k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,
     k38,k39,k0,k1) =
   (k36,k37,k38,k39,k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,
    k16,k17,k18,k19,k20,k21,k22, k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,
    k33,k34,k35) : keysched
End

Definition INVROTKEYS_def:
  INVROTKEYS
     (k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,k20,
      k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,
      k38,k39,k0,k1) =
   (k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,
    k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,
    k37,k38,k39) : keysched
End

val ROTKEYS_Inversion = Q.store_thm
  ("ROTKEYS_Inversion",
  `!k:keysched. (INVROTKEYS(ROTKEYS(k)) = k) /\
                (ROTKEYS(INVROTKEYS(k)) = k)`,
  SIMP_TAC std_ss [FORALL_KEYSCHEDS] THEN
  REWRITE_TAC [ROTKEYS_def,INVROTKEYS_def]);

Definition GETKEYS_def:
  GETKEYS
    ((k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,
      k19,k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,
      k35,k36,k37,k38,k39):keysched) =
    (k0,k1)
End

Definition LIST_TO_KEYS_def:
   (LIST_TO_KEYS [] acc = acc:keysched) /\
   (LIST_TO_KEYS (h::t) (k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,
                         k11,k12,k13,k14,k15,k16,k17,k18,k19,k20,
                         k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,
                         k31,k32,k33,k34,k35,k36,k37,k38,k39) =
      LIST_TO_KEYS t (h,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,
                      k16,k17,k18,k19,k20,k21,k22,k23,k24,k25,k26,k27,k28,
                      k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39))
End

Definition DUMMY_KEYS_def:
   DUMMY_KEYS =
      (0w,0w,0w,0w,0w,0w,0w,0w,0w,0w,
       0w,0w,0w,0w,0w,0w,0w,0w,0w,0w,
       0w,0w,0w,0w,0w,0w,0w,0w,0w,0w,
       0w,0w,0w,0w,0w,0w,0w,0w,0w,0w) : keysched
End

