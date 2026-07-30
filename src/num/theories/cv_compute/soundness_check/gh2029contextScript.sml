Theory gh2029context[bare]
Ancestors
  arithmetic cv one option
Libs
  HolKernel Parse boolLib cv_computeLib BasicProvers metisLib numLib

fun simp ths = simpLib.SIMP_TAC (srw_ss()) ths

(* -------------------------------------------------------------------------
 * A polymorphic family of prospective compute-value types.
 *
 * At the good instance 'a = cv, :('a option) is isomorphic to :cv.  The
 * selected maps below are therefore genuine inverse maps at that instance.
 * At the bad instance 'a = one there can be no such isomorphism, and choice
 * is unconstrained.  Importantly, demo_num still maps every positive numeral
 * to SOME of an element of :'a, so demo_num 1 = demo_num 2 at 'a = one.
 * ------------------------------------------------------------------------- *)

val demo_good_def = new_definition("demo_good_def",
  “demo_good (e:num -> 'a) (enc:cv -> 'a option)
            (dec:'a option -> cv) <=>
    (!x. dec (enc x) = x) /\
    (!y. enc (dec y) = y) /\
    enc (cv$Num 0) = NONE /\
    (!n. enc (cv$Num (SUC n)) = SOME (e n))”
);

val demo_choice_def = new_definition("demo_choice_def",
  “demo_choice =
    @z : (num -> 'a) #
         ((cv -> 'a option) # ('a option -> cv)).
      demo_good (FST z) (FST (SND z)) (SND (SND z))”
);

val demo_e_def = new_definition("demo_e_def", “demo_e = FST demo_choice”);
val demo_enc_def = new_definition(
  "demo_enc_def",
  “demo_enc = FST (SND demo_choice)”);
val demo_dec_def = new_definition(
  "demo_dec_def",
  “demo_dec = SND (SND demo_choice)”);

(* An explicit cv <-> cv option isomorphism witnessing that demo_good is
 * satisfiable at the good instance. *)
val demo_cenc_def = new_recursive_definition {
  def = “(demo_cenc (cv$Num n) =
          case n of 0 => NONE | SUC n => SOME (cv$Num n)) /\
         (demo_cenc (cv$Pair x y) = SOME (cv$Pair x y))”,
  name = "demo_cenc_def",
  rec_axiom = cvTheory.cv_Axiom
}

val demo_cdec_def = new_recursive_definition{
  def = “(demo_cdec NONE = cv$Num 0) /\
         (demo_cdec (SOME cv) = case cv of
                                  cv$Num n => cv$Num (SUC n)
                                | cv$Pair x y => cv$Pair x y)”,
  rec_axiom = optionTheory.option_Axiom, name = "demo_cdec_def"
};

Theorem demo_cdec_cenc[simp]:
  !x. demo_cdec (demo_cenc x) = x
Proof
  Cases >> simp [demo_cenc_def, demo_cdec_def] >>
  Cases_on `m` >> simp [demo_cenc_def, demo_cdec_def]
QED

Theorem demo_cenc_cdec[simp]:
  !a. demo_cenc (demo_cdec a) = a
Proof
  Cases >> simp [demo_cenc_def, demo_cdec_def] >>
  Cases_on `x` >> simp [demo_cenc_def, demo_cdec_def] >>
  Cases_on `n` >> simp [demo_cenc_def, demo_cdec_def]
QED

Theorem demo_good_exists_cv:
  ?z : (num -> cv) # ((cv -> cv option) # (cv option -> cv)).
    demo_good (FST z) (FST (SND z)) (SND (SND z))
Proof
  Q.EXISTS_TAC `(cv$Num, (demo_cenc, demo_cdec))` >>
  simp [demo_good_def, demo_cenc_def] >>
  MATCH_ACCEPT_TAC demo_cdec_cenc
QED

(* SELECT_RULE turns the preceding existential theorem into the property of
 * the selected tuple.  Rewriting exposes the three public projections. *)
Theorem demo_choice_good =
  demo_good_exists_cv
  |> SELECT_RULE
  |> REWRITE_RULE
       [GSYM demo_choice_def, GSYM demo_e_def,
        GSYM demo_enc_def, GSYM demo_dec_def];

Theorem demo_dec_enc_good[simp]:
  !x:cv. (demo_dec (demo_enc x : cv option)) = x
Proof
  mp_tac demo_choice_good >>
  rewrite_tac [demo_good_def] >>
  strip_tac >> first_x_assum MATCH_ACCEPT_TAC
QED

Theorem demo_enc_dec_good[simp]:
  !x:cv option. (demo_enc (demo_dec x)) = x
Proof
  mp_tac demo_choice_good >>
  rewrite_tac[demo_good_def] >>
  strip_tac >> first_x_assum MATCH_ACCEPT_TAC
QED

Theorem demo_enc_11_good[simp]:
  !x y. ((demo_enc x : cv option) = demo_enc y) <=> (x = y)
Proof
  METIS_TAC [demo_dec_enc_good]
QED

Theorem demo_dec_11_good[simp]:
  !x y:cv option. ((demo_dec x) = demo_dec y) <=> (x = y)
Proof
  METIS_TAC [demo_enc_dec_good]
QED

(* -------------------------------------------------------------------------
 * Polymorphic CV operations.  The non-equality operations are transports of
 * the standard cv operations.  demo_num is intentionally defined directly,
 * so its bad :one option instance has the finite collision used below.
 * ------------------------------------------------------------------------- *)

val demo_num_def = new_recursive_definition{
  def = “(demo_num 0 = (NONE:'a option)) /\
         (demo_num (SUC n) = SOME (demo_e n))”,
  name = "demo_num_def",
  rec_axiom = prim_recTheory.num_Axiom
}

val demo_pair_def = new_definition(
  "demo_pair_def",
  “(demo_pair (p:'a option) (q:'a option) : 'a option) =
   demo_enc (cv$Pair (demo_dec p) (demo_dec q))”
);

val demo_fst_def = new_definition(
  "demo_fst_def",
  “(demo_fst (p:'a option) : 'a option) = demo_enc (cv_fst (demo_dec p))”
);

val demo_snd_def = new_definition(
  "demo_snd_def",
  “(demo_snd (p:'a option) : 'a option) = demo_enc (cv_snd (demo_dec p))”
);

val demo_ispair_def = new_definition(
  "demo_ispair_def",
  “(demo_ispair (p:'a option) : 'a option) = demo_enc (cv_ispair (demo_dec p))”
);

val demo_add_def = new_definition(
  "demo_add_def",
  “(demo_add (p:'a option) (q:'a option) : 'a option) =
    demo_enc (cv_add (demo_dec p) (demo_dec q))”
);

val demo_sub_def = new_definition(
  "demo_sub_def",
  “(demo_sub (p:'a option) (q:'a option) : 'a option) =
   demo_enc (cv_sub (demo_dec p) (demo_dec q))”
);

val demo_mul_def = new_definition(
  "demo_mul_def",
  “(demo_mul (p:'a option) (q:'a option) : 'a option) =
   demo_enc (cv_mul (demo_dec p) (demo_dec q))”
);

val demo_div_def = new_definition(
  "demo_div_def",
  “(demo_div (p:'a option) (q:'a option) : 'a option) =
   demo_enc (cv_div (demo_dec p) (demo_dec q))”
);

val demo_mod_def = new_definition(
  "demo_mod_def",
  “(demo_mod (p:'a option) (q:'a option) : 'a option) =
   demo_enc (cv_mod (demo_dec p) (demo_dec q))”
);

val demo_lt_def = new_definition(
  "demo_lt_def",
  “(demo_lt (p:'a option) (q:'a option) : 'a option) =
   demo_enc (cv_lt (demo_dec p) (demo_dec q))”
);

val demo_if_def = new_definition(
  "demo_if_def",
  “(demo_if (c:'a option) (p:'a option) (q:'a option) : 'a option) =
   demo_enc (cv_if (demo_dec c) (demo_dec p) (demo_dec q))”
);

(* This operation has its intended equality behaviour at every instance. *)
val demo_eq_def = new_definition(
  "demo_eq_def",
  “(demo_eq (p:'a option) (q:'a option) : 'a option) =
   demo_num (if p = q then SUC 0 else 0)”
);

Theorem demo_num_good[simp]:
  !n. (demo_num n : cv option) = demo_enc (cv$Num n)
Proof
  Cases >>
  simp [demo_num_def] >>
  METIS_TAC [demo_choice_good, demo_good_def]
QED

