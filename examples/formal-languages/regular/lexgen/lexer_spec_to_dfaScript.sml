(*---------------------------------------------------------------------------*)
(* Mapping lexer specs to lexers. Treats an entire lex_spec as a "state"     *)
(*---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory listTheory;
open dfaTheory charsetTheory regexpTheory lexer_runtimeTheory;

val _ = new_theory "lexer_spec_to_dfa"

val is_error_state_def =
 Define
  `is_error_state lex_spec =
     EVERY (\(regexp,tokfn). regexp = Chset charset_empty) lex_spec`;

val lex_spec_transition_def =
 Define
  `lex_spec_transition (lspec,c) =
     let lspec' = MAP (\(r,tokfn). (smart_deriv (ORD c) r, tokfn)) lspec
     in
       if is_error_state lspec' then
         NONE
       else
         SOME lspec'`;

val lex_spec_finals_def =
 Define
  `lex_spec_finals lspec =
    case FILTER (\(r,tokfn). nullable r) lspec of
     | (regexp,tokfn)::_ => SOME tokfn
     | _ => NONE`;

val lex_spec_action_lem = Q.prove
(`n < LENGTH lspec /\ (lex_spec_transition (lspec,c) = SOME lspec')
  ==>
  (SND (EL n lspec) = SND (EL n lspec'))`,
rw [LET_THM, lex_spec_transition_def]
  >> rw [EL_MAP]
  >> Cases_on `EL n lspec`
  >> rw []);

val lex_spec_trans_lem = Q.prove
(`n < LENGTH lspec' /\ n < LENGTH lspec /\
  (lex_spec_transition (lspec, c) = SOME lspec') /\
  regexp_lang (FST (EL n lspec')) (MAP FST p)
  ==>
  regexp_lang (FST (EL n lspec)) (STRING c (MAP FST p))`,
 rw [LET_THM, lex_spec_transition_def]
  >> POP_ASSUM MP_TAC
  >> rw [EL_MAP]
  >> Cases_on `EL n lspec`
  >> fs [GSYM regexp_lang_smart_deriv, smart_deriv_matches_def]);

val lex_spec_trans_lem2 = Q.prove
(`n' < n /\ n' < LENGTH lspec' /\ n' < LENGTH lspec /\
  (lex_spec_transition (lspec,c) = SOME lspec') /\
  ~regexp_lang (FST (EL n' lspec')) (MAP FST p)
  ==>
   ~regexp_lang (FST (EL n' lspec)) (STRING c (MAP FST p))`,
 rw [LET_THM, lex_spec_transition_def]
  >> POP_ASSUM MP_TAC
  >> rw [EL_MAP]
  >> Cases_on `EL n' lspec`
  >> fs [GSYM regexp_lang_smart_deriv, smart_deriv_matches_def]);

val path_to_spec = Q.prove
(`!trans lspec end_st p.
  dfa_path trans lspec end_st p
  ==>
  !t.
    (trans = lex_spec_transition) /\
    (lex_spec_finals end_st = SOME t)
    ==>
    ?n.
      n < LENGTH lspec /\ (SND (EL n lspec) = t) /\
      regexp_lang (FST (EL n lspec)) (MAP FST p) /\
      (!n'. n' < n ==> ~regexp_lang (FST (EL n' lspec)) (MAP FST p))`,
 ho_match_mp_tac dfa_path_ind
 >> rw [LET_THM,dfa_path_def]
 >- (fs [lex_spec_transition_def, lex_spec_finals_def]
      >> Cases_on `FILTER (\(regexp,action). nullable regexp) end_st`
      >> fs []
      >> PairCases_on `h`
      >> fs [] >> rw []
      >> Induct_on `end_st`
      >> rw []
      >> fs []
      >- (qexists_tac `0` >> rw [] >> metis_tac [nullable_thm])
      >- (qexists_tac `SUC n`
          >> fs []
          >> rw []
          >> Cases_on `n'`
          >> fs []
          >> PairCases_on `h`
          >> fs []
          >> metis_tac [nullable_thm]))
 >- (Cases_on `lex_spec_transition (lspec,c)`
      >> fs [] >> rw []
      >> res_tac
      >> fs [] >> rw []
      >> `n < LENGTH lspec`
              by (fs [LET_THM,lex_spec_transition_def]
      >> metis_tac [LENGTH_MAP])
      >> qexists_tac `n`
      >> rw []
      >> metis_tac [arithmeticTheory.LESS_TRANS, lex_spec_action_lem,
                    lex_spec_trans_lem, lex_spec_trans_lem2])
);

val lemma = Q.prove
(`!s. ~regexp_lang (Chset charset_empty) s`,
 metis_tac [regexp_lang_eqns]);

val spec_to_path = Q.prove
(`!n lex_spec l.
   n < LENGTH lex_spec /\
   regexp_lang (FST (EL n lex_spec)) l /\
   (!n'. n' < n ==> ~regexp_lang (FST (EL n' lex_spec)) l)
  ==>
   ?p s.
     (l = MAP FST p) /\
     dfa_path lex_spec_transition lex_spec s p /\
     (lex_spec_finals s = SOME (SND (EL n lex_spec)))`,
Induct_on `l`
 >> rw []
 >- (qexists_tac `lex_spec`
       >> rw [dfa_path_def, lex_spec_transition_def,
              lex_spec_finals_def, nullable_thm]
       >> REPEAT (pop_assum mp_tac)
       >> Q.SPEC_TAC (`lex_spec`, `lex_spec`)
       >> Induct_on `n`
       >> rw []
       >> Cases_on `lex_spec`
       >> fs []
       >> PairCases_on `h`
       >> fs [] >> rw []
       >- metis_tac [DECIDE ``0 < SUC n``, EL, FST, HD, TL]
       >- (res_tac
            >> pop_assum match_mp_tac
            >> rw []
            >> `SUC n' < SUC n` by decide_tac
            >> metis_tac [EL, FST, HD, TL])
    )
 >- (`!n'. n' < n ==>
       ~smart_deriv_matches
           (FST (EL n'
                  (MAP (\(r,tokfn). (smart_deriv (ORD h) r,tokfn)) lex_spec)))
           l`
       by (rw []
            >> `n' < LENGTH lex_spec` by decide_tac
            >> rw [EL_MAP, LENGTH_MAP]
            >> fs [smart_deriv_matches_def, GSYM regexp_lang_smart_deriv]
            >> Cases_on  `EL n' lex_spec`
            >> rw []
            >> metis_tac [FST])
     >> qpat_x_assum `!n lex_spec. P n lex_spec`
          (MP_TAC o Q.SPECL [`n`, `THE (lex_spec_transition (lex_spec,h))`])
     >> rw [lex_spec_transition_def, lex_spec_finals_def, EL_MAP, LET_THM]
     >> Cases_on `EL n lex_spec`
     >> fs [GSYM regexp_lang_smart_deriv, smart_deriv_matches_def]
     >- (fs [is_error_state_def, EVERY_MAP]
         >> fs [EVERY_EL]
         >> res_tac
         >> Cases_on `EL n lex_spec`
         >> fs []
         >> rw []
         >> metis_tac [GSYM regexp_lang_smart_deriv, lemma])
     >- (qpat_x_assum `a /\b ==> c` MP_TAC
          >> rw[]
          >> byA (
              `(!n'. n' < n ==>
                     ~smart_deriv_matches
                       (FST ((\(r,tokfn). (smart_deriv (ORD h) r,tokfn))
                             (EL n' lex_spec)))
                       l)
               =
               (!n'. n' < n ==>
                     ~smart_deriv_matches
                       (FST (EL n'
                              (MAP (\(r,tokfn).
                                   (smart_deriv (ORD h) r,tokfn)) lex_spec)))
                      l)`,
              (pop_assum kall_tac >> rw [EQ_IMP_THM] >> res_tac
               >> pop_assum kall_tac
               >> pop_assum mp_tac
               >> `n' < LENGTH lex_spec` by decide_tac
               >> metis_tac [EL_MAP]))
          >> pop_assum SUBST_ALL_TAC
          >> res_tac
          >> rw []
          >> Cases_on `FILTER (\(r,tokfn). nullable r) s`
          >> fs []
          >> PairCases_on `h'`
          >> fs []
          >> rw []
          >> qexists_tac
              `(h,MAP (\(r,tokfn). (smart_deriv (ORD h) r,tokfn)) lex_spec)::p`
          >> qexists_tac `s`
          >> rw [dfa_path_def,lex_spec_transition_def]
          >> fs []))
);

val lex_spec_to_dfa_correct = Q.store_thm
("lex_spec_to_dfa_correct",
 `!lex_spec.
   dfa_correct lex_spec lex_spec_transition lex_spec_finals lex_spec`,
rw [dfa_correct_def,EQ_IMP_THM]
 >- metis_tac [path_to_spec]
 >- metis_tac [spec_to_path]
);


val _ = export_theory ();
