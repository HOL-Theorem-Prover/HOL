(*---------------------------------------------------------------------------*)
(* Specification of a lexer in terms of regular expressions paired with      *)
(* action functions.                                                         *)
(*---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;
open stringTheory listTheory rich_listTheory regexpTheory;

val _ = new_theory "lexer_spec";

(*---------------------------------------------------------------------------*)
(* A lexer is specified by a list of regexps, each paired with an action     *)
(* function.                                                                 *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev ("lexer_spec", ``:(regexp#(string->'a)) list``);

(*---------------------------------------------------------------------------*)
(* Generic lemmas                                                            *)
(*---------------------------------------------------------------------------*)

val strcat_lem = Q.prove (
`!s1 s2 s3 s4.
  (STRLEN s1 = STRLEN s3) /\ (STRCAT s1 s2 = STRCAT s3 s4)
  ==>
  (s1 = s3) /\
  (s2 = s4)`,
Induct_on `s1`
  >> rw [] 
  >> Cases_on `s3`
  >> fs [] 
  >> metis_tac []);

val append_length_gt = Q.prove (
`!s1 s2 s3 s4.
  (LENGTH s1 > LENGTH s3) /\ (s1 ++ s2 = s3 ++ s4) ==>
  ?c s5. (s1 = s3 ++ c::s5)`,
Induct_on `s1`
 >> rw []
 >> Cases_on `s3` 
 >> full_simp_tac (srw_ss()++ARITH_ss) [] 
 >> rw [] 
 >> `LENGTH s1 > LENGTH t` by decide_tac 
 >> metis_tac []);

(*---------------------------------------------------------------------------*)
(* How a lexer spec matches the prefix of a string                           *)
(*---------------------------------------------------------------------------*)

val lexer_spec_matches_prefix_def =
 Define 
  `lexer_spec_matches_prefix lexer_spec n token prefix suffix s =
   ?r f.
      n < LENGTH lexer_spec     /\
      (EL n lexer_spec = (r,f)) /\
      (token = f prefix)        /\
      regexp_lang r prefix      /\
      (s = prefix ++ suffix)`;

val lexer_spec_matches_prefix_alt_def =
 Define 
  `lexer_spec_matches_prefix_alt lexer_spec token prefix suffix s =
    ?r f. (MEM (r,f) lexer_spec) /\
          (token = f prefix)     /\ 
          regexp_lang r prefix   /\
          (s = prefix ++ suffix)`;

val lexer_spec_matches_equiv = Q.store_thm 
("lexer_spec_matches_equiv",
 `!lexer_spec tok prefix suffix s.
   lexer_spec_matches_prefix_alt lexer_spec tok prefix suffix s 
    =
   ?n. lexer_spec_matches_prefix lexer_spec n tok prefix suffix s`,
 rw [lexer_spec_matches_prefix_def, lexer_spec_matches_prefix_alt_def]
  >> metis_tac [MEM_EL])

(*---------------------------------------------------------------------------*)
(* A correct lexer breaks a string into a sequence of non-null lexemes, each *)
(* being matched by one of the regexps given in the actions, and each of max *)
(* possible length. If multiple regexps in the spec match the max. len.      *)
(* lexeme, the earliest one in the list of actions is taken. This is the     *)
(* "maximal munch" approach to making lexing deterministic.                  *)
(*---------------------------------------------------------------------------*)

val correct_lex_def =
 Define 
  `(correct_lex lexer_spec s [] = (s = [])) /\
   (correct_lex lexer_spec s (tok::toks) =
     ?prefix n suffix.
       (prefix <> []) /\
       lexer_spec_matches_prefix lexer_spec n tok prefix suffix s /\
       correct_lex lexer_spec suffix toks /\
       (* Ensure a longest match  *)
       (!n' tok' prefix' suffix'.
           lexer_spec_matches_prefix lexer_spec n' tok' prefix' suffix' s 
            ==>
           LENGTH prefix' <= LENGTH prefix) /\
       (* Ensure the earliest match of equal length *)
       (!n' tok' prefix' suffix'.
           lexer_spec_matches_prefix lexer_spec n' tok' prefix' suffix' s
             ==>
           (LENGTH prefix' <> LENGTH prefix) \/ n <= n'))`;

val correct_lex_thm = Q.store_thm 
("correct_lex_thm",
 `!lexer_spec s tok toks.
    (correct_lex lexer_spec s [] = (s = [])) /\
    (correct_lex lexer_spec s (tok::toks) =
     ?prefix n suffix.
        (prefix <> []) /\
        lexer_spec_matches_prefix lexer_spec n tok prefix suffix s /\
        correct_lex lexer_spec suffix toks /\
        (* Ensure a longest match  *)
        (!tok' prefix' suffix'.
           (prefix' <> "") /\ (suffix = prefix' ++ suffix') 
          ==>
          ~lexer_spec_matches_prefix_alt
              lexer_spec tok' (prefix++prefix') suffix' s) /\
        (* Ensure the earliest match of equal length *)
        (!tok'.
           ~lexer_spec_matches_prefix_alt (TAKE n lexer_spec) tok' prefix suffix s))`,
 rw []
 >> rw [Once correct_lex_def] 
 >> eq_tac 
 >> rw [lexer_spec_matches_prefix_alt_def, lexer_spec_matches_prefix_def] 
 >- (qexists_tac `prefix` >> qexists_tac `n` >> qexists_tac `suffix` 
     >> simp[] 
     >> conj_tac
        THENL [map_every qx_gen_tac [`tok`, `prefix'`, `suffix'`],
               map_every qx_gen_tac [`r'`, `f'`]] 
     >> rw [] 
     >> CCONTR_TAC
     >> fs [MEM_EL] 
     >> rw [] 
     >- (`STRLEN (STRCAT prefix prefix') <= STRLEN prefix` by metis_tac [] 
         >> fs [] 
         >> `STRLEN prefix' = 0` by decide_tac
         >> Cases_on `prefix'` 
         >> fs [])
     >- (`n <= LENGTH lexer_spec` by decide_tac
         >> fs [LENGTH_TAKE] 
         >> `(r',f') = EL n' lexer_spec` by metis_tac [EL_TAKE, LENGTH_TAKE] 
         >> `n' < LENGTH lexer_spec` by DECIDE_TAC 
         >> `n <= n'` by metis_tac [LENGTH_TAKE] 
         >> DECIDE_TAC))
 >- (qexists_tac `prefix`
     >> qexists_tac `n`
     >> qexists_tac `suffix` 
     >> simp[] 
     >> conj_tac 
     >> map_every qx_gen_tac [`n'`, `tok`, `prefix'`, `suffix'`] 
     >> rw [] 
     >> CCONTR_TAC 
     >> fs []
     >- (`STRLEN prefix' > STRLEN prefix` by DECIDE_TAC 
         >> `?c prefix''. prefix' = prefix++c::prefix''` 
               by metis_tac [append_length_gt] 
         >> fs [MEM_EL] 
         >> rw [] 
         >> `c::prefix'' <> ""` by rw [] 
         >> metis_tac [APPEND, APPEND_ASSOC])
     >- (`prefix = prefix'` by metis_tac [strcat_lem] 
         >> `n' < n /\ n' <= LENGTH lexer_spec /\ n <= LENGTH lexer_spec`
                  by DECIDE_TAC 
         >> fs [MEM_EL] >> rw [] 
         >> metis_tac [EL_TAKE, LENGTH_TAKE]))
);

val correct_lex_determ = Q.store_thm
("correct_lex_determ",
 `!lexer_spec s toks toks'.
    correct_lex lexer_spec s toks /\ correct_lex lexer_spec s toks'
    ==>
    (toks = toks')`,
Induct_on `toks` 
 >> rw [correct_lex_def] 
 >> Cases_on `toks'` 
 >> rw [] >> fs []
 >> rw [] >> fs [correct_lex_def] 
 >> rw [] 
 >- (fs [lexer_spec_matches_prefix_def] >> metis_tac [])
 >- (fs [lexer_spec_matches_prefix_def] >> metis_tac [])
 >- (res_tac 
     >> full_simp_tac (srw_ss()++ARITH_ss) []
     >> `n = n'` by decide_tac
     >> fs [lexer_spec_matches_prefix_def] 
     >> rw [] >> fs [] 
     >> `STRLEN prefix = STRLEN prefix'` by decide_tac
     >> fs [lexer_spec_matches_prefix_def] 
     >> rw [] >> fs [] 
     >> metis_tac [strcat_lem])
 >- (res_tac 
     >> full_simp_tac (srw_ss()++ARITH_ss) []
     >> `STRLEN prefix = STRLEN prefix'` by decide_tac 
     >> fs [lexer_spec_matches_prefix_def] 
     >> rw [] >> fs [] 
     >> metis_tac [strcat_lem])
);

val _ = export_theory ();
