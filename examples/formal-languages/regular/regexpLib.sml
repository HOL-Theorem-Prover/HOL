structure regexpLib :> regexpLib =
struct

open HolKernel boolLib bossLib;
open pairLib optionLib pred_setLib listLib stringLib wordsLib;
open listTheory stringTheory arithmeticTheory pred_setTheory
     sortingTheory mergesortTheory comparisonTheory balanced_mapTheory
     vec_mapTheory charsetTheory
     regexpTheory regexp_compilerTheory regexp_parserTheory;

open Regexp_Type regexpSyntax regexpMisc;

val ERR = mk_HOL_ERR "regexpLib";

fun sml_matcher r =
 let val {matchfn,start,table,final} = Regexp_Match.vector_matcher r
     val _ = stdErr_print (Int.toString(Vector.length final)^" states.\n")
 in {certificate = NONE:thm option,
     matchfn = matchfn,
     table = table,
     start = start,
     final = final}
 end;

(*---------------------------------------------------------------------------*)
(* Proof-based compilation of regexps into DFAs, and associated regexp       *)
(* matching.                                                                 *)
(*---------------------------------------------------------------------------*)

val numeral_cmp_thm = Q.prove
(`(num_cmp (NUMERAL x) (NUMERAL y) = num_cmp x y) /\
  (num_cmp (NUMERAL x) y = num_cmp x y) /\
  (num_cmp x (NUMERAL y) = num_cmp x y) /\
  (num_cmp 0 n = num_cmp ZERO n) /\
  (num_cmp n 0 = num_cmp n ZERO) /\
  (num_cmp ZERO ZERO = Equal) ∧
  (num_cmp ZERO (BIT1 y) = Less) ∧
  (num_cmp ZERO (BIT2 y) = Less) ∧
  (num_cmp (BIT1 x) ZERO = Greater) ∧
  (num_cmp (BIT2 x) ZERO = Greater) ∧
  (num_cmp (BIT1 x) (BIT1 y) = num_cmp x y) ∧
  (num_cmp (BIT2 x) (BIT2 y) = num_cmp x y) ∧
  (num_cmp (BIT1 x) (BIT2 y) = case num_cmp x y of Greater => Greater | _ => Less) ∧
  (num_cmp (BIT2 x) (BIT1 y) = case num_cmp x y of Less => Less | _ => Greater)`,
 METIS_TAC [arithmeticTheory.NUMERAL_DEF,comparisonTheory.num_cmp_numOrd,
            totoTheory.numeralOrd,arithmeticTheory.ALT_ZERO]);

val vector_defs =
 let (* open ml_translatorTheory *)
 in [fromList_def, sub_def, length_def]
 end;

val regexp_compute_thms =
  vector_defs
  @
  [ALPHABET_def, alphabet_size_def, And_def,
   charset_empty_def, charset_full_def,
   words4_bit_def, charset_mem_def, charset_union_def,
   charset_sing_def, merge_charsets_def,

   charset_cmp_def, numeral_cmp_thm, len_cmp_def,
   regexp_compare_def,regexp_compareW_def,regexp_compare_eq,regexp_leq_def,

   build_char_set_def, Sigma_def, Empty_def, Epsilon_def, catstring_def,
   assoc_cat_def, build_cat_def, build_neg_def, build_star_def,
   flatten_or_def, remove_dups_def, build_or_def,
   nullable_def, nullableW_def, smart_deriv_thm, (* smart_deriv_def *) normalize_def,
   transitions_def, build_table_def, extend_states_def,
   insert_regexp_def, mem_regexp_def, relationTheory.inv_image_def,

   dom_Brz_alt_eqns,SIMP_RULE bool_ss [dom_Brz_alt_equal] exec_Brz_def,
   Brzozo_def, Brzozowski_exec_Brz, MAXNUM_32_def,
   get_accepts_def, numLib.SUC_RULE (vec_mapTheory.alist_to_vec_def),
   accepts_to_vector_def, table_to_vectors_def,
   compile_regexp_def, exec_dfa_def, regexp_matcher_def,

   mergesort_def, mergesortN_def,sort2_def,sort3_def,merge_def,
   balanced_mapTheory.empty_def,
   balanced_mapTheory.member_def,
   balanced_mapTheory.insert_def,
   balanced_mapTheory.lookup_def,
   balanced_mapTheory.singleton_def,
   balanced_mapTheory.balanceL_def,
   balanced_mapTheory.balanceR_def,
   balanced_mapTheory.ratio_def,
   balanced_mapTheory.size_def,
   balanced_mapTheory.delta_def,
   balanced_mapTheory.foldrWithKey_def,
   (* adding stuff revealed by computeLib.unmapped *)
   combinTheory.o_DEF, combinTheory.I_THM, combinTheory.C_DEF, combinTheory.FAIL_DEF,
   rich_listTheory.SPLITP_AUX_def, rich_listTheory.SPLITP_compute,rich_listTheory.SEG_compute
 ];

(*---------------------------------------------------------------------------*)
(* The complete compset                                                      *)
(*---------------------------------------------------------------------------*)

fun regexp_compset() =
 let open computeLib
     val compset = listLib.list_compset()
     val _ = optionLib.OPTION_rws compset
     val _ = pairLib.add_pair_compset compset
     val _ = pred_setLib.add_pred_set_compset compset
     val _ = wordsLib.add_words_compset true compset
     val _ = stringLib.add_string_compset compset
     val _ = add_datatype_info compset (valOf(TypeBase.fetch ``:ordering``))
     val _ = add_datatype_info compset (valOf(TypeBase.fetch ``:('a,'b)balanced_map``))
     val _ = add_datatype_info compset (valOf(TypeBase.fetch ``:charset``))
     val _ = add_datatype_info compset (valOf(TypeBase.fetch ``:regexp``))
     val _ = add_thms regexp_compute_thms compset
 in
   compset
 end;

(*---------------------------------------------------------------------------*)
(* Evaluator based on the compset                                            *)
(*---------------------------------------------------------------------------*)

val compset = regexp_compset();

val check_these_consts = computeLib.unmapped compset;

val regexpEval = computeLib.CBV_CONV compset;

(*
max_print_depth := 25;

fun compile q =
  regexpEval ``compile_regexp ^(mk_regexp(Regexp_Type.fromQuote q))``;

val regexp_tm = mk_regexp(Regexp_Type.fromQuote `a`);
*)

val Brzozowski_partial_eval_alt =
   SIMP_RULE bool_ss [dom_Brz_alt_equal] Brzozowski_partial_eval;

fun hol_matcher r =
 let open listSyntax regexpSyntax
     val _ = stdErr_print "Compiling regexp to DFA by deduction (can be slow) :\n"
     val regexp_tm = regexpSyntax.mk_regexp r
     val compile_thm = Count.apply regexpEval ``regexp_compiler$compile_regexp ^regexp_tm``
     val triple = rhs (concl compile_thm)
     val [t1,t2,t3] = strip_pair triple
     val start_state_thm = regexpEval ``lookup regexp_compare (normalize ^regexp_tm) ^t1``
     val dom_Brz_thm = EQT_ELIM (Count.apply regexpEval
                      ``dom_Brz_alt empty [normalize ^regexp_tm]``)
     val hyps_thm = LIST_CONJ [compile_thm, start_state_thm,dom_Brz_thm]
     val thm = SIMP_RULE list_ss [fromList_Vector,ORD_BOUND,alphabet_size_def]
                       (SPEC regexp_tm Brzozowski_partial_eval_conseq)
     val dfa_thm = MATCH_MP thm hyps_thm
     fun match_string_by_proof s =
      let val stm = stringLib.fromMLstring s
          val dfa_thm1 = SPEC stm dfa_thm
       (* val (string_ok_tm,_) = dest_imp (concl dfa_thm1)
          val _ = stdErr_print "Checking input string is in alphabet ... "
          val string_ok_thm = EQT_ELIM(regexpEval string_ok_tm)
          val _ = stdErr_print "it is.\n"
          val dfa_thm2 = MP dfa_thm1 string_ok_thm
        *)
          val dfa_thm2 = dfa_thm1
          val _ = stdErr_print ("Running DFA on string: "^Lib.quote s^" ... ")
          val dfa_exec_thm = regexpEval (lhs(concl dfa_thm2))
          val verdict = (boolSyntax.T = rhs(concl dfa_exec_thm))
          val _ = if verdict then stdErr_print "accepted.\n" else stdErr_print "rejected.\n"
      in
        verdict
      end
     val eq_tm = snd(strip_forall (concl dfa_thm))
     val (_,[final,table,start,_]) = strip_comb(boolSyntax.lhs eq_tm)
     val ifinal = List.map (equal boolSyntax.T)
                  (fst(listSyntax.dest_list (dest_vector final)))
     val istart = numSyntax.int_of_term start
     val rows1 = dest_vector table
     fun dest_row row =
        let val opts = fst (listSyntax.dest_list row)
        in List.map (numSyntax.int_of_term o optionSyntax.dest_some) opts
        end
     val rows2 = fst(listSyntax.dest_list(snd(listSyntax.dest_map rows1)))
     val itable = List.map dest_row rows2
     val len = length ifinal
     val _ = stdErr_print (Int.toString len^" states.\n")
 in
     {certificate = SOME dfa_thm,
      matchfn = match_string_by_proof,
      table = Vector.fromList (map Vector.fromList itable),
      start = istart,
      final = Vector.fromList ifinal}
 end;


datatype evaluator = HOL | SML ;

fun matcher HOL = hol_matcher
  | matcher SML = sml_matcher;

fun dfa_by_proof (name,r) =
 let val name = if Lexis.ok_identifier name then name
               else (HOL_MESG (Lib.quote name^
                       " is not a suitable identifier, using \"foo\" instead");
                     "foo")
     val {certificate, start,table,final,matchfn} = hol_matcher r
     val SOME thm = certificate
     val eqn = snd(dest_forall(concl thm))
     val (exec_dfa,[finals,table,start,s]) = strip_comb(lhs eqn)
     val finals_var = mk_var(name^"_finals",type_of finals)
     val table_var = mk_var(name^"_table",type_of table)
     val start_var = mk_var(name^"_start",type_of start)
     val finals_def = Define `^finals_var = ^finals`
     val table_def = Define `^table_var = ^table`
     val start_def = Define `^start_var = ^start`
     val thm' = CONV_RULE (BINDER_CONV
                  (LHS_CONV (REWRITE_CONV [GSYM finals_def, GSYM table_def, GSYM start_def])))
		  thm
     val thm'' = LIST_CONJ [thm',table_def, finals_def, start_def]
 in
   save_thm(name^"_regexp_compilation",thm'')
 end;


(*---------------------------------------------------------------------------*)
(* Reasoner for character sets. charset_conv converts terms of the form      *)
(*                                                                           *)
(*   regexp_lang (Chset cs)                                                  *)
(*                                                                           *)
(* into theorems of the form                                                 *)
(*                                                                           *)
(*   |- regexp_lang (Chset cs) = {#"c1"; ...; #"cn"}                         *)
(*                                                                           *)
(* where c1 ... cn are the elements of cs.                                   *)
(*---------------------------------------------------------------------------*)

fun charset_term_elts (cs:term) = 
  Regexp_Type.charset_elts (regexpSyntax.term_to_charset cs);

val csvar = mk_var("cs",regexpSyntax.charset_ty);
val regexp_chset_pat = ``regexp$regexp_lang ^(regexpSyntax.mk_chset csvar)``;

fun char_tac (asl,c) = 
    let val ctm = fst(dest_eq (last (strip_conj (snd (dest_exists c)))))
    in Q.EXISTS_TAC `ORD ^ctm` >> EVAL_TAC
    end

val tactic = 
   RW_TAC (list_ss ++ pred_setLib.PRED_SET_ss)
          [pred_setTheory.EXTENSION,
           regexpTheory.regexp_lang_def,
           charsetTheory.charset_mem_def,
           charsetTheory.alphabet_size_def,EQ_IMP_THM]
    >> TRY (ntac 2 (pop_assum mp_tac)
            >> Q.ID_SPEC_TAC `c`
            >> REPEAT (CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL))
            >> rw_tac bool_ss []
            >> NO_TAC)
    >> W char_tac;

fun charset_conv tm = 
 case total (match_term regexp_chset_pat) tm
  of NONE => raise ERR "charset_conv" 
                    "expected ``regexp_lang (Chset cs)`` term"
  | SOME (theta, _) => 
     let open pred_setSyntax
         val chars = charset_term_elts (subst theta csvar)
         val char_tms = map fromMLchar chars
         val string_tms = map (fromMLstring o String.str) chars
         val the_goal = mk_eq(tm, mk_set string_tms)
  in
     prove(the_goal,tactic)
  end

val charset_conv_ss = 
  simpLib.std_conv_ss
    {name="charset_conv",
     conv = charset_conv, 
     pats = [regexp_chset_pat]}

end (* regexpLib *)
