structure regexpLib :> regexpLib = 
struct

open HolKernel boolLib bossLib;
open pairLib optionLib pred_setLib listLib stringLib;
open listTheory stringTheory arithmeticTheory pred_setTheory 
     sortingTheory mergesortTheory comparisonTheory balanced_mapTheory 
     charsetTheory regexpTheory vec_mapTheory regexp_compilerTheory; 
open Regexp_Type regexpSyntax;

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
   zip_def, genlist_def, toListAux_def, toList_def,
   vector_slice_cmp_def, vector_cmp_def,
   len_cmp_def, bool_cmp_def,
   all_unset_def, all_set_def, charset_empty_def, charset_full_def, 
   charset_mem_def, charset_sing_def, 
   charset_union_def, charset_insert_def, merge_charsets_def, charset_cmp_def,
   numeral_cmp_thm, comparisonTheory.list_cmp_def,
   
   regexp_compare_def,regexp_compareW_def,regexp_compare_eq,regexp_leq_def, 

   build_char_set_def, Sigma_def, Empty_def, Epsilon_def, catstring_def,
   assoc_cat_def, build_cat_def, build_neg_def, build_star_def, 
   flatten_or_def, remove_dups_def, build_or_def, 
   nullable_def, nullableW_def, smart_deriv_def, normalize_def, 
   transitions_def, build_table_def, extend_states_def,
   insert_regexp_def, mem_regexp_def, relationTheory.inv_image_def, 

   dom_Brz_alt_eqns, SIMP_RULE bool_ss [dom_Brz_alt_equal] exec_Brz_def, 
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
   combinTheory.o_DEF, combinTheory.I_THM,   combinTheory.K_DEF, combinTheory.FAIL_DEF,
   basicSizeTheory.bool_size_def,
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
(*     val _ = wordsLib.add_words_compset true compset *)
     val _ = stringLib.add_string_compset compset
     val _ = add_datatype_info compset (valOf(TypeBase.fetch ``:cpn``))
     val _ = add_datatype_info compset (valOf(TypeBase.fetch ``:regexp``))
     val _ = add_datatype_info compset (valOf(TypeBase.fetch ``:('a,'b)balanced_map``))
     val _ = add_datatype_info compset (valOf(TypeBase.fetch ``:'a vector``))
     val _ = add_thms regexp_compute_thms compset
 in
   compset
 end;

(*---------------------------------------------------------------------------*)
(* Evaluator based on the compset                                            *)
(*---------------------------------------------------------------------------*)

val compset = regexp_compset();

val unmapped_consts = computeLib.unmapped compset;

val regexpEval = computeLib.CBV_CONV compset;


(*
max_print_depth := 25;

val regexp_tm = mk_regexp(Regexp_Type.fromQuote `a`);

regexpEval ``compile_regexp ^regexp_tm``;

regexpEval ``exec_Brz empty [^regexp_tm] (1,singleton ^regexp_tm 0,[]) MAXNUM_32``;
regexpEval ``transitions ^regexp_tm``;
regexpEval ``insert_regexp ^regexp_tm empty``;
regexpEval ``remove_dups (MAP SND (transitions ^regexp_tm))``;
regexpEval ``build_table (transitions ^regexp_tm) ^regexp_tm (1,singleton ^regexp_tm 0,[])``;
regexpEval ``extend_states 1n (singleton ^regexp_tm 0) [] (transitions ^regexp_tm)``;

val (_,[next_state,state_map,trans,_]) = strip_comb ``extend_states 1n (singleton ^regexp_tm 0) [] (transitions ^regexp_tm)``;
val arcs_tm = rhs(concl (regexpEval ``transitions ^regexp_tm``));
val arcs = fst(listSyntax.dest_list arcs_tm);

fun opr [] next_state state_map trans = ([],next_state,state_map,trans)
  | opr (cr::t) next_state state_map trans = 
     let val _ = print "."
         val (c,r') = pairSyntax.dest_pair cr
         val opt = rhs(concl (regexpEval ``lookup regexp_compare ^(r') ^state_map``))
     in 
       if optionSyntax.is_some opt
        then let val n = optionSyntax.dest_some opt
                 val trans = rhs(concl (regexpEval ``((^c,^n)::^trans)``))
             in opr t next_state state_map trans
             end
        else let val next_state = rhs (concl (regexpEval ``^next_state + 1``))
                 val state_map = rhs (concl (regexpEval ``insert regexp_compare ^(r') 1n ^state_map``))
                 val trans = rhs(concl (regexpEval ``((^c,1n)::^trans)``))
             in opr t next_state state_map trans
             end
     end;

val res = opr arcs next_state state_map trans;

extend_states_def
 |- extend_states next_state state_map trans [] = (next_state,state_map,trans)) ∧
    extend_states next_state state_map trans ((c,r')::t) =
     case lookup regexp_compare r' state_map
      of NONE => extend_states 
                  (next_state + 1)
                  (insert regexp_compare r' next_state state_map)
                  ((c,next_state)::trans)
                  t
     | SOME n => extend_states next_state state_map ((c,n)::trans) t:
   thm


*)

(* Apply optimization for dom_Brz *)

val Brzozowski_partial_eval_alt = 
   SIMP_RULE bool_ss [dom_Brz_alt_equal] Brzozowski_partial_eval;

fun hol_matcher r = 
 let open listSyntax regexpSyntax
     val _ = print "Compiling regexp to DFA by deduction (can be slow) :\n"
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
          val _ = print "Checking input string is in alphabet ... "
          val string_ok_thm = EQT_ELIM(regexpEval string_ok_tm)
          val _ = print "it is.\n"
          val dfa_thm2 = MP dfa_thm1 string_ok_thm
        *)
          val dfa_thm2 = dfa_thm1
          val _ = print ("Running DFA on string: "^Lib.quote s^" ... ")
          val dfa_exec_thm = regexpEval (lhs(concl dfa_thm2))
          val verdict = (boolSyntax.T = rhs(concl dfa_exec_thm))
          val _ = if verdict then print "accepted.\n" else print "rejected.\n"
      in 
        verdict
      end
     val eq_tm = snd(strip_forall (concl dfa_thm))
     val (_,[final,table,start,_]) = strip_comb(boolSyntax.lhs eq_tm)
     val ifinal = List.map (equal boolSyntax.T) 
                  (fst(dest_list (dest_vector final)))
     val istart = numSyntax.int_of_term start
     fun dest_row row = 
        let val opts = fst (dest_list row)
        in List.map (numSyntax.int_of_term o optionSyntax.dest_some) opts
        end
     val rows1 = dest_vector table
     val rows2 = fst(dest_list(snd(dest_map rows1)))
     val itable = List.map dest_row rows2
     val len = length ifinal
     val _ = print (Int.toString len^" states.\n")
 in 
     {certificate = SOME dfa_thm,
      matchfn = match_string_by_proof,
      table = Vector.fromList (map Vector.fromList itable),
      start = istart,
      final = Vector.fromList ifinal}
 end;

fun sml_matcher r = 
 let val {matchfn,start,table,final} = Regexp_Match.vector_matcher r
     val _ = print (Int.toString(Vector.length final)^" states.\n")
 in {certificate = NONE:thm option,
     matchfn = matchfn,
     table = table,
     start = start,
     final = final}
 end;

datatype evaluator = HOL | SML ;

fun matcher HOL = hol_matcher 
  | matcher SML = sml_matcher;


fun dfa_by_proof (name,q) = 
 let val name = if Lexis.ok_identifier name then name
               else (HOL_MESG (Lib.quote name^
                       " is not a suitable identifier, using \"foo\" instead");
                     "foo")
     val {certificate, start,table,final,matchfn} = hol_matcher (Regexp_Type.fromQuote q)
     val SOME thm = certificate
     val eqn = snd(dest_forall(concl thm))
     val (exec_dfa,[finals,table,start,s]) = strip_comb(lhs eqn)
     val finals_var = mk_var(name^"_finals",type_of finals)
     val table_var = mk_var(name^"_table",type_of table)
     val start_var = mk_var(name^"_start",type_of start)
     val finals_def = Define `^finals_var = ^finals`
     val table_def = Define `^table_var = ^table`
     val start_def = Define `^start_var = ^start`
     val thm' = SIMP_RULE std_ss 
                 [GSYM finals_def, GSYM table_def, GSYM start_def]
                thm
 in
   save_thm(name^"_regexp_compilation",thm')
 end;

end (* regexpLib *)
