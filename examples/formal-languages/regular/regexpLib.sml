structure regexpLib :> regexpLib =
struct

open HolKernel boolLib bossLib;
open pairLib optionLib pred_setLib listLib stringLib wordsLib;
open listTheory stringTheory arithmeticTheory pred_setTheory
     sortingTheory mergesortTheory comparisonTheory balanced_mapTheory vec_mapTheory
     charsetTheory regexpTheory regexp_compilerTheory regexp_parserTheory;

open Regexp_Type regexpSyntax regexpMisc;

local open Regexp_Numerics DFA_Codegen in end;

val ERR = mk_HOL_ERR "regexpLib";

fun gen_sml_dfa r =
 let val {matchfn,start,table,final} = Regexp_Match.vector_matcher r
     val _ = stdErr_print (Int.toString(Vector.length final)^" states.\n")
 in {certificate = NONE:thm option,
     aux = NONE,
     matchfn = matchfn,
     table = table,
     start = start,
     final = final}
 end;

val numeral_cmp_thm = Q.prove
(`(num_cmp (NUMERAL x) (NUMERAL y) = num_cmp x y) /\
  (num_cmp (NUMERAL x) y = num_cmp x y) /\
  (num_cmp x (NUMERAL y) = num_cmp x y) /\
  (num_cmp 0 n = num_cmp ZERO n) /\
  (num_cmp n 0 = num_cmp n ZERO) /\
  (num_cmp ZERO ZERO = Equal) /\
  (num_cmp ZERO (BIT1 y) = Less) /\
  (num_cmp ZERO (BIT2 y) = Less) /\
  (num_cmp (BIT1 x) ZERO = Greater) /\
  (num_cmp (BIT2 x) ZERO = Greater) /\
  (num_cmp (BIT1 x) (BIT1 y) = num_cmp x y) /\
  (num_cmp (BIT2 x) (BIT2 y) = num_cmp x y) /\
  (num_cmp (BIT1 x) (BIT2 y) = case num_cmp x y of Greater => Greater | _ => Less) /\
  (num_cmp (BIT2 x) (BIT1 y) = case num_cmp x y of Less => Less | _ => Greater)`,
 METIS_TAC [arithmeticTheory.NUMERAL_DEF,comparisonTheory.num_cmp_numOrd,
            totoTheory.numeralOrd,arithmeticTheory.ALT_ZERO]);

val vector_defs =
 let (* open ml_translatorTheory *)
 in [fromList_def, sub_def, length_def]
 end;


val exec_dfa_thms = exec_dfa_def :: vector_defs;

val base_compute_thms =
  vector_defs
  @
  [ALPHABET_def, alphabet_size_def, And_def,
   charset_empty_def, charset_full_def, charset_sing_def,
   merge_charsets_def, charset_cmp_def, numeral_cmp_thm, len_cmp_def,
   regexp_compare_def, regexp_leq_def, regexp_compareW_compute,

   build_char_set_def, DOT_def, Empty_def, Epsilon_def, catstring_def,
   assoc_cat_def, build_cat_def, build_neg_def, build_star_def,
   flatten_or_def, remove_dups_def, build_or_def,
   nullable_def, nullableW_def, smart_deriv_thm, normalize_def,
   build_table_def, extend_states_def,
   insert_regexp_def, mem_regexp_def, relationTheory.inv_image_def,

   get_accepts_def, numLib.SUC_RULE (vec_mapTheory.alist_to_vec_def),
   accepts_to_vector_def, table_to_vectors_def,

   mergesort_def, mergesortN_def,sort2_def,sort3_def,merge_def,
   balanced_mapTheory.null_def,
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
   balanced_mapTheory.deleteFindMin_def,
   balanced_mapTheory.fromList_def,

   (* adding stuff revealed by computeLib.unmapped *)
   combinTheory.o_DEF, combinTheory.I_THM, combinTheory.C_DEF,
   combinTheory.FAIL_DEF, rich_listTheory.SPLITP_AUX_def,
   rich_listTheory.SPLITP_compute,rich_listTheory.SEG_compute
 ];

fun chsets_of regexp =
 let open HOLset
     fun trav (x as Chset _) set = add(set,x)
       | trav (Star r) set   = trav r set
       | trav (Neg r) set    = trav r set
       | trav (Cat(r,s)) set = trav r (trav s set)
       | trav (Or rlist) set = itlist trav rlist set
 in
   listItems (trav regexp (empty regexp_compare))
 end

val alphabet_tms = map numSyntax.term_of_int (upto 0 255)

val charset_mem_tm = prim_mk_const{Name="charset_mem",Thy="charset"};
val smart_deriv_tm = prim_mk_const{Name="smart_deriv",Thy="regexp"};
val build_or_tm    = prim_mk_const{Name="build_or",   Thy="regexp"};
val transitions_tm = prim_mk_const{Name="transitions",Thy="regexp_compiler"};

val Empty_charset =
   Empty_def |> SIMP_RULE std_ss [charset_empty_def] |> concl |> rhs |> rand

val DOT_charset = DOT_def |> concl |> rhs |> EVAL |> concl |> rhs |> rand

val charset_mem_conv =
 let val cs_memEval =
      let open computeLib
          val compset = listLib.list_compset()
      in
          wordsLib.add_words_compset true compset
        ; add_datatype_info compset (valOf(TypeBase.fetch ``:charset``))
        ; add_thms [alphabet_size_def, words4_bit_def, charset_mem_def] compset
        ; computeLib.CBV_CONV compset
      end
     val pairs = cross alphabet_tms [Empty_charset, DOT_charset]
     val probs = map (fn (x,y) => list_mk_comb(charset_mem_tm, [x,y])) pairs
     val table = List.map (fn x => (x,cs_memEval x)) probs
     val init_Map = Redblackmap.fromList Term.compare table
 in fn () =>
    let val theMap = ref init_Map
    in fn tm =>
       Redblackmap.find (!theMap,tm)
       handle NotFound =>
       let val _ = print "previously unseen charset ... "
           val cset_tm = rand tm
           val pairs = cross alphabet_tms [cset_tm]
           val probs = map (fn (x,y) => list_mk_comb(charset_mem_tm, [x,y])) pairs
           val table = List.map (fn x => (x,cs_memEval x)) probs
           val _ = (theMap := Redblackmap.insertList (!theMap, table))
           val _ = print "tabulated.\n"
       in
          Redblackmap.find (!theMap,tm)
       end
    end
 end;

val charset_union_conv =
 let val charset_unionEval =
        let open computeLib
            val compset = listLib.list_compset()
        in wordsLib.add_words_compset true compset
         ; add_datatype_info compset (valOf(TypeBase.fetch ``:charset``))
         ; add_thms [charset_union_def, charset_empty_def] compset
         ; CBV_CONV compset
        end
 in
   fn () =>
   let val theMap = ref (Redblackmap.mkDict Term.compare)
   in fn tm =>
      Redblackmap.find (!theMap,tm)
      handle NotFound =>
        let val thm = charset_unionEval tm
            val _ = (theMap := Redblackmap.insert(!theMap, tm,thm))
        in
           thm
        end
   end
end;


(*---------------------------------------------------------------------------*)
(* Assumes that input tm has form "transitions r"                            *)
(*---------------------------------------------------------------------------*)

fun transitions_conv compset =
 let open regexpSyntax listSyntax
     val smart_deriv_or = el 5 (CONJUNCTS smart_deriv_thm)
     val sdi_tms = map (curry mk_comb smart_deriv_tm) alphabet_tms
     val RW_MAP = PURE_REWRITE_CONV [listTheory.MAP]
     val RW_SD_OR = PURE_REWRITE_RULE [GSYM smart_deriv_or]
     val transitions_CONV1 =
       PURE_REWRITE_CONV [transitions_def,listTheory.MAP,ALPHABET_def]
       THENC DEPTH_CONV BETA_CONV
     val Eval = computeLib.CBV_CONV compset
     val theMap = ref (Redblackmap.mkDict Term.compare)
 in
 fn tm =>
   Redblackmap.find (!theMap,tm)
   handle NotFound =>
   let val r = rand tm
   in if not (is_or r) then
        let val thm = (REWR_CONV transitions_def THENC Eval) tm
            val _ = (theMap := Redblackmap.insert(!theMap,tm,thm))
        in thm
        end
      else
      let val rlist = dest_or r
          fun sdtms r = map (C (curry mk_comb) r) sdi_tms
          val sdlists = map sdtms rlist
          val thmlists = map (map Eval) sdlists
          val orlists = transpose thmlists
          fun map_sd n = ``MAP (smart_deriv ^n) ^(rand r)``
          val map_tms = map map_sd alphabet_tms
          val map_thms = map RW_MAP map_tms
          val map_thms' = map2 PURE_REWRITE_RULE orlists map_thms
          val map_thms'' = map (AP_TERM build_or_tm) map_thms'
          val build_or_thms = map (CONV_RULE (RHS_CONV Eval)) map_thms''
          val smart_deriv_thms = map RW_SD_OR build_or_thms
          val thm =
             (transitions_CONV1 THENC PURE_REWRITE_CONV smart_deriv_thms) tm
      in
        theMap := Redblackmap.insert(!theMap,tm,thm)
      ; thm
      end
   end
 end;

(*---------------------------------------------------------------------------*)
(* The base compset                                                          *)
(*---------------------------------------------------------------------------*)

fun base_compset() =
 let open computeLib
     val compset = listLib.list_compset()
 in
     optionLib.OPTION_rws compset
   ; pairLib.add_pair_compset compset
   ; pred_setLib.add_pred_set_compset compset
   ; wordsLib.add_words_compset true compset
   ; stringLib.add_string_compset compset
   ; add_datatype_info compset (valOf(TypeBase.fetch ``:ordering``))
   ; add_datatype_info compset (valOf(TypeBase.fetch ``:('a,'b)balanced_map``))
   ; add_datatype_info compset (valOf(TypeBase.fetch ``:charset``))
   ; add_datatype_info compset (valOf(TypeBase.fetch ``:regexp``))
   ; add_thms base_compute_thms compset
   ; add_conv(``charset_mem``, 2, charset_mem_conv ()) compset
   ; add_conv(``charset_union``, 2, charset_union_conv()) compset
   ; add_conv(``transitions``, 1, transitions_conv compset) compset
   ; compset
 end;

fun gen_dfa_conv r =
 let val regexp_tm = regexp_to_term r
     val compset = base_compset()
     val baseEval = computeLib.CBV_CONV compset
     val dom_Brz_alt_conv = REPEATC (time (REWR_CONV dom_Brz_alt_eqns THENC baseEval))
     val _ = print "proving dom_Brz for this instance ...\n"
     val dom_Brz_thm = EQT_ELIM (Count.apply dom_Brz_alt_conv
                         ``dom_Brz_alt empty (singleton (normalize ^regexp_tm) ())``)
     val _ = print "---> done.\n"

     val _ = print "Compiling regexp ... "
     val exec_Brz_conv = REPEATC (time (REWR_CONV exec_Brz_def THENC baseEval))
     fun compile_regexp_conv regexp_tm =
       let val th1 = baseEval ``normalize ^regexp_tm``
           val nr = th1 |> concl |> rhs
           val th2 = (PURE_REWRITE_CONV [Brzozowski_exec_Brz, MAXNUM_32_def]
                      THENC exec_Brz_conv)
                ``Brzozowski empty (singleton ^nr ()) (1,singleton ^nr 0,[])``
           val _ = print "\nState transitions computed; now building DFA.\n"
       in
           compile_regexp_def
             |> SPEC regexp_tm
             |> PURE_ONCE_REWRITE_RULE [th1]
             |> CONV_RULE (ONCE_DEPTH_CONV let_CONV)
             |> PURE_ONCE_REWRITE_RULE [th2]
             |> CONV_RULE (RHS_CONV baseEval)
       end
     val compile_thm = Count.apply compile_regexp_conv regexp_tm
     val _ = print "done.\n"
     val triple = rhs (concl compile_thm)
     val [t1,t2,t3] = strip_pair triple
     val start_state_thm = baseEval ``lookup regexp_compare (normalize ^regexp_tm) ^t1``
     val hyps_thm = LIST_CONJ [compile_thm, start_state_thm,dom_Brz_thm]
     val thm = SIMP_RULE list_ss [fromList_Vector,ORD_BOUND,alphabet_size_def]
                       (SPEC regexp_tm Brzozowski_partial_eval_conseq)
     val dfa_thm = MATCH_MP thm hyps_thm
 in
   (dfa_thm,hyps_thm)
 end

fun exec_dfa_compset() =
 let open computeLib
     val compset = listLib.list_compset()
 in
     optionLib.OPTION_rws compset
   ; stringLib.add_string_compset compset
   ; add_thms exec_dfa_thms compset
   ; compset
 end;

val exec_dfa_conv = computeLib.CBV_CONV (exec_dfa_compset());

val Brzozowski_partial_eval_alt =
   SIMP_RULE bool_ss [dom_Brz_alt_equal] Brzozowski_partial_eval;


fun gen_hol_dfa r =
 let open listSyntax regexpSyntax
     val _ = stdErr_print "Compiling regexp to DFA by deduction (can be slow) :\n"
     val (dfa_thm, hyps_thm) = gen_dfa_conv r
     fun match_string_by_proof s =
       let val stm = stringLib.fromMLstring s
           val dfa_thm1 = SPEC stm dfa_thm
           val _ = stdErr_print ("Running DFA on string: "^Lib.quote s^" ... ")
           val dfa_exec_thm = exec_dfa_conv (lhs(concl dfa_thm1))
           val verdict = Teq (rhs(concl dfa_exec_thm))
           val _ = if verdict then stdErr_print "accepted.\n"
                   else stdErr_print "rejected.\n"
       in
         verdict
       end
     val eq_tm = snd(strip_forall (concl dfa_thm))
     val (_,[final,table,start,_]) = strip_comb(boolSyntax.lhs eq_tm)
     val ifinal = List.map (aconv boolSyntax.T)
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
      (* the aux field is used by the CakeML translator, see
         <cakemldir>/examples/filterProgScript.sml *)
      aux = SOME hyps_thm,
      matchfn = match_string_by_proof,
      table = Vector.fromList (map Vector.fromList itable),
      start = istart,
      final = Vector.fromList ifinal}
 end;

datatype evaluator = HOL | SML ;

fun gen_dfa HOL = gen_hol_dfa
  | gen_dfa SML = gen_sml_dfa

fun dfa_by_proof (name,r) =
 let val name = if Lexis.ok_identifier name then name
               else (HOL_MESG (Lib.quote name^
                       " is not a suitable identifier, using \"DFA\" instead");
                     "foo")
     val {certificate,aux,start,table,final,matchfn} = gen_hol_dfa r
     val SOME thm = certificate
     val eqn = snd(dest_forall(concl thm))
     val (exec_dfa,[finals,table,start,s]) = strip_comb(lhs eqn)
     val finals_var = mk_var(name^"_finals",type_of finals)
     val table_var  = mk_var(name^"_table",type_of table)
     val start_var  = mk_var(name^"_start",type_of start)
     val finals_def = Define `^finals_var = ^finals`
     val table_def  = Define `^table_var = ^table`
     val start_def  = Define `^start_var = ^start`
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


(*---------------------------------------------------------------------------*)
(* Set up default generator for interval regexps                             *)
(*---------------------------------------------------------------------------*)

val _ =
 let open Regexp_Numerics
     fun iFn p =
        twos_comp_interval LSB (interval_width Twos_comp p) p
 in
    Regexp_Type.set_intervalFn iFn
 end

end (* regexpLib *)
