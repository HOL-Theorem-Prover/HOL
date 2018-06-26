structure straightlineLib :> straightlineLib =
struct

open HolKernel boolLib bossLib Parse;
open listTheory wordsTheory pred_setTheory arithmeticTheory wordsLib pairTheory;
open set_sepTheory progTheory helperLib addressTheory straightlineTheory;
open core_decompilerLib tripleTheory derive_specsLib;

open backgroundLib file_readerLib stack_introLib stack_analysisLib writerLib;

val add_DO_NOTHING = let
  val c = REWR_CONV (GSYM DO_NOTHING_def)
  in CONV_RULE (POST_CONV c THENC PRE_CONV c) end

local
  val produce_TRIPLE_fail = ref TRUTH;
  val index = ref (0:int);
  fun next_index () = (index := (!index) + 1; (!index))
in
  fun produce_TRIPLE th = let
    val all_parts = arm_assert_def
      |> SPEC_ALL |> concl |> dest_eq |> snd
      |> list_dest dest_star
    (* move bool conditions into assums *)
    val th = CONV_RULE (PRE_CONV (MOVE_OUT_CONV ``arm_PC``)) th
    val th = MATCH_MP SPEC_VAR_PC th |> SPEC_ALL |> UNDISCH_ALL
    val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
                |> UNDISCH_ALL
    (* make pre have all parts *)
    val (_,pre,_,_) = dest_spec (concl th)
    val ps = list_dest dest_star pre
    val ps' = map rator ps
    val missing_parts = filter (fn p => not (mem (rator p) ps')) all_parts
    val frame = list_mk_star missing_parts (type_of pre)
    val th = SPEC_FRAME_RULE th frame
    val th = th |> CONV_RULE (PRE_CONV (STAR_REWRITE_CONV (GSYM arm_assert_def)))
    val th = th |> CONV_RULE (POST_CONV (STAR_REWRITE_CONV (GSYM arm_assert_def)))
    val th = th |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
    val th = if is_imp (concl th) then th else DISCH T th
    val th = MATCH_MP TRIPLE_INTRO (DISCH_ALL th)
    val th = th |> REWRITE_RULE []
    val tuple = th |> concl |> rator |> rator |> rand
    val post = th |> concl |> rand
    val postfix = "@" ^ (int_to_string (next_index ()))
    val vs = free_vars tuple
             |> map (fn v => v |-> mk_var(fst (dest_var v) ^ postfix,type_of v))
    val new_tuple = subst vs tuple
    fun mk_new_post (post,tuple,new_tuple) =
      if not (pairSyntax.is_pair tuple) then
        if post = tuple then REFL post else ASSUME (mk_eq(post,new_tuple))
      else let
        val (lhs1,rhs1) = dest_pair post
        val (lhs2,rhs2) = dest_pair tuple
        val (lhs3,rhs3) = dest_pair new_tuple
        val th1 = mk_new_post (lhs1,lhs2,lhs3)
        val th2 = mk_new_post (rhs1,rhs2,rhs3)
        val lemma = CONJ (DISCH_ALL th1) (DISCH_ALL th2)
        val th = UNDISCH_ALL (MATCH_MP COMBINE1 lemma) handle HOL_ERR _ =>
                 UNDISCH_ALL (MATCH_MP COMBINE2 lemma) handle HOL_ERR _ =>
                 UNDISCH_ALL (MATCH_MP COMBINE3 lemma) handle HOL_ERR _ =>
               UNDISCH_ALL (MATCH_MP COMBINE4 lemma)
         in th end
    val lemma = mk_new_post (post,tuple,new_tuple)
    val th = th |> CONV_RULE (RAND_CONV (K lemma))
    in add_DO_NOTHING th end
    handle HOL_ERR e => (produce_TRIPLE_fail := th; raise (HOL_ERR e));
  fun last_fail () = !produce_TRIPLE_fail
end

fun triple_compose_list [] = add_DO_NOTHING TRIPLE_NOP
  | triple_compose_list (th1::thms) =
      let val th2 = triple_compose_list thms
      in compose th1 th2 end

fun remove_var_annotations th = let
  fun fix_var_name v = let
    val (s,ty) = dest_var v
    val t = String.tokens (fn c => c = #"@") s
    in if length t > 1 then mk_var (hd t,ty) else fail() end
  fun fix_names tm =
    if is_comb tm then
      (RATOR_CONV fix_names THENC RAND_CONV fix_names) tm
    else let
      val (n,body) = dest_abs tm
      in (ALPHA_CONV (fix_var_name n) THENC ABS_CONV fix_names) tm end
      handle HOL_ERR _ => ALL_CONV tm
  in CONV_RULE fix_names th end

local
  val format = SKIP_TAG_def |> SPEC_ALL |> concl |> dest_eq |> fst |> rator
in
  val is_SKIP_TAG = can (match_term format)
end

fun split_at P [] [] = []
  | split_at P [] aux = [rev aux]
  | split_at P (x::xs) [] =
      if P x then split_at P xs [] else split_at P xs [x]
  | split_at P (x::xs) aux =
      if P x then rev aux :: split_at P xs [] else split_at P xs (x::aux)

fun compose_all_for sec_name = let
  val xs = derive_specs_for sec_name
  val ys = map (fn (_,(th,_,_),_) => th) xs
  val yss = split_at (can (find_term is_SKIP_TAG) o concl) ys []
  val thms = map (fn ys => let
    val zs = map produce_TRIPLE ys
    val th = triple_compose_list zs
    val th = remove_var_annotations th
             |> REWRITE_RULE (!code_abbreviations)
             |> REWRITE_RULE [DO_NOTHING_def]
    in th end) yss
  in thms end

fun triples_for base_name = let
  val _ = read_files base_name []
  in map (fn n => (n,compose_all_for n)) (section_names ()) end

end
