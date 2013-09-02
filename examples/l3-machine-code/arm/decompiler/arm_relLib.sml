structure arm_relLib =
struct

local

open HolKernel Parse boolLib bossLib Lib;
open armTheory armLib arm_stepTheory pred_setTheory pairTheory optionTheory;
open arithmeticTheory wordsTheory wordsLib addressTheory combinTheory pairSyntax;
open sumTheory whileTheory;

open arm_relTheory progTheory helperLib;

val cond_var = mk_var("cond",``:bool``)

val (spec,_,_,_) = arm_decompLib.l3_arm_tools

val arm_assert = ARM_ASSERT_def |> SPEC_ALL
   |> REWRITE_RULE [arm_FP_REGS_def,set_sepTheory.STAR_ASSOC]
   |> SIMP_RULE (bool_ss++star_ss) [] |> GSYM

val targets = list_dest dest_star (arm_assert |> GSYM |> concl |> rand)

val precond_thm = prove(
  ``!b. precond b = cond (Abbrev b): 'a set set``,
  SIMP_TAC std_ss [markerTheory.Abbrev_def,set_sepTheory.precond_def]);

fun add_prime v = mk_var(fst (dest_var v) ^ "'",type_of v)

val PAIR_LEMMA = prove(
  ``((x1 = y1) ==> (x2 = y2) ==> b) ==>
    (((x2,x1) = (y2:'a,y1:'b)) ==> b)``,
  SIMP_TAC std_ss []);

fun old_to_new th = let
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [precond_thm]
  val th = th |> REWRITE_RULE [SPEC_MOVE_COND] |> UNDISCH_ALL
  val (_,pre,_,_) = dest_spec (concl th)
  val ps = list_dest dest_star pre
  fun find_match [] tm = fail()
    | find_match (x::xs) tm =
        match_term x tm handle HOL_ERR _ => find_match xs tm
  val frame = filter (fn tm => not (can (find_match ps) tm)) targets
  val xs = filter (fn tm => (can (find_match ps) tm)) targets
           |> map (fn tm => fst (find_match ps tm)) |> foldr (fn (x,y) => x @ y) []
  val th = INST xs th
  val th = SPEC_FRAME_RULE th (list_mk_star frame (type_of (hd ps)))
  val th = th |> CONV_RULE (PRE_CONV (SIMP_CONV (bool_ss++star_ss) [])
                   THENC REWRITE_CONV [arm_assert,set_sepTheory.SEP_CLAUSES])
  val (_,_,_,post) = dest_spec (concl th)
  val ps = list_dest dest_star post
  val diff = filter (fn tm => not (mem tm ps)) targets
  val ds = map rator diff
  fun find_similar x xs = first (fn t => rator t = x) xs
  val xs = map (fn d => (rand (find_similar d targets),
                         rand (find_similar d ps))) ds
  val simple = filter (is_var o fst) xs
  val rest = filter (not o is_var o fst) xs
  val ts = map (fn (x,y) => (rator x, combinSyntax.mk_update(rand x,y))) rest
  val fs = map (rator o fst) rest |> all_distinct
  val all = simple @ map (fn f => let
    val f = hd fs
    val ups = filter (fn (x,y) => x = f) ts |> map snd
    val t = foldr mk_comb f ups
    in (f,t) end) fs
  val simp = SIMP_CONV (srw_ss()++star_ss) [APPLY_UPDATE_THM]
  val lemma = arm_assert |> INST (map (fn (x,y) => x |-> y) all)
             |> CONV_RULE (RATOR_CONV simp)
  val th = th |> CONV_RULE (POST_CONV simp THENC REWRITE_CONV [lemma])
  val th = th |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
              |> CONV_RULE ((RATOR_CONV o RAND_CONV) (REWRITE_CONV []))
  val th = MATCH_MP INTRO_TRIPLE_L3_ARM th
  val th = SPEC cond_var th |> REWRITE_RULE []
  (* abbreviate posts *)
  val pat = th |> concl |> rator |> rator |> rand
  val post = th |> concl |> rand
  fun abbrev_conv ignore pat post =
    if ignore pat then ALL_CONV post
    else if is_var pat then
      if pat = post then ALL_CONV post else
        ASSUME (mk_eq(post,add_prime pat))
    else if is_comb pat then
      (RAND_CONV (abbrev_conv ignore (rand pat)) THENC
       RATOR_CONV (abbrev_conv ignore (rator pat))) post
    else if pat = post then ALL_CONV post
    else NO_CONV post
  val r15 = mk_var("r15",``:word32``)
  val th = th |> CONV_RULE (RAND_CONV (abbrev_conv (fn x => x = r15) pat))
  val th = th |> DISCH_ALL
  val th = repeat (MATCH_MP PAIR_LEMMA) th |> UNDISCH_ALL
  in th end

val fv_spec_tm = arm_assert |> concl |> free_vars

in

val l3_triple = cache (fn hex => let
  val thms = spec hex
  fun is_NONE NONE = true | is_NONE _ = false
  fun apply ((th1,x1,y1),NONE) =
        if is_NONE y1 then fail() else
          ((old_to_new th1,x1,y1),NONE)
    | apply ((th1,x1,y1),SOME (th2,x2,y2)) =
        if is_NONE y1 then fail() else
          ((old_to_new th1,x1,y1),SOME (old_to_new th2,x2,y2))
  in apply thms end handle HOL_ERR _ => failwith ("l3_triple: " ^ hex))

val (swap_primes,SWAP_PRIMES_RULE) = let
  val vs = (cond_var :: fv_spec_tm) |> map (fn v => (v,add_prime v))
  val ss = map (fn (x,y) => x |-> y) vs @ map (fn (x,y) => y |-> x) vs
  in (subst ss, INST ss) end

end

end
