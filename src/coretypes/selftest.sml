open HolKernel Parse boolLib testutils
open pairTheory sumTheory optionTheory optionSyntax
open simpLib BasicProvers boolSimps

val _ = set_trace "Unicode" 0

(* testing for sums *)
val _ = tpp "case s of INL b => b | INR c => ~c"

(* testing for options *)
val alpha_option_ty = mk_option alpha
val alphanone_t = mk_thy_const{Thy = "option", Name = "NONE", Ty = alpha_option_ty}

val _ = tprint "dest_none returns unwrapped type"
val ty = dest_none alphanone_t
val _ = if Type.compare(ty, alpha) = EQUAL then OK()
        else die "FAILED!"

val _ = tpp "case opt of NONE => T | SOME b => b"

(* tests for option monad stuff evaluation *)
val _ = convtest ("EVAL OPTION_BIND(1)", computeLib.EVAL_CONV,
                  ``OPTION_BIND (SOME T) (\x. SOME x)``, ``SOME T``)
val _ = convtest ("EVAL OPTION_BIND(2)", computeLib.EVAL_CONV,
                  “OPTION_BIND NONE (\x:bool. SOME x)”, “NONE : bool option”)

val _ = convtest ("EVAL OPTION_IGNORE_BIND(1)", computeLib.EVAL_CONV,
                  ``OPTION_IGNORE_BIND (SOME T) (SOME (\x:'a. x))``,
                  ``SOME (\x:'a. x)``)
val _ = convtest ("EVAL OPTION_IGNORE_BIND(2)", computeLib.EVAL_CONV,
                  ``OPTION_IGNORE_BIND (NONE : bool option) (SOME (\x:'a. x))``,
                  “NONE : ('a -> 'a) option”)

(* testing for pairs *)
val die = fn () => die "FAILED!\n"
fun sdie s = testutils.die ("FAILED!\n  "^s^"\n")

val _ = app tpp ["\\(x,y). x /\\ y",
                 "\\(x,y,z). x /\\ y /\\ z",
                 "\\((x,y),z). x /\\ y /\\ z",
                 "(\\(x,y,z). x /\\ y /\\ z) p",
                 "case x of (y,z) => y /\\ z",
                 "f000000000 arg000000000\n\
                 \  (case x of\n\
                 \     INL u => u inl00000000000 inl111111111\n\
                 \   | INR v => v inr00000000000 inr111111111)\n\
                 \  (arg222222222222 arg333333333 arg444444444)"
                ]

(* check LET_INTRO *)

val _ = let
  val _ = tprint "Testing pairTools.LET_INTRO"
  val _ = pairTools.LET_INTRO (ASSUME ``((x,y) = (zw)) ==> (ARB x y):bool``)
  val _ = pairTools.LET_INTRO (ASSUME ``((x,y) = (z,w)) ==> (ARB x y):bool``)
  val _ = OK()
in
  ()
end handle e => die()

(* parsing of case expressions with conditionals as arms *)
val _ = tprint "Parsing case expressions with conditional arms"
val t1 = ``case p:'a#'b of (x,y) => if y = a then x else f x y``
val t2 = ``pair_CASE (p:'a # 'b) (\x y. if y = a then x else f x y)``
val _ = if aconv t1 t2 then OK() else die()

val _ = print "**** More Inductive Definition tests ****\n"
open IndDefLib
fun checkhyps th = if null (hyp th) then ()
                   else sdie "FAILED - Hyps in theorem!"

(* emulate the example in examples/monosetScript.sml *)
val _ = print "*** Testing monoset example\n"
val _ = new_type ("t", 0)
val _ = new_type ("list", 1)
val _ = new_type ("num", 0)
val _ = new_constant ("v", ``:num -> t``)
val _ = new_constant ("app", ``:t list -> t``)
val _ = new_constant ("EVERY", ``:('a -> bool) -> 'a list -> bool``)
val _ = new_constant ("MEM", ``:'a -> 'a list -> bool``)
val _ = new_constant ("ZIP", ``:('a list # 'b list) -> ('a # 'b) list``)

val MONO_EVERY = mk_thm([], ``(!x:'a. P x ==> Q x) ==>
                              (EVERY P l ==> EVERY Q l)``)
val _ = add_mono_thm MONO_EVERY

val (red_rules, red_ind, red_cases) = Hol_reln `
  (!n. red f (v n) (v (f n))) /\
  (!t0s ts. EVERY (\ (t0,t). red f t0 t) (ZIP (t0s, ts)) ==>
            red f (app t0s) (app ts))
`;
val _ = checkhyps red_rules

(* emulate Peter's example *)
val _ = print "*** Testing Peter's example\n"
val _ = new_constant ("nil", ``:'a list``)
val _ = new_constant ("SUC", ``:num -> num``)
val _ = new_constant ("cons", ``:'a -> 'a list -> 'a list``)
val _ = new_constant ("HD", ``:'a list -> 'a``)
val _ = new_constant ("TL", ``:'a list -> 'a list``)
val (ph_rules, ph_ind, ph_cases) = Hol_reln`
  (WF_CX nil) /\
  (!s ty cx. WF_CX cx /\ WF_TYPE cx ty ==> WF_CX (cons (s,ty) cx)) /\

  (!n cx. WF_CX cx ==> WF_TYPE cx (v n)) /\
  (!ts cx s. WF_CX cx /\ MEM (s, HD ts) cx /\ EVERY (\t. WF_TYPE cx t) ts /\
             red SUC (HD ts) (HD (TL ts)) ==>
             WF_TYPE cx (app ts))
`
val _ = checkhyps ph_rules

(* UNCURRY with more than two arguments *)
val _ = new_constant ("Z", ``:num``)
val _ = new_constant ("ONE", ``:num``)
val _ = new_constant ("TWO", ``:num``)
val _ = print "*** Testing UNCURRY with more than two arguments\n"
val (u3_rules, u3_ind, u3_cases) = Hol_reln`
  u3 (Z,ONE,TWO) /\
  (!x y z. (\ ((x,y), z). u3 (x,y,z)) ((y,x),z) ==> u3 (x,y,z))
`
val _ = checkhyps u3_rules

(* single rule *)
val _ = print "*** Testing strong principle for singleton rule\n"
val _ = new_constant ("+", ``:num -> num -> num``)
val _ = set_fixity "+" (Infixl 500)
val (single_rules, single_ind, single_cases) = Hol_reln`
  (!x y. RTC single x y \/ (x = y + TWO) ==> single x y)
`;
val _ = checkhyps single_rules

val _ = print "*** Overloading case constant (pairs)\n"
val _ = overload_on ("foo", ``\p. case p of (x,y) => x /\ y``)
val _ = tpp "foo z"
val _ = set_trace "types" 1
val _ = trace ("types", 1) tpp  "case (p :'a # 'b) of (x,y) => x"

val _ = print "*** Overloading case constant (booleans)\n"
val _ = overload_on ("bar", ``\b. if b then T else F``)
val _ = tpp "bar T"
val _ = trace ("types", 1) tpp "if (b :bool) then (x :'a) else (y :'a)"

(* pairLib conversions etc *)
val _ = List.app convtest [
  ("PairRules.PBETA_CONV(1)", PairRules.PBETA_CONV,
   “(\ (a:'a,b:'b). f (a,b) (c:'c) : 'd) x”, “(f:'a # 'b -> 'c -> 'd) x c”),
  ("PairRules.PETA_CONV(1)", PairRules.PETA_CONV,
   “(\ (a:'a,b:'b). f (a,b) : 'c)”, “f : 'a # 'b -> 'c”)
]

local open pairLib in
val _ = print "*** new_specification with existential definition\n"
val th = metisLib.METIS_PROVE[]``?x y z. x ==> z /\ z ==> y``;
val _ = tprint "Testing 0 constants"
val nothing_def = new_specification("nothing_def",[],th);
val _ = OK()
val _ = tprint "Testing 1 constant"
val a_def = new_specification("a_def",["a"],th);
val _ = OK()
val _ = tprint "Testing 2 constants"
val pq_def = new_specification("pq_def",["p","q"],th);
val _ = OK()
val _ = tprint "Testing 3 constants"
val rst_def = new_specification("rst_def",["r","s","t"],th);
val _ = OK()
end

(* split_pair_case_tac *)
open pairLib
val _ = app (ignore o hide) ["aa", "bb", "xx", "pp", "qq"]
val _ = tprint "split_pair_case_tac (case in goal)"
val _ = let
  val g = ([] : term list, ``case xx of (aa,bb) => aa /\ bb``)
  fun check (sgs, vfn) =
      case sgs of
          [([a], g')] => aconv (#2 g) g' andalso
                         aconv a ``xx = (aa:bool,bb:bool)``
        | _ => false
in
  require (check_result check) split_pair_case_tac g
end;

val _ = tprint "split_pair_case_tac (case in assumptions)"
val _ = let
  val a = ``case xx of (aa,bb) => aa /\ bb``
  val g = ``pp /\ qq``
  fun check (sgs, vfn) =
      case sgs of
          [([a1, a2], g')] => aconv g' g andalso
                              aconv a1 ``xx = (aa:bool, bb:bool)`` andalso
                              aconv a2 a
        | _ => false
in
  require (check_result check) split_pair_case_tac ([a], ``pp /\ qq``)
end

val _ = Feedback.emit_MESG := false
val _ = Feedback.emit_WARNING := false
val _ = delete_const "v"

val _ = tprint "simp (srw_ss()) on one_CASE"
local
in
val _ = require_msg (check_result (aconv ``v:'a``)) term_to_string
                    (rhs o concl o SIMP_CONV (srw_ss()) [])
                    ``one_CASE () (v:'a)``
end

(* github issue #765; induction principle for pairs is wrong *)
val _ = hide "p"
val _ = tprint "Induction principle for pairs"
val res = Exn.capture (BasicProvers.Induct_on ‘p’) ([], “FST p ≠ SND p”)
val _ = case res of
            Exn.Res _ => OK()
          | Exn.Exn e => sdie ("Exception : " ^ General.exnMessage e)

(* removing thy-named fragments *)
local

in
val _ = convtest("srw_ss has x = () rewrite", SIMP_CONV (srw_ss()) [],
                 “x:unit”, “() : unit”)
val _ = diminish_srw_ss ["one"]
val _ = shouldfail {checkexn = fn UNCHANGED => true | _ => false,
                    printarg = K "after diminish\"one\", that no longer works",
                    printresult = thm_to_string,
                    testfn = SIMP_CONV (srw_ss()) []}
                   “x:unit”
end (* local *)

(* one_line_ify *)
val fsumdef = new_recursive_definition {
  name = "fsumdef",
  rec_axiom = sumTheory.sum_Axiom,
  def = “fsum f (INR x) = (T,INL T) /\ fsum f (INL y) = (F,INR (f y))”
};

fun good_oneline th =
    null (hyp th) andalso
    (let val cs = strip_conj (concl th)
     in
       length cs = 1 andalso is_eq (hd cs)
     end)

fun test msg th =
    (tprint ("one_line_ify on " ^ msg);
     require_msg (check_result good_oneline)
                 (trace("assumptions", 1) thm_to_string)
                 (DefnBase.one_line_ify NONE) th)
val _ = test "function over sum" fsumdef

val pairdef = new_definition("pairdef", “pairdef (f,x) g = f (g x)”)
val _ = test "function over pair" pairdef

val upairdef0 = new_definition("upairdef0", “upairdef (v:unit) (x,y) = x”)
val upairdef = upairdef0 |> SIMP_RULE bool_ss [oneTheory.one]
val _ = test "pair function with unit pat" upairdef

val onedef0 = new_definition ("one_def0",
                              “onedef (f : bool -> 'a) (v:unit) = f T”)
val onedef = onedef0 |> SIMP_RULE bool_ss [oneTheory.one]
val _ = test "function over unit" onedef

val spcross_def0 = new_recursive_definition{
  name = "spcross_def",
  rec_axiom = sumTheory.sum_Axiom,
  def = “spcross f (INL x) p = (x /\ FST p) /\
         spcross f (INR y) p = f y ”};
val spcross_def = CONV_RULE (LAND_CONV (SIMP_CONV bool_ss [FORALL_PROD, FST]))
                            spcross_def0

val _ = test "sum+pair, inconsistent patterns" spcross_def


val _ = app (ignore o hide) ["a", "q"]
val c1pairdef0 =
    new_definition("c1pairdef", “c1pair (p:'a#'b) q = (FST q /\ SND q)”)
val c1pairdef =
    c1pairdef0
      |> SIMP_RULE bool_ss [FORALL_PROD, FST, SND]
val _ = test "function over pairs (one pair ignored)" c1pairdef

val spvcross1_def0 = new_recursive_definition{
  name = "spvcross1_def",
  rec_axiom = sumTheory.sum_Axiom,
  def = “spvcross1 f (INL x) (p:'a # 'b) = x /\
         spvcross1 f (INR y) p = f y”};
val spvcross1_def =
    spvcross1_def0
      |> CONV_RULE (RAND_CONV (SIMP_CONV bool_ss [FORALL_PROD]))
val _ = test "sum+pair, pair pattern unused" spvcross1_def

val spvcross2_def0 = new_recursive_definition{
  name = "spvcross2_def",
  rec_axiom = sumTheory.sum_Axiom,
  def = “spvcross2 f (INL x) (p:'a # 'b) = f x p /\
         spvcross2 f (INR y) p = y f”};
val spvcross2_def =
    spvcross2_def0
      |> CONV_RULE (RAND_CONV (SIMP_CONV bool_ss [FORALL_PROD]))
val _ = test "sum+pair, pair components unused" spvcross2_def



val cpairdef = new_definition("cpairdef", “cpair (f,x) = T”)
val _ = test "constant function over pair" cpairdef

val multiv_def0 = new_definition ("multiv_def", “multiv f (p1:'a # 'b) (p2:'b # 'd) = f T”)
val multiv_def = multiv_def0 |> SIMP_RULE bool_ss [FORALL_PROD]
val _ = test "multiple vacuous patterns" multiv_def

val nestedv_def0 = new_recursive_definition{
  rec_axiom = sumTheory.sum_Axiom,
  name = "nestedv_def",
  def = “nestedv f a (INL (p:'a # bool)) = f p /\
         nestedv f a (INR (x:'a # bool # bool)) = f (a,F)”}
val nestedv_def = nestedv_def0
                    |> CONV_RULE (RAND_CONV (SIMP_CONV bool_ss [FORALL_PROD]))
val _ = test "nested vacuous pattern" nestedv_def

val already_good1_def = new_definition("already_good1_def",
  “already_good1 p q = (p,q)”);
val _ = test "already good, simple RHS" already_good1_def

val already_good2_def = new_definition("already_good2_def",
  “already_good2 p q = case (p,q) of (T,_) => T | (F, q) => q”);
val _ = test "already good, case on RHS" already_good2_def

val _ = tprint "TypeBase.case_pred_disj_of “:'b # 'c”"
fun eq_upto_renaming t1 t2 = can (match_term t1) t2 andalso
                             can (match_term t2) t1
val desired = “!P. P (pair_CASE p f) <=> ?q r. p = (q,r) /\ P (f q r)”
val hoelim = require_msg
               (check_result (eq_upto_renaming desired))
               term_to_string
               (concl o TypeBase.case_pred_disj_of) “:'b # 'c”

val _ = Process.exit Process.success
