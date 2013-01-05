(*=====================================================================  *)
(* FILE          : quantHeuristicsLibAbbrev.sml                          *)
(* DESCRIPTION   : Abbreviate subterms                                   *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : Oct 2012                                              *)
(* ===================================================================== *)


structure quantHeuristicsLibAbbrev :> quantHeuristicsLibAbbrev =
struct

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/src/quantHeuristics"])::
            !loadPath;

map load ["quantHeuristicsTheory"];
load "ConseqConv"
show_assums := true;
quietdec := true;
*)

open HolKernel Parse boolLib Drule
     quantHeuristicsLibBase

fun no_var_const_filter t =
  not ((is_var t) orelse (is_const t))

local
   fun find_tms (d:(term, int) Redblackmap.dict) tm =
   let
      val d = Redblackmap.update (d, tm, (fn vo => (getOpt (vo, 0)) + 1))
   in
      find_tms d (body tm)
      handle HOL_ERR _ =>
         case Lib.total dest_comb tm of
            SOME (r1, r2) => (find_tms (find_tms d r1) r2)
          | NONE => d
   end

   val empty_tm_dict:(term, int) Redblackmap.dict = Redblackmap.mkDict Term.compare

in
   (* Returns a list of all the subterms of t that satisfy P ordered by the number of appearences in t.
      Moreover, a function that allows to efficiently lookup how often a term apears in t is returned *)
   fun find_terms_count P t =
   let
      val d = find_tms empty_tm_dict t;
      fun d_fun t = getOpt(Redblackmap.peek (d, t), 0)

      val tL = Redblackmap.listItems d;
      val ftL = filter (fn (t, _) => P t) tL
      val stL = Lib.sort (fn (_, i) => fn (_, j:int) => (i > j)) ftL
      val ftL = map fst stL
   in
      (ftL, d_fun)
   end

end


(*
val t = ``P (FST (h y)) /\ !x. (Q (SND (g x)) /\ P (f (FST (g x))))``

val t = ``P (FST (h y)) /\ (Q (SND (g x)) /\ P (f (FST (g x))))``

val elim_abbrev_abort = false
fun elim_conv _ = NO_CONV
val intro_abbrev = true
val only_top = true
*)

type selection_fun = term -> (term -> int) -> term -> (term * string) list

fun select_funs_combine (sfL:selection_fun list) = (fn ctx => fn cf =>
   (let val sfL' = map (fn sf => sf ctx cf) sfL in
   (fn t =>
      flatten (map (fn sf => sf t handle HOL_ERR _ => []) sfL')) end)):selection_fun

fun INTRO_QUANT_ABBREVIATIONS_CONV_base elim_conv elim_abbrev_abort intro_abbrev only_top (select_funs:selection_fun list) t =
let
   val select_terms = let
      val (tL, t_count_fun) = (find_terms_count (K true) t);
      val sf = select_funs_combine select_funs t t_count_fun
      val sfs = flatten (map sf tL)
      val fsfs = filter (fn (tt, _) => no_var_const_filter tt) sfs

      fun my_insert ((tt, n), l) = if (exists (fn (tt', _) => tt' = tt) l) then l else (tt,n)::l
      val fsfs_unique = rev (foldl my_insert [] fsfs)
   in fsfs_unique end
   val fvL = ref (all_vars t);
(*
   val (st, ss) = hd select_terms
*)


   fun try_select (st, ss) t =
   let
      val new_v = variant (!fvL) (mk_var (ss, type_of st))
      val s = [st |-> new_v];
      val _ = fvL := new_v :: (!fvL);

      fun v_inst_filter v t i fvL = not (i = st)
      fun v_filter v t = v = new_v
      val v_qps = [inst_filter_qp [v_inst_filter], filter_qp [v_filter]]

(*
      val (_, t0) = dest_abs (rand (rand t))
val t0 = t
val t0 = qasm_t
val is_top = true
val t0 = snd (strip_forall t)
*)
      fun try_subst is_top t0 =
      let
         val t' = subst s t0
         val is_top' = (is_top andalso is_forall t0)
      in
         if (t0 = t') then (if (only_top andalso (not is_top')) then fail() else
                               (if is_top' then QUANT_CONV (try_subst true) t0 else
                                                (SUB_CONV (try_subst false) t0))) else
         let
           val abbrev_t = mk_forall (new_v, mk_imp(mk_eq (st, new_v), t'));
           val elim_thm = QCHANGED_CONV (elim_conv v_qps) abbrev_t handle HOL_ERR _ => REFL abbrev_t
           val _ = if (aconv t0 (rhs (concl elim_thm))) then fail() else ()
           val no_simp = (aconv abbrev_t (rhs (concl elim_thm)))
           val _ = if (elim_abbrev_abort andalso no_simp) then fail() else ()
           val elim_thm = if (no_simp andalso intro_abbrev andalso is_top) then
              let
                 val pre_thm = CONV_RULE (LHS_CONV SYM_CONV) (GSYM (ISPEC (mk_eq (new_v, st)) markerTheory.Abbrev_def))
              in QUANT_CONV (RATOR_CONV (RAND_CONV (K pre_thm))) abbrev_t end
              else elim_thm;

           val abbrev_thm = prove (mk_eq (t0, abbrev_t), Unwind.UNWIND_FORALL_TAC THEN REWRITE_TAC [])
         in
           TRANS abbrev_thm elim_thm
         end
      end
   in
     try_subst true t
   end;
in
  EVERY_CONV (map (fn arg => TRY_CONV (try_select arg)) select_terms) t
end;

fun GEN_SIMPLE_QUANT_ABBREV_CONV intro_abbrev only_top select_funs =
   (INTRO_QUANT_ABBREVIATIONS_CONV_base (K NO_CONV) false intro_abbrev only_top select_funs)

fun SIMPLE_QUANT_ABBREV_CONV select_funs =
    GEN_SIMPLE_QUANT_ABBREV_CONV false false select_funs

fun SIMPLE_QUANT_ABBREV_TAC (select_funs:selection_fun list) =
  ConseqConv.DISCH_ASM_CONV_TAC (GEN_SIMPLE_QUANT_ABBREV_CONV true true select_funs)

fun quant_elim_conv qpL qps = QCHANGED_CONV (FAST_QUANT_INSTANTIATE_CONV (qps@qpL))

fun QUANT_ABBREV_CONV select_funs qpL = (INTRO_QUANT_ABBREVIATIONS_CONV_base
 (quant_elim_conv qpL) false false false select_funs)

fun QUANT_ABBREV_TAC (select_funs:selection_fun list) qpL =
  ConseqConv.DISCH_ASM_CONV_TAC (QUANT_ABBREV_CONV select_funs qpL)


(* Some select functions *)

(* Searching for constants "c" and abbreviation argument number "i"
   with name "name". i = 0 means the whole term, i = 1 the first argument ... *)
fun select_fun_constant c i (name:string) = (fn ctx => fn cf => (fn t =>
  let
    val (c', aL) = strip_comb t;
    val _ = if same_const c c' then () else fail();
  in
    [(if i = 0 then t else el i aL, name)]
  end handle HOL_ERR _ => [])): selection_fun

(* This allows common selection funs *)
val FST_select_fun = select_fun_constant pairSyntax.fst_tm 1 "p"
val SND_select_fun = select_fun_constant pairSyntax.snd_tm 1 "p"
val IS_SOME_select_fun = select_fun_constant optionSyntax.is_some_tm 1 "x"
val THE_select_fun = select_fun_constant optionSyntax.the_tm 1 "p"

(* For pairs, the pattern "(\(x,y). P) X" is useful as well *)
fun select_fun_pabs name = (fn ctx => fn cf => (fn t =>
  let
    val (p, a) = dest_comb t;
    val _ = if pairSyntax.is_pabs p andalso not (is_abs p) then () else fail();
  in
    [(p, name)]
  end handle HOL_ERR _ => [])): selection_fun;

val PAIR_select_fun = select_funs_combine [select_fun_pabs "p", FST_select_fun, SND_select_fun];


(* In general, we might want pattern matching. The following function tries matching
   and abbreviates any matched variable in the pattern that does not start with _.
   The general version allows to specify that it needs to occur at least n times as well. *)
(*
val q = `f (_, xx)`
val ctx = ``Q (f (2, g(z))) /\ Y x``
val t = ``f (2, g(z))``
*)
fun select_fun_pattern_occ n q = (fn ctx => fn cf =>
let
  val fvs = all_vars ctx
  val pat = Parse.parse_in_context fvs q
  val fvs_set = HOLset.fromList (Term.compare) fvs
in
  fn t => let
     val ((ts, _), _) = raw_match [] fvs_set pat t ([], [])
     val sb' = filter (fn {redex=l,residue=r} => not (String.isPrefix "_" (fst (dest_var l))) andalso
                     cf r >= n) ts
  in (map (fn {redex=l,residue=r} => (r, fst (dest_var l))) sb') end
end):selection_fun

fun select_fun_pattern q = select_fun_pattern_occ 0 q

(* you might want to abbreviate the whole match however, as well *)

fun select_fun_match_occ n q name_fun = (fn ctx => fn cf =>
let
  val fvs = all_vars ctx
  val pat = Parse.parse_in_context fvs q
  val fvs_set = HOLset.fromList (Term.compare) fvs
in
  fn t => let
     val _ = if (cf t) >= n then () else fail();
     val _ = raw_match [] fvs_set pat t ([], [])
  in [(t, name_fun t)] end
end):selection_fun

fun select_fun_match q name = select_fun_match_occ 0 q (K name)


(* Testing it

open quantHeuristicsLibAbbrev
open quantHeuristicsLib

val t = ``P (FST (g x)) /\ (P (FST (g x))) /\ P (FST (f x)) /\ !y. Q p /\ P (SND (g y))``


SIMPLE_QUANT_ABBREV_CONV [FST_select_fun]  t
SIMPLE_QUANT_ABBREV_CONV [SND_select_fun]  t

QUANT_ABBREV_CONV [FST_select_fun] [std_qp] t
QUANT_ABBREV_CONV [SND_select_fun] [std_qp] t
QUANT_ABBREV_CONV [FST_select_fun, SND_select_fun] [std_qp] t


set_goal ([], t)
e (SIMPLE_QUANT_ABBREV_TAC [SND_select_fun, FST_select_fun])
e (QUANT_ABBREV_TAC [SND_select_fun, FST_select_fun] [std_qp])


val select_funs = [FST_select_fun, SND_select_fun]

set_goal ([], t)
e (QUANT_ABBREV_TAC [FST_select_fun, SND_select_fun] [std_qp])
e (SIMPLE_QUANT_ABBREV_TAC [FST_select_fun, SND_select_fun])

Q.UNABBREV_TAC `p''`

val t2 = ``Q x ==> (IS_SOME (g x)) ==> (IS_SOME (f x)) ==> P (THE (g x), THE (f x))``

REPEAT STRIP_TAC
QUANT_ABBREV_TAC [select_fun_pattern `IS_SOME dummy`] [std_qp]

QUANT_ABBREV_TAC [select_fun_match `f x` "gx"] [std_qp]

QUANT_ABBREV_CONV [select_fun_match `g x` "gx"] [std_qp] t2
SIMPLE_QUANT_ABBREV_TAC [THE_select_fun]

*)

end
