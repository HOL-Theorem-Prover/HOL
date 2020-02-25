(*=====================================================================  *)
(* FILE          : quantHeuristicsLibSimple.sml                          *)
(* DESCRIPTION   : simple and fast way to find guesses, this is closer   *)
(*                 to unwind than to the full search of quantifier       *)
(*                 heuristics                                            *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : February 2017                                         *)
(* ===================================================================== *)


structure quantHeuristicsLibSimple :> quantHeuristicsLibSimple =
struct

(*
loadPath :=
            (concat [Globals.HOLDIR, "/src/quantHeuristics"])::
            !loadPath;

map load ["quantHeuristicsTheory"];
*)

open HolKernel Parse boolLib Drule
     quantHeuristicsTheory pairTools


val std_ss = numLib.std_ss


(**************************************)
(* Basic types                        *)
(**************************************)

datatype simple_guess_type = sgty_forall | sgty_exists

type simple_guess_search_fun =
  term set ->          (* vars to avoid *)
  simple_guess_type -> (* which type of guess should be searched *)
  term ->              (* var to search a guess for *)
  term ->              (* term to search in *)
  thm;                 (* found thm *)

type simple_guess_search_fun_with_callback =
  simple_guess_search_fun -> simple_guess_search_fun


(***************************************)
(* Auxiliary function                  *)
(***************************************)

val ERR = mk_HOL_ERR "quantHeuristicsLibSimple"

fun not_uses_avoid_vars avoid tm = let
  val s1 = FVL [tm] empty_tmset
  val s2 = HOLset.intersection (s1, avoid)
in
  HOLset.isEmpty s2
end

fun inst_vi v i thm = let
  val ty = type_of v
  val thm' = INST_TYPE [alpha |-> ty] thm
in
  SPEC i (SPEC v thm')
end

fun dest_simple_guess_thm thm = let
  val tt = concl thm
  val (tt, P) = dest_comb tt
  val (tt, i) = dest_comb tt
  val (tt, v) = dest_comb tt
in
  (tt, v, i, P)
end

fun inst_guess gi es thm = let
  val (_, v, i, _) = dest_simple_guess_thm gi
  val thm' = inst_vi v i thm
  val thm'' = SPECL es thm'
in
  MP thm'' gi
end

val select_some      = prim_mk_const {Name = "some", Thy = "option"}
val dest_select_some = dest_binder select_some (ERR "dest_select_some" "not a \"some x. _\"")

(***************************************)
(* search functions                    *)
(***************************************)

fun sgsfwc_eq_var sys avoid sgty_forall v tm = failwith "sgsfwc_eq_var: only works for exists"
  | sgsfwc_eq_var sys avoid sgty_exists v tm = (
      if (aconv v tm) then
        SPEC v (SIMPLE_GUESS_EXISTS_EQ_T)
      else failwith "sgsfwc_eq_var: not eq v"
    )

fun sgsfwc_eq (sys : simple_guess_search_fun) avoid sgty_forall v tm =
    failwith "sgsfwc_eq: only works for exists"
  | sgsfwc_eq sys avoid sgty_exists v tm = let
      val (tm1, tm2) = dest_eq tm in
        if (aconv v tm1) andalso not_uses_avoid_vars avoid tm2 then
          inst_vi v tm2 SIMPLE_GUESS_EXISTS_EQ_1
        else if (aconv v tm2) andalso not_uses_avoid_vars avoid tm1 then
          inst_vi v tm1 SIMPLE_GUESS_EXISTS_EQ_2
        else failwith "sgty_eq"
      end;

fun sgsfwc_neg (sys : simple_guess_search_fun) avoid sgty v tm =
    let
      val tm' = dest_neg tm
      val (sgty', thm) = case sgty of
          sgty_exists => (sgty_forall, SIMPLE_GUESS_EXISTS_NEG)
        | sgty_forall => (sgty_exists, SIMPLE_GUESS_FORALL_NEG)
      val g = sys avoid sgty' v tm'
    in inst_guess g [tm'] thm end

fun sgsfwc_and (sys : simple_guess_search_fun) avoid sgty_forall v tm =
    failwith "sgsfwc_and: only works for exists"
  | sgsfwc_and sys avoid sgty_exists v tm = let
      val (tm1, tm2) = dest_conj tm in
        let
          val g1 = sys avoid sgty_exists v tm1
        in inst_guess g1 [tm1, tm2] SIMPLE_GUESS_EXISTS_AND_1 end
        handle HOL_ERR _ =>
        let
          val g2 = sys avoid sgty_exists v tm2
        in inst_guess g2 [tm1, tm2] SIMPLE_GUESS_EXISTS_AND_2 end
        handle HOL_ERR _ => failwith "sgsfwc_and"
      end;

fun sgsfwc_or (sys : simple_guess_search_fun) avoid sgty_exists v tm =
    failwith "sgsfwc_or: only works for forall"
  | sgsfwc_or sys avoid sgty_forall v tm = let
      val (tm1, tm2) = dest_disj tm in
        let
          val g1 = sys avoid sgty_forall v tm1
        in inst_guess g1 [tm1, tm2] SIMPLE_GUESS_FORALL_OR_1 end
        handle HOL_ERR _ =>
        let
          val g2 = sys avoid sgty_forall v tm2
        in inst_guess g2 [tm1, tm2] SIMPLE_GUESS_FORALL_OR_2 end
        handle HOL_ERR _ => failwith "sgsfwc_or"
      end;

fun sgsfwc_imp (sys : simple_guess_search_fun) avoid sgty_exists v tm =
    failwith "sgsfwc_imp: only works for forall"
  | sgsfwc_imp sys avoid sgty_forall v tm = let
      val (tm1, tm2) = dest_imp_only tm in
        let
          val g1 = sys avoid sgty_exists v tm1
        in inst_guess g1 [tm1, tm2] SIMPLE_GUESS_FORALL_IMP_1 end
        handle HOL_ERR _ =>
        let
          val g2 = sys avoid sgty_forall v tm2
        in inst_guess g2 [tm1, tm2] SIMPLE_GUESS_FORALL_IMP_2 end
        handle HOL_ERR _ => failwith "sgsfwc_or"
      end;

fun sgsfwc_forall (sys : simple_guess_search_fun) avoid sgty v tm =
    let
      val (v', tm') = dest_forall tm
      val avoid' = HOLset.add (avoid, v')
      val g0 = sys avoid' sgty v tm'
      val g1 = GEN v' g0
      val thm0 = case sgty of
          sgty_exists => SIMPLE_GUESS_EXISTS_FORALL
        | sgty_forall => SIMPLE_GUESS_FORALL_FORALL
      val (_, v, i, _) = dest_simple_guess_thm g0
      val thm' = HO_MATCH_MP thm0 g1
    in thm' end;

fun sgsfwc_exists (sys : simple_guess_search_fun) avoid sgty v tm =
    let
      val (v', tm') = dest_exists tm
      val avoid' = HOLset.add (avoid, v')
      val g0 = sys avoid' sgty v tm'
      val g1 = GEN v' g0
      val thm0 = case sgty of
          sgty_exists => SIMPLE_GUESS_EXISTS_EXISTS
        | sgty_forall => SIMPLE_GUESS_FORALL_EXISTS
      val (_, v, i, _) = dest_simple_guess_thm g0
      val thm' = HO_MATCH_MP thm0 g1
    in thm' end;


fun sgsfwc_eq_fun_aux (sys : simple_guess_search_fun) avoid v (tm1, tm2) (f, cond, rewr) =
  if (not (cond tm1 orelse cond tm2)) then failwith "sgsfwc_fun_aux: cond failed" else
  let
    val tm1' = mk_icomb (f, tm1)
    val tm1'_eq = REWR_CONV rewr tm1' handle HOL_ERR _ => REFL tm1'
    val tm2' = mk_icomb (f, tm2)
    val tm2'_eq = REWR_CONV rewr tm2' handle HOL_ERR _ => REFL tm2'

    val tm' = mk_eq (tm1', tm2')
    val tm'_eq = (LHS_CONV (K tm1'_eq) THENC RHS_CONV (K tm2'_eq)) tm'
    val tm'' = rhs (concl tm'_eq)

    val g = sys avoid sgty_exists v tm''
    val g' = CONV_RULE (RAND_CONV (K (GSYM tm'_eq))) g
  in
    MATCH_MP SIMPLE_GUESS_EXISTS_EQ_FUN g'
  end

fun sgsfwc_eq_fun l (sys : simple_guess_search_fun) avoid sgty_forall v tm =
    failwith "sgsfwc_eq_fun: only works for exists"
  | sgsfwc_eq_fun l (sys : simple_guess_search_fun) avoid sgty_exists v tm =
    let
      val (tm1, tm2) = dest_eq tm
    in
      tryfind (sgsfwc_eq_fun_aux sys avoid v (tm1, tm2)) l
    end;

val default_eq_funs = [
  (``FST``, pairSyntax.is_pair, pairTheory.FST),
  (``SND``, pairSyntax.is_pair, pairTheory.SND),
  (``HD``, listSyntax.is_cons, listTheory.HD),
  (``TL``, listSyntax.is_cons, listTheory.TL),
  (``THE``, optionSyntax.is_some, optionTheory.THE_DEF),
  (``OUTL``, sumSyntax.is_inl, sumTheory.OUTL),
  (``OUTR``, sumSyntax.is_inr, sumTheory.OUTR)]


fun combine_sgsfwcs (wc_l : simple_guess_search_fun_with_callback list)
  avoid ty v tm =
  Lib.tryfind (fn wc => wc (combine_sgsfwcs wc_l) avoid ty v tm) wc_l

val default_sgsfwcs : simple_guess_search_fun_with_callback list = [
  sgsfwc_and,
  sgsfwc_or,
  sgsfwc_imp,
  sgsfwc_neg,
  sgsfwc_eq,
  sgsfwc_eq_var,
  sgsfwc_forall,
  sgsfwc_exists,
  sgsfwc_eq_fun default_eq_funs];

val sys = combine_sgsfwcs default_sgsfwcs

(***************************************)
(* top level functions                 *)
(***************************************)

fun MOVE_TO_LAST_EXISTS_CONV c t =
  ((SWAP_EXISTS_CONV THENC QUANT_CONV
    (MOVE_TO_LAST_EXISTS_CONV c)) ORELSEC c) t

fun SIMPLE_EXISTS_INSTANTIATE_CONV_GEN wcl tm = let
  val (vl, b_tm) = strip_exists tm
  val (v, vl') = case vl of [] => failwith "SIMPLE_EXISTS_INSTANTIATE_CONV: no exists"
                          | (v :: vl') => (v, vl')
  val avoid = HOLset.singleton Term.compare v
  val guess = combine_sgsfwcs wcl avoid sgty_exists v b_tm

  val thm0 = HO_MATCH_MP SIMPLE_GUESS_EXISTS_THM (GEN v guess)
  val thm1 = MOVE_TO_LAST_EXISTS_CONV (K thm0) tm
in
  thm1
end

val SIMPLE_EXISTS_INSTANTIATE_CONV = SIMPLE_EXISTS_INSTANTIATE_CONV_GEN default_sgsfwcs


fun MOVE_TO_LAST_FORALL_CONV c t =
  ((SWAP_FORALL_CONV THENC QUANT_CONV
    (MOVE_TO_LAST_FORALL_CONV c)) ORELSEC c) t


fun SIMPLE_FORALL_INSTANTIATE_CONV_GEN wcl tm = let
  val (vl, b_tm) = strip_forall tm
  val (v, vl') = case vl of [] => failwith "SIMPLE_FORALL_INSTANTIATE_CONV: no forall"
                          | (v :: vl') => (v, vl')
  val avoid = HOLset.singleton Term.compare v
  val guess = combine_sgsfwcs wcl avoid sgty_forall v b_tm

  val thm0 = HO_MATCH_MP SIMPLE_GUESS_FORALL_THM (GEN v guess)
  val thm1 = MOVE_TO_LAST_FORALL_CONV (K thm0) tm
in
  thm1
end;

val SIMPLE_FORALL_INSTANTIATE_CONV = SIMPLE_FORALL_INSTANTIATE_CONV_GEN default_sgsfwcs;


fun SIMPLE_UEXISTS_INSTANTIATE_CONV_GEN wcl tm = let
  val (v, b_tm) = dest_exists1 tm
  val avoid = HOLset.singleton Term.compare v
  val guess = combine_sgsfwcs wcl avoid sgty_exists v b_tm

  val thm0 = HO_MATCH_MP SIMPLE_GUESS_UEXISTS_THM (GEN v guess)
in
  thm0
end;

val SIMPLE_UEXISTS_INSTANTIATE_CONV = SIMPLE_UEXISTS_INSTANTIATE_CONV_GEN default_sgsfwcs;


fun SIMPLE_SOME_INSTANTIATE_CONV_GEN wcl tm = let
  val (v, b_tm) = dest_select_some tm
  val avoid = HOLset.singleton Term.compare v
  val guess = combine_sgsfwcs wcl avoid sgty_exists v b_tm

  val thm0 = HO_MATCH_MP SIMPLE_GUESS_SOME_THM (GEN v guess)
in
  thm0
end

val SIMPLE_SOME_INSTANTIATE_CONV = SIMPLE_SOME_INSTANTIATE_CONV_GEN default_sgsfwcs;


fun SIMPLE_SELECT_INSTANTIATE_CONV_GEN wcl tm = let
  val (v, b_tm) = dest_select tm
  val avoid = HOLset.singleton Term.compare v
  val guess = combine_sgsfwcs wcl avoid sgty_exists v b_tm

  val thm0 = HO_MATCH_MP SIMPLE_GUESS_SELECT_THM (GEN v guess)
in
  thm0
end

val SIMPLE_SELECT_INSTANTIATE_CONV = SIMPLE_SELECT_INSTANTIATE_CONV_GEN default_sgsfwcs;


fun SIMPLE_QUANT_INSTANTIATE_CONV_GEN wcl = FIRST_CONV [
  SIMPLE_EXISTS_INSTANTIATE_CONV_GEN wcl,
  SIMPLE_FORALL_INSTANTIATE_CONV_GEN wcl,
  SIMPLE_UEXISTS_INSTANTIATE_CONV_GEN wcl,
  SIMPLE_SOME_INSTANTIATE_CONV_GEN wcl,
  SIMPLE_SELECT_INSTANTIATE_CONV_GEN wcl]

val SIMPLE_QUANT_INSTANTIATE_CONV =
  SIMPLE_QUANT_INSTANTIATE_CONV_GEN default_sgsfwcs

val SIMPLE_QUANT_INSTANTIATE_TAC =
  CONV_TAC (TOP_DEPTH_CONV SIMPLE_QUANT_INSTANTIATE_CONV)

fun SIMPLE_QUANT_INST_GEN_ss wcl = simpLib.SSFRAG
  {name=SOME "SIMPLE_QUANT_INSTANTIATE_GEN",
   convs=[{name="SIMPLE_EXISTS_INSTANTIATE_CONV_GEN",
           trace=1,
           key=SOME ([],``?x:'a. P``),
           conv=K (K (SIMPLE_EXISTS_INSTANTIATE_CONV_GEN wcl))},
          {name="SIMPLE_FORALL_INSTANTIATE_CONV_GEN",
           trace=1,
           key=SOME ([],``!x:'a. P``),
           conv=K (K (SIMPLE_FORALL_INSTANTIATE_CONV_GEN wcl))},
          {name="SIMPLE_UEXISTS_INSTANTIATE_CONV_GEN",
           trace=1,
           key=SOME ([],``?!x:'a. P``),
           conv=K (K (SIMPLE_UEXISTS_INSTANTIATE_CONV_GEN wcl))},
          {name="SIMPLE_SOME_INSTANTIATE_CONV_GEN",
           trace=1,
           key=SOME ([],``some (x:'a). P``),
           conv=K (K (SIMPLE_SOME_INSTANTIATE_CONV_GEN wcl))},
          {name="SIMPLE_SELECT_INSTANTIATE_CONV_GEN",
           trace=1,
           key=SOME ([],``@x:'a. P``),
           conv=K (K (SIMPLE_SELECT_INSTANTIATE_CONV_GEN wcl))}],
   rewrs=map (fn (s, th) => (SOME {Thy = "", Name = s}, th)) [
     ("HD_TL_EQ_THMS", HD_TL_EQ_THMS),
     ("SOME_THE_EQ", SOME_THE_EQ),
     ("FST_PAIR_EQ", FST_PAIR_EQ),
     ("SND_PAIR_EQ", SND_PAIR_EQ),
     ("SOME_THE_EQ_SYM", SOME_THE_EQ_SYM),
     ("FST_PAIR_EQ_SYM", FST_PAIR_EQ_SYM),
     ("SND_PAIR_EQ_SYM", SND_PAIR_EQ_SYM)
   ],filter=NONE,ac=[],dprocs=[],congs=[]};

val SIMPLE_QUANT_INST_ss = SIMPLE_QUANT_INST_GEN_ss default_sgsfwcs;

end
