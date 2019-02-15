(* ===================================================================== *)
(* FILE          : numLib.sml  (Formerly num_lib.sml, num.sml)           *)
(* DESCRIPTION   : Proof support for :num. Translated from hol88.        *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge               *)
(* DATE          : 88.04.04                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* UPDATE        : October'94 bugfix to num_EQ_CONV (KLS;bugfix from tfm)*)
(* UPDATE        : January'99 fix to use "Norrish" numerals (MN)         *)
(* UPDATE        : August'99 to incorporate num_CONV and INDUCT_TAC      *)
(* UPDATE        : Nov'99 to incorporate main entrypoints from           *)
(*                 reduceLib and arithLib. Also, ADD_CONV and            *)
(*                 num_EQ_CONV are banished: use the stuff in reduceLib  *)
(*                 instead.                                              *)
(* ===================================================================== *)


structure numLib :> numLib =
struct

local open numeralTheory in end;

open HolKernel boolLib Num_conv Parse numSyntax;

val ERR = mk_HOL_ERR "numLib";

(* Fix the grammar used by this file *)
val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars arithmeticTheory.arithmetic_grammars

val N = numSyntax.num;

(* --------------------------------------------------------------------- *)
(* EXISTS_LEAST_CONV: applies the well-ordering property to non-empty    *)
(* sets of numbers specified by predicates.                              *)
(*                                                                       *)
(* A call to EXISTS_LEAST_CONV `?n:num. P[n]` returns:                   *)
(*                                                                       *)
(*   |- (?n. P[n]) = ?n. P[n] /\ !n'. (n' < n) ==> ~P[n']                *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

local val wop = arithmeticTheory.WOP
      val wth = CONV_RULE (ONCE_DEPTH_CONV ETA_CONV) wop
      val check = assert (fn tm => type_of tm = N)
      val acnv = RAND_CONV o ABS_CONV
in
fun EXISTS_LEAST_CONV tm =
   let val (Bvar,P) = dest_exists tm
       val n = check Bvar
       val thm1 = UNDISCH (SPEC (rand tm) wth)
       val thm2 = CONV_RULE (GEN_ALPHA_CONV n) thm1
       val (c1,c2) = dest_comb (snd(dest_exists(concl thm2)))
       val bth1 = RAND_CONV BETA_CONV c1
       val bth2 = acnv (RAND_CONV (RAND_CONV BETA_CONV)) c2
       val n' = variant (n :: free_vars tm) n
       val abth2 = CONV_RULE (RAND_CONV (GEN_ALPHA_CONV n')) bth2
       val thm3 = EXISTS_EQ n (MK_COMB(bth1,abth2))
       val imp1 = DISCH tm (EQ_MP thm3 thm2)
       val eltm = rand(concl thm3)
       val thm4 = CONJUNCT1 (ASSUME (snd(dest_exists eltm)))
       val thm5 = CHOOSE (n,ASSUME eltm) (EXISTS (tm,n) thm4)
   in
     IMP_ANTISYM_RULE imp1 (DISCH eltm thm5)
   end
   handle HOL_ERR _ => raise ERR "EXISTS_LEAST_CONV" ""
end;

(*---------------------------------------------------------------------------*)
(* EXISTS_GREATEST_CONV - Proves existence of greatest element satisfying P. *)
(*                                                                           *)
(* EXISTS_GREATEST_CONV `(?x. P[x]) /\ (?y. !z. z > y ==> ~(P[z]))` =        *)
(*    |- (?x. P[x]) /\ (?y. !z. z > y ==> ~(P[z])) =                         *)
(*        ?x. P[x] /\ !z. z > x ==> ~(P[z])                                  *)
(*                                                                           *)
(* If the variables x and z are the same, the `z` instance will be primed.   *)
(* [JRH 91.07.17]                                                            *)
(*---------------------------------------------------------------------------*)

local val EXISTS_GREATEST = arithmeticTheory.EXISTS_GREATEST
      val t = RATOR_CONV
      and n = RAND_CONV
      and b = ABS_CONV
      val red1 = t o n o t o n o n o b
      and red2 = t o n o n o n o b o n o b o n o n
      and red3 = n o n o b o t o n
      and red4 = n o n o b o n o n o b o n o n
in
fun EXISTS_GREATEST_CONV tm =
   let val (lc,rc) = dest_conj tm
       val pred = rand lc
       val (xv,xb) = dest_exists lc
       val (yv,yb) = dest_exists rc
       val zv = fst (dest_forall yb)
       val prealpha = CONV_RULE
         (red1 BETA_CONV THENC red2 BETA_CONV THENC
          red3 BETA_CONV THENC red4 BETA_CONV) (SPEC pred EXISTS_GREATEST)
       val rqd = mk_eq (tm, mk_exists(xv,mk_conj(xb,subst[yv |-> xv] yb)))
   in
      Lib.S (Lib.C EQ_MP) (Lib.C ALPHA rqd o concl) prealpha
   end
   handle HOL_ERR _ => raise ERR "EXISTS_GREATEST_CONV" ""
end;


local fun SEC_ERR m = ERR "SUC_ELIM_CONV" m
      fun assert f x = f x orelse raise SEC_ERR "assertion failed"
in
fun SUC_ELIM_CONV tm =
   let val (v,bod) = dest_forall tm
       val _ = assert (fn x => type_of x = N) v
       val (sn,n) = (genvar N, genvar N)
       val suck_suc = subst [numSyntax.mk_suc v |-> sn] bod
       val suck_n = subst [v |-> n] suck_suc
       val _ = assert (fn x => not (aconv x tm)) suck_n
       val th1 = ISPEC (list_mk_abs ([sn,n],suck_n))
                     arithmeticTheory.SUC_ELIM_THM
       val BETA2_CONV = (RATOR_CONV BETA_CONV) THENC BETA_CONV
       val th2 = CONV_RULE (LHS_CONV (QUANT_CONV BETA2_CONV)) th1
       val th3 = CONV_RULE (RHS_CONV (QUANT_CONV
                    (FORK_CONV (ALL_CONV, BETA2_CONV)))) th2
   in th3
   end
end;

val num_CONV = Num_conv.num_CONV;

(*---------------------------------------------------------------------------
     Forward rule for induction
 ---------------------------------------------------------------------------*)

local val v1 = genvar Type.bool
      and v2 = genvar Type.bool
in
fun INDUCT (base,step) =
   let val (Bvar,Body) = dest_forall(concl step)
       val (ant,_) = dest_imp Body
       val P  = mk_abs(Bvar, ant)
       val P0 = mk_comb(P, zero_tm)
       val Pv = mk_comb(P,Bvar)
       val PSUC = mk_comb(P, mk_suc Bvar)
       val base' = EQ_MP (SYM(BETA_CONV P0)) base
       and step'  = SPEC Bvar step
       and hypth  = SYM(RIGHT_BETA(REFL Pv))
       and concth = SYM(RIGHT_BETA(REFL PSUC))
       and IND    = SPEC P numTheory.INDUCTION
       val template = mk_eq(concl step', mk_imp(v1, v2))
       val th1 = SUBST[v1 |-> hypth, v2|->concth] template (REFL (concl step'))
       val th2 = GEN Bvar (EQ_MP th1 step')
       val th3 = SPEC Bvar (MP IND (CONJ base' th2))
   in
     GEN Bvar (EQ_MP (BETA_CONV(concl th3)) th3)
   end
   handle HOL_ERR _ => raise ERR "INDUCT" ""
end;

(* --------------------------------------------------------------------- *)
(*             [A] !n.t[n]                                               *)
(*  ================================                                     *)
(*   [A] t[0]  ,  [A,t[n]] t[SUC x]                                      *)
(* --------------------------------------------------------------------- *)

fun INDUCT_TAC g =
  INDUCT_THEN numTheory.INDUCTION ASSUME_TAC g
  handle HOL_ERR _ => raise ERR "INDUCT_TAC" "";


fun completeInduct_on qtm g =
 let open BasicProvers
     val st = find_subterm qtm g
     val ind_tac = Prim_rec.INDUCT_THEN
                     arithmeticTheory.COMPLETE_INDUCTION ASSUME_TAC
 in
    primInduct st ind_tac g
 end
 handle e => raise wrap_exn "numLib" "completeInduct_on" e


(*---------------------------------------------------------------------------
    Invoked e.g. measureInduct_on `LENGTH L` or
                 measureInduct_on `(\(x,w). x+w) (M,N)`
 ---------------------------------------------------------------------------*)

local open relationTheory prim_recTheory
      val mvar = mk_var("m", alpha --> numSyntax.num)
      val measure_tm = prim_mk_const{Name="measure",Thy="prim_rec"}
      val measure_m = mk_comb(measure_tm,mvar)
      val ind_thm0 = GEN mvar
          (BETA_RULE
             (REWRITE_RULE[WF_measure,measure_def,inv_image_def]
                 (MATCH_MP (SPEC measure_m WF_INDUCTION_THM)
                         (SPEC_ALL WF_measure))))
in
fun measureInduct_on q (g as (asl,w)) =
 let val FVs = free_varsl (w::asl)
     val tm = parse_in_context FVs q
     val (meas, arg) = dest_comb tm
     val (d,r) = dom_rng (type_of meas)  (* r should be num *)
     val st = BasicProvers.prim_find_subterm FVs arg g
     val st_type = type_of (BasicProvers.dest_tmkind st)
     val meas' = inst (match_type d st_type) meas
     val ind_thm1 = INST_TYPE [Type.alpha |-> st_type] ind_thm0
     val ind_thm2 = pairLib.GEN_BETA_RULE (SPEC meas' ind_thm1)
     val ind_tac = Prim_rec.INDUCT_THEN ind_thm2 ASSUME_TAC
 in
    BasicProvers.primInduct st ind_tac g
 end
 handle e => raise wrap_exn "numLib" "measureInduct_on" e
end

val REDUCE_CONV = reduceLib.REDUCE_CONV
val REDUCE_RULE = reduceLib.REDUCE_RULE
val REDUCE_TAC  = reduceLib.REDUCE_TAC

val ARITH_CONV  = Arith.ARITH_CONV
val ARITH_PROVE = Drule.EQT_ELIM o ARITH_CONV
val ARITH_TAC   = CONV_TAC ARITH_CONV;


(*---------------------------------------------------------------------------*)
(* If "c" is a number constant,                                              *)
(*                                                                           *)
(*  BOUNDED_FORALL_CONV cnv ``!n. n < c ==> P n``                            *)
(*                                                                           *)
(* generates "P (c-1) /\ !n. n < (c-1) ==> P n" and applies cnv to the first *)
(* conjunct "P (c-1)". With NTAC or REPEATC, this can be used to prove       *)
(* bounded quantifications.                                                  *)
(*---------------------------------------------------------------------------*)

fun BOUNDED_FORALL_CONV cnv M =
 let open reduceLib arithmeticTheory
     val c = snd(dest_less(fst(dest_imp(snd(dest_forall M)))))
     val thm = MP (SPEC c BOUNDED_FORALL_THM)
                  (EQT_ELIM(REDUCE_CONV (mk_less(zero_tm,c))))
 in
   (HO_REWR_CONV thm THENC LAND_CONV cnv THENC REDUCE_CONV) M
 end
 handle e => raise wrap_exn "numLib" "BOUNDED_FORALL_CONV" e;


(*---------------------------------------------------------------------------*)
(* If "c" is a number constant,                                              *)
(*                                                                           *)
(*    BOUNDED_EXISTS_CONV cnv `?n. n < c /\ P n`                             *)
(*                                                                           *)
(* generates "P (c-1) \/ ?n. n < (c-1) /\ P n"  and applies cnv to the first *)
(* conjunct "P (c-1)". With NTAC or REPEATC, this can be used to prove       *)
(* bounded quantifications.                                                  *)
(*---------------------------------------------------------------------------*)

fun BOUNDED_EXISTS_CONV cnv M =
 let open reduceLib arithmeticTheory
     val c = snd(dest_less(fst(dest_conj(snd(dest_exists M)))))
     val thm = MP (SPEC c BOUNDED_EXISTS_THM)
                  (EQT_ELIM(REDUCE_CONV (mk_less(zero_tm,c))))
 in
   (HO_REWR_CONV thm THENC LAND_CONV cnv THENC REDUCE_CONV) M
 end
 handle e => raise wrap_exn "numLib" "BOUNDED_EXISTS_CONV" e;

(* ----------------------------------------------------------------------
    LEAST_ELIM_TAC : tactic

    Turns

       A ?- Q ($LEAST P)

    (where P is free) into

       A ?- (?n. P n) /\ (!n. (!m. m < n ==> ~P m) /\ P n ==> Q n)

    Picks an arbitrary LEAST-subterm if there are multiple such.
   ---------------------------------------------------------------------- *)

val LEAST_ELIM_TAC = DEEP_INTRO_TAC whileTheory.LEAST_ELIM

(*---------------------------------------------------------------------------
    Simplification set for numbers (and booleans).
 ---------------------------------------------------------------------------*)

local open simpLib infix ++
in
val std_ss =
     (boolSimps.bool_ss ++ pairSimps.PAIR_ss ++ optionSimps.OPTION_ss ++
      numSimps.REDUCE_ss ++ sumSimps.SUM_ss ++ combinSimps.COMBIN_ss ++
      numSimps.ARITH_RWTS_ss)

val arith_ss = std_ss ++ numSimps.ARITH_DP_ss
end;

(*---------------------------------------------------------------------------*)
(* Arith. decision proc packaged up.                                         *)
(*---------------------------------------------------------------------------*)

fun DECIDE tm =
 ARITH_PROVE tm handle HOL_ERR _ => tautLib.TAUT_PROVE tm
                handle HOL_ERR _ => raise ERR "DECIDE" "";


fun DECIDE_TAC (g as (asl,_)) =
((MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith_asm asl)
      THEN ARITH_TAC)
 ORELSE tautLib.TAUT_TAC ORELSE NO_TAC) g;

(*---------------------------------------------------------------------------*)
(* Moving SUC out of patterns on lhs                                         *)
(*---------------------------------------------------------------------------*)

val SUC_TO_NUMERAL_DEFN_CONV = let
  fun UBLIST [] = ALL_CONV
    | UBLIST (h::t) = UNBETA_CONV h THENC RATOR_CONV (UBLIST t)
  fun basic_elim t = let
    (* t of form !n. ..SUC n.. = .. n .. SUC n .. *)
    val (v, body) = dest_forall t
    val sv = numSyntax.mk_suc v
  in
    BINDER_CONV (LAND_CONV (UNBETA_CONV sv) THENC
                 RAND_CONV (UBLIST [sv, v])) THENC
    REWR_CONV arithmeticTheory.SUC_ELIM_NUMERALS THENC
    BINOP_CONV (BINDER_CONV (BINOP_CONV LIST_BETA_CONV) THENC
                RAND_CONV (ALPHA_CONV v))
  end t

  fun push_down t =
      if is_forall (#2 (dest_forall t)) then
        (SWAP_VARS_CONV THENC BINDER_CONV push_down) t
      else ALL_CONV t
  fun push_nth_down n t =
      if n > 0 then BINDER_CONV (push_nth_down (n - 1)) t
      else push_down t
  fun pull_up t =
      if is_forall (#2 (dest_forall t)) then
        (BINDER_CONV pull_up THENC SWAP_VARS_CONV) t
      else ALL_CONV t
  fun pull_upto_nth n t =
      if n > 0 then BINDER_CONV (pull_upto_nth (n - 1)) t
      else pull_up t
  fun push_over_conjs t =
      if is_forall t then
        (BINDER_CONV push_over_conjs THENC FORALL_AND_CONV) t
      else ALL_CONV t

  fun unsuc_conjn c = let
    val (vs, body) = strip_forall c
    val (l, r) = dest_eq body
    val suc_terms = find_terms numSyntax.is_suc l
    fun elim_one_suc st t = let
      val v = numSyntax.dest_suc st
    in
      if is_var v then
        case Lib.total (index (aconv v)) vs of
          NONE => ALL_CONV t
        | SOME i => (push_nth_down i THENC
                     LAST_FORALL_CONV basic_elim THENC
                     push_over_conjs THENC
                     BINOP_CONV (pull_upto_nth i)) t
      else
        ALL_CONV t
    end
  in
    EVERY_CONV (map (EVERY_CONJ_CONV o elim_one_suc) suc_terms) c
  end
  fun reassociate_toplevel_conjns t =
      if is_conj t then
        ((REWR_CONV (GSYM CONJ_ASSOC) THENC
          reassociate_toplevel_conjns) ORELSEC
         RAND_CONV reassociate_toplevel_conjns) t
      else ALL_CONV t
in
  EVERY_CONJ_CONV unsuc_conjn THENC reassociate_toplevel_conjns
end

val _ = Defn.SUC_TO_NUMERAL_DEFN_CONV_hook := SUC_TO_NUMERAL_DEFN_CONV;

val SUC_RULE = Conv.CONV_RULE SUC_TO_NUMERAL_DEFN_CONV;

(* ----------------------------------------------------------------------
    Parsing adjustments
   ---------------------------------------------------------------------- *)

val magic_injn = prim_mk_const {Thy = "arithmetic",
                                Name = GrammarSpecials.nat_elim_term};
val operators = [("+", ``$+``),
                 ("-", ``$-``),
                 ("*", ``$*``),
                 ("<", ``$<``),
                 ("<=", ``$<=``),
                 (">", ``$>``),
                 (">=", ``$>=``),
                 (GrammarSpecials.fromNum_str, magic_injn)];

fun deprecate_num () = let
  fun losety {Name,Thy,Ty} = {Name = Name, Thy = Thy}
  fun doit (s, t) = Parse.temp_remove_ovl_mapping s (losety (dest_thy_const t))
in
  app (ignore o doit) operators
end

fun prefer_num () = app temp_overload_on operators

val _ = Parse.temp_set_grammars ambient_grammars;

end (* numLib *)
