(* ========================================================================= *)
(* Tools for reasoning about wp and wlp.                                     *)
(* ========================================================================= *)

structure wpTools :> wpTools =
struct

open HolKernel Parse boolLib bossLib simpLib metisLib intLib
     integerTheory stringTheory combinTheory listTheory
     posrealTheory posrealLib expectationTheory syntaxTheory wpTheory;

(* ------------------------------------------------------------------------- *)
(* Automatic tool for calculating wlp verification conditions.               *)
(* ------------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "wpTools";

local
  open folTools;

  val prolog_parm =
    {equality = false,
     boolean = false,
     combinator = false,
     mapping_parm = {higher_order = false, with_types = true}};
in
  val prolog = fn ths =>
    let
      val (cs,ths) = FOL_NORM ths
      val lmap = build_map (prolog_parm, cs, ths)
      val lmap = add_thm (([``x:bool``], []), ASSUME ``x:bool``) lmap
    in
      FOL_FIND mlibMeson.prolog lmap mlibMeter.unlimited
    end;
end;

fun find_subterm p =
  let
    val f = find_term p
    fun g t =
      if is_comb t then
        g (f (rator t))
        handle HOL_ERR _ => (g (f (rand t)) handle HOL_ERR _ => t)
      else if is_abs t then
        g (f (body t)) handle HOL_ERR _ => t
      else t
  in
    fn t => g (f t)
  end;

fun abbrev_tac n p (asl,g) =
  let
    val t = find_subterm p g
    val v =
      with_flag (Globals.priming, SOME "")
      (variant (free_varsl (g :: asl))) (mk_var (n, type_of t))
    val th = EXISTS (mk_exists (v, mk_eq (t, v)), t) (REFL t)
  in
    MP_TAC th THEN CONV_TAC LEFT_IMP_EXISTS_CONV THEN GEN_TAC
    THEN DISCH_THEN (fn th => PURE_REWRITE_TAC [th] THEN ASSUME_TAC th)
  end (asl,g);

local
  val mp = prove
    (``!p q. ((\v. p v) = q) ==> !v. q v = p v``,
     CONV_TAC (DEPTH_CONV ETA_CONV)
     THEN REWRITE_TAC [GSYM FUN_EQ_THM]
     THEN MATCH_ACCEPT_TAC EQ_SYM);
in
  val lam_abbrev_tac =
    abbrev_tac "lam" is_abs
    THEN POP_ASSUM (ASSUME_TAC o HO_MATCH_MP mp);
end;

local
  fun gconj tm = (TRY_CONV (RAND_CONV gconj) THENC REWR_CONV AND_IMP_INTRO) tm;
  val tconj = REWR_CONV (GSYM (CONJUNCT1 (SPEC_ALL IMP_CLAUSES)));
  fun sel [] = tconj | sel [_] = ALL_CONV | sel (_ :: _ :: _) = gconj;
in
  fun DISCH_CONJ th = CONV_RULE (sel (hyp th)) (DISCH_ALL th);
end;

local
  val leq_tm = ``Leq : 'a state expect -> 'a state expect -> bool``;

  val dest_leq = dest_binop leq_tm (ERR "dest_leq" "");

  fun mk_leq (a,b) =
      let
        val (_,ty) = dom_rng (hd (snd (dest_type (type_of a))))
        val tm = inst [alpha |-> ty] leq_tm
      in
        mk_comb (mk_comb (tm,a), b)
      end;

  val vc_solve = prolog
    [wlp_abort_vc, wlp_consume_vc, wlp_assign_vc, wlp_seq_vc, wlp_nondet_vc,
     wlp_prob_vc, wlp_while_vc, wlp_skip_vc, wlp_if_vc, wlp_assert_vc];
in
  fun vc_tac (asl,goal) =
    let
      val (pre,wlp_post) = dest_leq goal
      val var = genvar (type_of wlp_post)
      val query = mk_leq (var, wlp_post)
      val result = hd (snd (vc_solve (([var],[]),[query])))
      val (mid,_) = dest_leq (concl result)
      val mp_th = DISCH_CONJ result
    in
      MATCH_MP_TAC leq_trans
      THEN EXISTS_TAC mid
      THEN CONJ_TAC
      THENL [TRY (MATCH_ACCEPT_TAC leq_refl),
             MATCH_MP_TAC mp_th THEN TRY (ACCEPT_TAC TRUTH)]
      THEN REPEAT CONJ_TAC
    end (asl,goal);
end;

fun dest_lam tm =
  let
    val (v,b) = dest_forall tm
    val (l,r) = dest_eq b
    val (la,lb) = dest_comb l
    val _ = is_var la orelse raise ERR "dest_lam" "lhs rator not var"
    val _ = lb = v orelse raise ERR "dest_lam" "lhs rand not bvar"
    val _ = not (free_in la r) orelse raise ERR "dest_lam" "recursive"
  in
    (v,la,r)
  end;

fun dest_triv_lam tm =
  let
    val (v,la,r) = dest_lam tm
    val _ = not (free_in v r) orelse raise ERR "dest_triv_lam" ""
  in
    (v,la,r)
  end;

val is_triv_lam = can dest_triv_lam;

local
  fun f acc _ [] = EVERY (map (fn x => UNDISCH_THEN x (K ALL_TAC)) acc)
    | f acc ys (x :: xs) =
    let
      val p =
        case total dest_lam x of NONE => true
        | SOME (_,l,_) => List.exists (free_in l) (ys @ xs)
    in
      if p then f acc (x :: ys) xs else f (x :: acc) ys xs
    end;
in
  fun elim_redundant_lam_tac (asl,g) = f [] [g] asl (asl,g);
end;

local
  val if_t = (GEN_ALL o CONJUNCT1 o SPEC_ALL) COND_CLAUSES;
  val if_f = (GEN_ALL o CONJUNCT2 o SPEC_ALL) COND_CLAUSES;
  val if_ss = simpLib.++
    (pureSimps.pure_ss,
     simpLib.SSFRAG {ac = [], congs = [], convs = [], dprocs = [],
                      filter = NONE, rewrs = [if_t, if_f]});
in
  fun if_cases_tac thtac (asl,g) =
    let
      val (c,_,_) = dest_cond (find_subterm is_cond g)
    in
      MP_TAC (SPEC c BOOL_CASES_AX)
      THEN STRIP_TAC
      THEN POP_ASSUM (fn th => SIMP_TAC if_ss [th] THEN thtac th)
    end (asl,g);
end;

local
  val int_simps =
    [INT_LE_REFL, INT_SUB_ADD, INT_SUB_RZERO, INT_EQ_LADD, INT_EQ_RADD,
     INT_EQ_SUB_RADD, INT_EQ_SUB_LADD,
     INT_LE_SUB_RADD, INT_LE_SUB_LADD, INT_ADD_RID, INT_ADD_LID,
     INT_ADD_RID_UNIQ, INT_ADD_LID_UNIQ, GSYM INT_ADD_ASSOC,
     int_arithTheory.move_sub, int_arithTheory.less_to_leq_samer,
     INT_NOT_LE]

  fun assume_tac th ths =
    let
      (*val () = print ("\nthm = " ^ thm_to_string th ^ "\n");*)
      val th1 = SIMP_RULE arith_ss ([STRING_11, CHR_11, assign_def] @ ths) th
      val th2 = SIMP_RULE int_ss int_simps th1
      val th3 = SIMP_RULE posreal_reduce_ss [] th2
      val th4 = SIMP_RULE (simpLib.++ (bool_ss, boolSimps.COND_elim_ss)) [] th3
    in
      STRIP_ASSUME_TAC th4
    end;
in
  val wlp_assume_tac = (ASSUM_LIST o assume_tac);
end;

local
  fun simps ths =
      ths @ [min_alt, Lin_def, Cond_def, o_THM, magic_alt, assign_def];
in
  val leq_tac =
    CONV_TAC (REWR_CONV Leq_def)
    THEN GEN_TAC
    THEN ASSUM_LIST
         (SIMP_TAC pureSimps.pure_ss o simps o filter (is_triv_lam o concl))
    THEN REPEAT (if_cases_tac wlp_assume_tac)
    THEN ASSUM_LIST (SIMP_TAC pureSimps.pure_ss o simps)
    THEN REPEAT (if_cases_tac wlp_assume_tac)
    THEN elim_redundant_lam_tac
    THEN RW_TAC posreal_ss []
    THEN Q.UNABBREV_ALL_TAC
    THEN RW_TAC posreal_reduce_ss [bound1_def];
end;

local
  val expand =
    [MAP, LENGTH,
     Nondets_def, NondetAssign_def, Probs_def, ProbAssign_def,
     Program_def, Guards_def, guards_def];
in
  val pure_wlp_tac =
    REPEAT lam_abbrev_tac
    THEN vc_tac;

  val wlp_tac =
    RW_TAC posreal_ss expand
    THEN FULL_SIMP_TAC posreal_reduce_ss []
    THEN pure_wlp_tac
    THEN leq_tac;
end;

end
