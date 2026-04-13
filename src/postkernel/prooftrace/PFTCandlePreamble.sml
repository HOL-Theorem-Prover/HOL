structure PFTCandlePreamble :> PFTCandlePreamble = struct

fun emit {output, binary} = let
  val out = PFTWriter.openOut
    {file = output, binary = binary, version = 1, ruleset = "candle"}

  (* ================================================================ *)
  (* ID allocators                                                    *)
  (* ================================================================ *)

  val next_ty = ref 0
  val next_tm = ref 0
  val next_th = ref 0

  fun alloc_ty () = let val id = !next_ty in next_ty := id + 1; id end
  fun alloc_tm () = let val id = !next_tm in next_tm := id + 1; id end
  fun alloc_th () = let val id = !next_th in next_th := id + 1; id end

  (* ================================================================ *)
  (* Type constructors                                                *)
  (* ================================================================ *)

  fun mk_tyvar name =
    let val id = alloc_ty() in PFTWriter.tyvar out id name; id end

  (* Memoized type/term construction using hash tables.
     The preamble is small so a simple assoc list suffices. *)
  val tyop_memo : (int list * int) list ref = ref []

  fun mk_tyop name args =
    (* All tyops in preamble are min$fun, so key on args only *)
    case List.find (fn (a,_) => a = args) (!tyop_memo) of
      SOME (_, id) => id
    | NONE =>
        let val id = alloc_ty()
        in PFTWriter.tyop out id name args;
           tyop_memo := (args, id) :: !tyop_memo;
           id
        end
  fun mk_fun a b = mk_tyop "fun" [a, b]

  (* ================================================================ *)
  (* Term constructors                                                *)
  (* ================================================================ *)

  (* Memoized term construction using (tag, int, int) keys.
     tag: 0=var, 1=const, 2=comb, 3=abs
     For var/const: key is hash of name + type id
     For comb/abs: key is (a, b) *)
  val comb_memo : (int * int * int) list ref = ref []
                   (* (rator, rand, result_id) *)
  val abs_memo  : (int * int * int) list ref = ref []

  val var_memo   : (string * int * int) list ref = ref []
  val const_memo : (string * int * int) list ref = ref []

  fun mk_var name ty =
    case List.find (fn (n,t,_) => n = name andalso t = ty) (!var_memo) of
      SOME (_, _, id) => id
    | NONE =>
        let val id = alloc_tm()
        in PFTWriter.var out id name ty;
           var_memo := (name, ty, id) :: !var_memo;
           id
        end
  fun mk_const name ty =
    case List.find (fn (n,t,_) => n = name andalso t = ty) (!const_memo) of
      SOME (_, _, id) => id
    | NONE =>
        let val id = alloc_tm()
        in PFTWriter.const out id name ty;
           const_memo := (name, ty, id) :: !const_memo;
           id
        end
  fun mk_comb f x =
    case List.find (fn (a,b,_) => a = f andalso b = x) (!comb_memo) of
      SOME (_, _, id) => id
    | NONE =>
        let val id = alloc_tm()
        in PFTWriter.comb out id f x;
           comb_memo := (f, x, id) :: !comb_memo;
           id
        end
  fun mk_abs v b =
    case List.find (fn (a,c,_) => a = v andalso c = b) (!abs_memo) of
      SOME (_, _, id) => id
    | NONE =>
        let val id = alloc_tm()
        in PFTWriter.abs out id v b;
           abs_memo := (v, b, id) :: !abs_memo;
           id
        end

  fun mk_eq eq_c l r = mk_comb (mk_comb eq_c l) r

  (* ================================================================ *)
  (* Theorem constructors (Candle core rules)                         *)
  (* ================================================================ *)

  fun REFL tm =
    let val id = alloc_th() in PFTWriter.Candle.refl out id tm; id end
  fun TRANS th1 th2 =
    let val id = alloc_th() in PFTWriter.Candle.trans out id th1 th2; id end
  fun MK_COMB th1 th2 =
    let val id = alloc_th() in PFTWriter.Candle.mk_comb out id th1 th2; id end
  fun ABS_thm v th =
    let val id = alloc_th() in PFTWriter.Candle.abs_thm out id v th; id end
  fun BETA tm =
    let val id = alloc_th() in PFTWriter.Candle.beta out id tm; id end
  fun ASSUME tm =
    let val id = alloc_th() in PFTWriter.Candle.assume out id tm; id end
  fun EQ_MP th1 th2 =
    let val id = alloc_th() in PFTWriter.Candle.eq_mp out id th1 th2; id end
  fun DEDUCT_ANTISYM th1 th2 =
    let val id = alloc_th()
    in PFTWriter.Candle.deduct_antisym_rule out id th1 th2; id end
  fun INST th pairs =
    let val id = alloc_th() in PFTWriter.Candle.inst out id th pairs; id end
  fun INST_TYPE th pairs =
    let val id = alloc_th()
    in PFTWriter.Candle.inst_type out id th pairs; id end
  fun SYM th =
    let val id = alloc_th() in PFTWriter.Candle.sym out id th; id end
  fun PROVE_HYP th1 th2 =
    let val id = alloc_th()
    in PFTWriter.Candle.prove_hyp out id th1 th2; id end
  fun NEW_SPEC th names =
    let val id = alloc_th()
    in PFTWriter.Candle.new_specification out id th names; id end

  fun save name th = PFTWriter.save out name th

  (* ================================================================ *)
  (* Derived theorem helpers                                          *)
  (* ================================================================ *)

  (* AP_THM: from ⊢ f = g and term x, derive ⊢ f x = g x *)
  fun AP_THM th x = MK_COMB th (REFL x)

  (* AP_TERM: from term f and ⊢ x = y, derive ⊢ f x = f y *)
  fun AP_TERM f th = MK_COMB (REFL f) th

  (* General beta: given lambda term (abs var body), its bound var,
     and the desired argument, derive ⊢ (λvar. body) arg = body[arg/var].
     When arg = var (same term ID), uses restricted BETA directly.
     Otherwise uses restricted BETA + INST. *)
  fun beta_reduce lam var arg =
    let val app = mk_comb lam var         (* (λvar. body) var *)
        val th = BETA app                 (* ⊢ (λvar. body) var = body *)
    in if var = arg then th
       else INST th [(var, arg)]          (* ⊢ (λvar. body) arg = body[arg/var] *)
    end

  (* Unfold a binary definition: given ⊢ c = λx. λy. body,
     the rhs lambda, its inner lambda (λy. body), and the two bound vars,
     derive ⊢ c x y = body
     (using the same bound vars as arguments, so restricted BETA applies) *)
  fun unfold2 def_th rhs inner var_x var_y =
    let val th1 = AP_THM def_th var_x          (* ⊢ c x = (λx. λy. body) x *)
        val th2 = TRANS th1 (beta_reduce rhs var_x var_x)
                                               (* ⊢ c x = λy. body *)
        val th3 = AP_THM th2 var_y             (* ⊢ c x y = (λy. body) y *)
    in TRANS th3 (beta_reduce inner var_y var_y)
                                               (* ⊢ c x y = body *)
    end

  (* ================================================================ *)
  (* Types — all constructed once upfront                             *)
  (* ================================================================ *)

  val ty_bool  = mk_tyop "bool" []
  val ty_bb    = mk_fun ty_bool ty_bool           (* bool -> bool *)
  val ty_bbb   = mk_fun ty_bool ty_bb             (* bool -> bool -> bool *)
  val ty_bbb_b = mk_fun ty_bbb ty_bool            (* (bbb) -> bool *)

  val ty_A     = mk_tyvar "A"
  val ty_Ab    = mk_fun ty_A ty_bool               (* A -> bool *)
  val ty_Ab_b  = mk_fun ty_Ab ty_bool              (* (A->bool) -> bool *)

  (* ================================================================ *)
  (* Equality constants — one per type, constructed once              *)
  (* ================================================================ *)

  (* For equality at type α: = has type α -> (α -> bool).
     We need the intermediate type α -> bool for each α.
     Some of these are already defined above:
       bool -> bool = ty_bb
       (A->bool) -> bool = ty_Ab_b
       (bbb) -> bool = ty_bbb_b
     Build the remaining ones, then the full equality types. *)
  val ty_bb_b    = mk_fun ty_bb ty_bool               (* (b->b) -> bool *)
  val ty_bbb_b_b = mk_fun ty_bbb_b ty_bool            (* (bbb->b) -> bool *)
  val ty_Ab_b_b  = mk_fun ty_Ab_b ty_bool             (* ((A->b)->b) -> bool *)

  val eq_bool_ty  = ty_bbb                              (* bool -> (bool -> bool) = bbb *)
  val eq_bb_ty    = mk_fun ty_bb ty_bb_b               (* (b->b) -> ((b->b) -> bool) *)
  val eq_bbb_ty   = mk_fun ty_bbb ty_bbb_b             (* bbb -> (bbb -> bool) *)
  val eq_bbb_b_ty = mk_fun ty_bbb_b ty_bbb_b_b         (* (bbb->b) -> ((bbb->b) -> bool) *)
  val eq_Ab_ty    = mk_fun ty_Ab ty_Ab_b                (* (A->b) -> ((A->b) -> bool) *)
  val eq_Ab_b_ty  = mk_fun ty_Ab_b ty_Ab_b_b            (* ((A->b)->b) -> (((A->b)->b) -> bool) *)

  val eq_bool   = mk_const "=" eq_bool_ty
  val eq_bb     = mk_const "=" eq_bb_ty
  val eq_bbb    = mk_const "=" eq_bbb_ty
  val eq_bbb_b  = mk_const "=" eq_bbb_b_ty
  val eq_Ab     = mk_const "=" eq_Ab_ty
  val eq_Ab_b   = mk_const "=" eq_Ab_b_ty

  (* ================================================================ *)
  (* Variables — constructed once                                     *)
  (* ================================================================ *)

  val var_p = mk_var "p" ty_bool
  val var_q = mk_var "q" ty_bool
  val var_t = mk_var "t" ty_bool
  val var_f = mk_var "f" ty_bbb
  val var_P = mk_var "P" ty_Ab
  val var_x = mk_var "x" ty_A

  (* Variables at post-INST_TYPE types, for use when A is instantiated
     to bool in SPEC_pth / GEN_pth / etc. *)
  val var_P_bool = mk_var "P" ty_bb          (* P : bool -> bool *)
  val var_x_bool = mk_var "x" ty_bool        (* x : bool *)

  (* ================================================================ *)
  (* 1. Define T                                                      *)
  (*    T = ((\p:bool. p) = (\p:bool. p))                             *)
  (* ================================================================ *)

  val lam_p_p = mk_abs var_p var_p                (* \p. p *)
  val rhs_T = mk_eq eq_bb lam_p_p lam_p_p        (* (\p.p) = (\p.p) *)

  val var_T_v = mk_var "T" ty_bool
  val def_T_tm = mk_eq eq_bool var_T_v rhs_T      (* T_v = rhs *)
  val T_DEF = NEW_SPEC (ASSUME def_T_tm) ["T"]
  (* T_DEF: ⊢ T = (\p.p) = (\p.p) *)
  val () = save "candle$T_DEF" T_DEF

  val const_T = mk_const "T" ty_bool

  (* ================================================================ *)
  (* TRUTH: ⊢ T                                                      *)
  (* ================================================================ *)

  val TRUTH = EQ_MP (SYM T_DEF) (REFL lam_p_p)
  val () = save "candle$TRUTH" TRUTH

  (* ================================================================ *)
  (* EQT_INTRO_pth: ⊢ t = (t = T)                                   *)
  (* Used as: INST [(t, concl_of_th)] then EQ_MP with th             *)
  (* ================================================================ *)

  val th_assume_t = ASSUME var_t                         (* {t} ⊢ t *)
  val th_da1 = DEDUCT_ANTISYM th_assume_t TRUTH          (* {t} ⊢ t = T *)
  (* concl of th_da1 is t = T *)
  val t_eq_T = mk_eq eq_bool var_t const_T               (* term: t = T *)
  val th_assume_teqT = ASSUME t_eq_T                     (* {t=T} ⊢ t = T *)
  val th_eqt_elim = EQ_MP (SYM th_assume_teqT) TRUTH    (* {t=T} ⊢ t *)
  val EQT_INTRO_pth = DEDUCT_ANTISYM th_eqt_elim th_da1
  (* ⊢ t = (t = T) *)
  val () = save "candle$EQT_INTRO" EQT_INTRO_pth

  (* Helper: EQT_INTRO th = from ⊢ s, derive ⊢ s = T
     In PFT: INST EQT_INTRO_pth [(t, s)] then EQ_MP with th
     But in the preamble, we implement it inline: *)
  fun eqtIntro th_s s =
    EQ_MP (INST EQT_INTRO_pth [(var_t, s)]) th_s

  (* Helper: EQT_ELIM: from th: ⊢ s = T, derive ⊢ s *)
  fun eqtElim th = EQ_MP (SYM th) TRUTH

  (* ================================================================ *)
  (* 2. Define /\                                                     *)
  (*    /\ = \p q. (\f:bbb. f p q) = (\f. f T T)                     *)
  (* ================================================================ *)

  (* types and eq constants already defined above *)

  (* Body: (\f. f p q) = (\f. f T T) *)
  val fp = mk_comb var_f var_p                   (* f p *)
  val fpq = mk_comb fp var_q                     (* f p q *)
  val lam_fpq = mk_abs var_f fpq                 (* \f. f p q *)

  val fT = mk_comb var_f const_T                 (* f T *)
  val fTT = mk_comb fT const_T                   (* f T T *)
  val lam_fTT = mk_abs var_f fTT                 (* \f. f T T *)

  val and_body = mk_eq eq_bbb_b lam_fpq lam_fTT
  (* (\f. f p q) = (\f. f T T) *)

  val and_inner = mk_abs var_q and_body          (* \q. body *)
  val and_rhs = mk_abs var_p and_inner            (* \p. \q. body *)

  val var_and_v = mk_var "/\\" ty_bbb
  val def_and_tm = mk_eq eq_bbb var_and_v and_rhs
  val AND_DEF = NEW_SPEC (ASSUME def_and_tm) ["/\\"]
  val () = save "candle$AND_DEF" AND_DEF

  val const_and = mk_const "/\\" ty_bbb

  (* and_unfold: ⊢ p /\ q = (\f. f p q) = (\f. f T T) *)
  val and_unfold = unfold2 AND_DEF and_rhs and_inner var_p var_q

  (* Commonly used terms — constructed once *)
  val and_p = mk_comb const_and var_p              (* (/\) p *)
  val tm_pq = mk_comb and_p var_q                  (* p /\ q *)

  (* ================================================================ *)
  (* Selectors for extracting conjuncts                               *)
  (*   sel1 = \p. \q. p  (first projection)                          *)
  (*   sel2 = \p. \q. q  (second projection)                         *)
  (* ================================================================ *)

  val sel1_inner = mk_abs var_q var_p             (* \q. p *)
  val sel1 = mk_abs var_p sel1_inner              (* \p. \q. p *)

  val sel2_inner = mk_abs var_q var_q             (* \q. q *)
  val sel2 = mk_abs var_p sel2_inner              (* \p. \q. q *)

  (* ================================================================ *)
  (* sel_app_eq: derive ⊢ (\f. f a b) sel = result                   *)
  (* where result = a (for sel1) or b (for sel2)                      *)
  (* For the preamble, a = p, b = q (same as bound vars).             *)
  (*                                                                  *)
  (* Also need: ⊢ (\f. f T T) sel = T  for both selectors.           *)
  (* ================================================================ *)

  (* ⊢ (\f. f p q) f = f p q  [restricted BETA, f is bound var] *)
  val beta_fpq = BETA (mk_comb lam_fpq var_f)
  (* ⊢ (\f. f T T) f = f T T *)
  val beta_fTT = BETA (mk_comb lam_fTT var_f)

  (* --- sel1 (first projection) applied to (p, q) --- *)
  (* ⊢ sel1 p = \q. p  [restricted BETA] *)
  val beta_sel1_p = BETA (mk_comb sel1 var_p)
  (* ⊢ (\q. p) q = p  [restricted BETA] *)
  val beta_sel1_inner = BETA (mk_comb sel1_inner var_q)
  (* ⊢ sel1 p q = (\q. p) q  [AP_THM] *)
  (* ⊢ sel1 p q = p          [TRANS] *)
  val sel1_pq_eq_p =
    TRANS (AP_THM beta_sel1_p var_q) beta_sel1_inner

  (* ⊢ (\f. f p q) sel1 = sel1 p q  [INST f->sel1] *)
  (* ⊢ (\f. f p q) sel1 = p         [TRANS] *)
  val lhs_sel1_pq =
    TRANS (INST beta_fpq [(var_f, sel1)]) sel1_pq_eq_p

  (* --- sel1 applied to (T, T) --- *)
  (* ⊢ sel1 T = \q. T  [INST p->T in beta_sel1_p] *)
  val beta_sel1_T = INST beta_sel1_p [(var_p, const_T)]
  (* Need term \q. T *)
  val lam_q_T = mk_abs var_q const_T
  (* ⊢ (\q. T) q = T  [restricted BETA] *)
  val beta_lam_q_T = BETA (mk_comb lam_q_T var_q)
  (* ⊢ (\q. T) T = T  [INST q->T] *)
  val beta_lam_q_T_T = INST beta_lam_q_T [(var_q, const_T)]
  (* ⊢ sel1 T T = (\q. T) T  [AP_THM] *)
  (* ⊢ sel1 T T = T           [TRANS] *)
  val sel1_TT_eq_T =
    TRANS (AP_THM beta_sel1_T const_T) beta_lam_q_T_T

  (* ⊢ (\f. f T T) sel1 = sel1 T T  [INST f->sel1] *)
  (* ⊢ (\f. f T T) sel1 = T         [TRANS] *)
  val rhs_sel1_TT =
    TRANS (INST beta_fTT [(var_f, sel1)]) sel1_TT_eq_T

  (* --- sel2 (second projection) applied to (p, q) --- *)
  val beta_sel2_p = BETA (mk_comb sel2 var_p)   (* ⊢ sel2 p = \q. q *)
  val beta_sel2_inner = BETA (mk_comb sel2_inner var_q)  (* ⊢ (\q. q) q = q *)
  val sel2_pq_eq_q =
    TRANS (AP_THM beta_sel2_p var_q) beta_sel2_inner

  val lhs_sel2_pq =
    TRANS (INST beta_fpq [(var_f, sel2)]) sel2_pq_eq_q

  (* --- sel2 applied to (T, T) --- *)
  val beta_sel2_T = INST beta_sel2_p [(var_p, const_T)]
  (* ⊢ (\q. q) q = q  [same as beta_sel2_inner] *)
  (* ⊢ (\q. q) T = T  [INST q->T] *)
  val beta_sel2_inner_T = INST beta_sel2_inner [(var_q, const_T)]
  val sel2_TT_eq_T =
    TRANS (AP_THM beta_sel2_T const_T) beta_sel2_inner_T

  val rhs_sel2_TT =
    TRANS (INST beta_fTT [(var_f, sel2)]) sel2_TT_eq_T

  (* ================================================================ *)
  (* CONJUNCT1_pth: {p /\ q} ⊢ p                                    *)
  (* ================================================================ *)

  (* {p /\ q} ⊢ (\f. f p q) = (\f. f T T) *)
  val th_conj_unfolded = EQ_MP and_unfold (ASSUME tm_pq)

  (* {p /\ q} ⊢ (\f. f p q) sel1 = (\f. f T T) sel1 *)
  val th_ap_sel1 = AP_THM th_conj_unfolded sel1

  (* {p /\ q} ⊢ p = T *)
  val th_p_eq_T = TRANS (TRANS (SYM lhs_sel1_pq) th_ap_sel1) rhs_sel1_TT

  (* {p /\ q} ⊢ p *)
  val CONJUNCT1_pth = eqtElim th_p_eq_T
  val () = save "candle$CONJUNCT1" CONJUNCT1_pth

  (* ================================================================ *)
  (* CONJUNCT2_pth: {p /\ q} ⊢ q                                    *)
  (* ================================================================ *)

  val th_ap_sel2 = AP_THM th_conj_unfolded sel2
  val th_q_eq_T = TRANS (TRANS (SYM lhs_sel2_pq) th_ap_sel2) rhs_sel2_TT
  val CONJUNCT2_pth = eqtElim th_q_eq_T
  val () = save "candle$CONJUNCT2" CONJUNCT2_pth

  (* ================================================================ *)
  (* CONJ_pth: {p, q} ⊢ p /\ q                                     *)
  (* Following HOL Light's CONJ pth2 derivation.                      *)
  (* ================================================================ *)

  (* {p} ⊢ p = T *)
  val th_p_eqt = eqtIntro (ASSUME var_p) var_p
  (* {q} ⊢ q = T *)
  val th_q_eqt = eqtIntro (ASSUME var_q) var_q

  (* {p} ⊢ f p = f T  [AP_TERM f (p = T)] *)
  val th_fp_fT = AP_TERM var_f th_p_eqt
  (* {p, q} ⊢ f p q = f T T  [MK_COMB] *)
  val th_fpq_fTT = MK_COMB th_fp_fT th_q_eqt
  (* {p, q} ⊢ (\f. f p q) = (\f. f T T)  [ABS f] *)
  val th_lam_eq = ABS_thm var_f th_fpq_fTT

  (* ⊢ p /\ q = body  [and_unfold, already derived] *)
  (* {p, q} ⊢ p /\ q  [EQ_MP (SYM and_unfold) th_lam_eq] *)
  val CONJ_pth = EQ_MP (SYM and_unfold) th_lam_eq
  val () = save "candle$CONJ" CONJ_pth

  (* ================================================================ *)
  (* 3. Define ==>                                                    *)
  (*    ==> = \p q. (p /\ q) = p                                     *)
  (*    i.e., ==> = \p q. (p /\ q <=> p)                             *)
  (* ================================================================ *)

  (* RHS: \p q. (p /\ q) = p *)
  val imp_body = mk_eq eq_bool tm_pq var_p        (* (p /\ q) = p *)
  val imp_inner = mk_abs var_q imp_body            (* \q. (p /\ q) = p *)
  val imp_rhs = mk_abs var_p imp_inner             (* \p. \q. (p /\ q) = p *)

  val var_imp_v = mk_var "==>" ty_bbb
  val def_imp_tm = mk_eq eq_bbb var_imp_v imp_rhs
  val IMP_DEF = NEW_SPEC (ASSUME def_imp_tm) ["==>"]
  val () = save "candle$IMP_DEF" IMP_DEF

  val const_imp = mk_const "==>" ty_bbb

  (* imp_unfold: ⊢ (p ==> q) = ((p /\ q) = p) *)
  val imp_unfold = unfold2 IMP_DEF imp_rhs imp_inner var_p var_q
  val tm_imp_pq = mk_comb (mk_comb const_imp var_p) var_q  (* p ==> q *)

  (* ================================================================ *)
  (* MP_rth: {p} ⊢ (p ==> q) = q                                    *)
  (* DEDUCT_ANTISYM of the two directions of IMP_DEF.                *)
  (*                                                                  *)
  (* Usage: MP(ith: A ⊢ a ==> b, th: B ⊢ a) =                      *)
  (*   INST MP_rth [(p,a),(q,b)], DEDUCT_ANTISYM with th, two EQ_MPs *)
  (*   → A ∪ B ⊢ b                                                  *)
  (* ================================================================ *)

  (* DISCH direction: {q} ⊢ p ==> q
     DEDUCT_ANTISYM CONJ_pth CONJUNCT1_pth gives {q} ⊢ (p/\q)=p
     (CONJ_pth hyps {p,q} minus CONJUNCT1_pth concl p = {q};
      CONJUNCT1_pth hyps {p/\q} minus CONJ_pth concl p/\q = {})
     EQ_MP (SYM imp_unfold) converts to {q} ⊢ p ==> q *)
  val da_conj_c1 = DEDUCT_ANTISYM CONJ_pth CONJUNCT1_pth
  val imp_pth = EQ_MP (SYM imp_unfold) da_conj_c1

  (* MP direction: {p ==> q, p} ⊢ q
     Unfold ==> to get {p==>q} ⊢ (p/\q)=p, SYM + EQ_MP with ASSUME p
     gives {p==>q, p} ⊢ p/\q, then PROVE_HYP with CONJUNCT2_pth *)
  val th_imp_unfolded = EQ_MP imp_unfold (ASSUME tm_imp_pq)
  val th_conj_from_imp = EQ_MP (SYM th_imp_unfolded) (ASSUME var_p)
  val imp_qth = PROVE_HYP th_conj_from_imp CONJUNCT2_pth

  (* Combine: {p} ⊢ (p ==> q) = q *)
  val MP_rth = DEDUCT_ANTISYM imp_pth imp_qth
  val () = save "candle$MP" MP_rth

  (* ================================================================ *)
  (* DISCH_pth: ⊢ ((p /\ q) = p) = (p ==> q)                       *)
  (* i.e., SYM imp_unfold. Used to convert a deductAntisym result    *)
  (* into an implication.                                             *)
  (* ================================================================ *)

  val DISCH_pth = SYM imp_unfold
  val () = save "candle$DISCH" DISCH_pth


  (* ================================================================ *)
  (* EQ_IMP_RULE pths                                                 *)
  (* EQ_IMP_RULE1_pth: {p = q} ⊢ p ==> q                           *)
  (* EQ_IMP_RULE2_pth: {p = q} ⊢ q ==> p                           *)
  (* Derived via: EQ_MP gives {p=q, p} ⊢ q, then do_DISCH removes p *)
  (* ================================================================ *)

  val tm_p_eq_q = mk_eq eq_bool var_p var_q

  val th_peqq = ASSUME tm_p_eq_q                    (* {p=q} ⊢ p = q *)
  val th_assume_p = ASSUME var_p                     (* {p} ⊢ p *)
  val th_q_from_peqq = EQ_MP th_peqq th_assume_p    (* {p=q, p} ⊢ q *)

  (* do_DISCH p from {p=q, p} ⊢ q gives {p=q} ⊢ p ==> q.
     DISCH removes p via CONJ + CONJUNCT1 + DEDUCT_ANTISYM + IMP_DEF. *)

  (* CONJ helper: given th1: A ⊢ a and th2: B ⊢ b,
     produce A ∪ B ⊢ a /\ b.
     Uses CONJ_pth + INST + PROVE_HYP. *)
  fun do_CONJ th1 a th2 b =
    let val pth = INST CONJ_pth [(var_p, a), (var_q, b)]
        (* {a, b} ⊢ a /\ b *)
        val pth2 = PROVE_HYP th1 pth    (* discharge a *)
        (* A ∪ ({a,b} \ {a}) ⊢ a /\ b = A ∪ {b} ⊢ a /\ b *)
    in PROVE_HYP th2 pth2 end           (* discharge b *)
    (* A ∪ B ⊢ a /\ b *)

  (* CONJUNCT1 helper: given th: A ⊢ a /\ b and terms a, b,
     produce A ⊢ a *)
  fun do_CONJUNCT1 th a b =
    let val pth = INST CONJUNCT1_pth [(var_p, a), (var_q, b)]
        (* {a /\ b} ⊢ a *)
    in PROVE_HYP th pth end
    (* A ⊢ a  (discharged a /\ b) *)

  (* CONJUNCT2 helper *)
  fun do_CONJUNCT2 th a b =
    let val pth = INST CONJUNCT2_pth [(var_p, a), (var_q, b)]
    in PROVE_HYP th pth end

  (* DISCH helper: given tm a and th: A ⊢ c,
     produce A \ {a} ⊢ a ==> c *)
  fun do_DISCH a th c a_and_c =
    let val th1 = do_CONJ (ASSUME a) a th c
        val th2 = do_CONJUNCT1 (ASSUME a_and_c) a c
        (* {a /\ c} ⊢ a *)
        val th3 = DEDUCT_ANTISYM th1 th2
        (* A \ {a} ⊢ (a /\ c) = a *)
        val th4 = INST DISCH_pth [(var_p, a), (var_q, c)]
        (* ⊢ ((a /\ c) = a) = (a ==> c) *)
    in EQ_MP th4 th3 end

  (* Now derive EQ_IMP_RULE pths *)
  val EQ_IMP_RULE1_pth = do_DISCH var_p th_q_from_peqq var_q tm_pq
  (* {p = q} ⊢ p ==> q *)
  val () = save "candle$EQ_IMP_RULE1" EQ_IMP_RULE1_pth

  val th_p_from_qeqp = EQ_MP (SYM th_peqq) (ASSUME var_q)
  (* {p=q, q} ⊢ p *)
  val tm_qp = mk_comb (mk_comb const_and var_q) var_p  (* q /\ p *)
  val EQ_IMP_RULE2_pth = do_DISCH var_q th_p_from_qeqp var_p tm_qp
  (* {p = q} ⊢ q ==> p *)
  val () = save "candle$EQ_IMP_RULE2" EQ_IMP_RULE2_pth

  (* ================================================================ *)
  (* NOT_ELIM_pth: {~p} ⊢ p ==> F                                   *)
  (* NOT_INTRO_pth: {p ==> F} ⊢ ~p                                  *)
  (* (Deferred until F and ~ are defined)                             *)
  (* ================================================================ *)

  (* ================================================================ *)
  (* 4. Define !                                                      *)
  (*    ! = \P:A->bool. P = \x. T                                    *)
  (* ================================================================ *)

  val lam_x_T = mk_abs var_x const_T              (* \x. T *)
  val forall_body = mk_eq eq_Ab var_P lam_x_T
  (* P = \x. T *)
  val forall_rhs = mk_abs var_P forall_body        (* \P. P = \x. T *)

  val var_forall_v = mk_var "!" ty_Ab_b
  val def_forall_tm = mk_eq eq_Ab_b var_forall_v forall_rhs
  val FORALL_DEF = NEW_SPEC (ASSUME def_forall_tm) ["!"]
  val () = save "candle$FORALL_DEF" FORALL_DEF

  val const_forall = mk_const "!" ty_Ab_b

  (* forall_unfold: ⊢ !P = (P = \x. T) *)
  val forall_unfold_th =
    let val th1 = AP_THM FORALL_DEF var_P
        val th2 = beta_reduce forall_rhs var_P var_P
    in TRANS th1 th2 end
  (* ⊢ !P = (P = \x. T) *)

  (* ================================================================ *)
  (* SPEC_pth: ⊢ (!P) ==> P x                                       *)
  (* Following HOL Light's SPEC derivation.                           *)
  (* ================================================================ *)

  val tm_forall_P = mk_comb const_forall var_P     (* !P *)
  val th_spec1 = EQ_MP forall_unfold_th (ASSUME tm_forall_P)
  (* {!P} ⊢ P = \x. T *)
  val tm_Px = mk_comb var_P var_x                  (* P x *)
  val th_spec2 = AP_THM th_spec1 var_x
  (* {!P} ⊢ P x = (\x. T) x *)
  val th_spec3 = TRANS th_spec2 (beta_reduce lam_x_T var_x var_x)
  (* {!P} ⊢ P x = T *)
  val th_spec4 = eqtElim th_spec3
  (* {!P} ⊢ P x *)
  val tm_forallP_and_Px = mk_comb (mk_comb const_and tm_forall_P) tm_Px
  val SPEC_pth = do_DISCH tm_forall_P th_spec4 tm_Px tm_forallP_and_Px
  (* ⊢ (!P) ==> P x *)
  val () = save "candle$SPEC" SPEC_pth

  (* ================================================================ *)
  (* GEN helper derivation                                            *)
  (* HOL Light's GEN:                                                 *)
  (*   pth = SYM (CONV_RULE (RAND_CONV BETA_CONV)                    *)
  (*              (AP_THM FORALL_DEF P))                              *)
  (*       = ⊢ (P = \x. T) = !P                                     *)
  (*   GEN x th = EQ_MP (INST [mk_abs(x, concl th) / P] pth)        *)
  (*                     (ABS x (EQT_INTRO th))                       *)
  (* ================================================================ *)

  val GEN_pth = SYM forall_unfold_th
  (* ⊢ (P = \x. T) = !P *)
  val () = save "candle$GEN" GEN_pth

  (* ================================================================ *)
  (* Helper: do_MP — inline MP using MP_rth                          *)
  (*   from ith: A ⊢ a ==> b and th: B ⊢ a, derive A ∪ B ⊢ b      *)
  (* ================================================================ *)

  fun do_MP ith a b th =
    let val rth_inst = INST MP_rth [(var_p, a), (var_q, b)]
        (* {a} ⊢ (a ==> b) = b *)
        val da = DEDUCT_ANTISYM th rth_inst
        val th2 = EQ_MP da th
    in EQ_MP th2 ith end

  (* ================================================================ *)
  (* Helper: do_GEN — inline GEN using GEN_pth                       *)
  (*   from th: A ⊢ s, v not free in A, derive A ⊢ ∀v. s            *)
  (*   body_tm = mk_abs(v, s_tm), lam_v_T = mk_abs(v, T)            *)
  (* ================================================================ *)

  fun do_GEN v th s_tm body_tm lam_v_T =
    let val th1 = eqtIntro th s_tm                   (* A ⊢ s = T *)
        val th2 = ABS_thm v th1                      (* A ⊢ (\v. s) = (\v. T) *)
        val pth = INST (INST_TYPE GEN_pth [(ty_A, ty_bool)])
                       [(var_P_bool, body_tm), (var_x_bool, v)]
                                                     (* ⊢ (body = \v. T) = !body *)
    in EQ_MP pth th2 end

  (* ================================================================ *)
  (* Helper: do_SPEC — inline SPEC using SPEC_pth                    *)
  (*   from th: A ⊢ ∀P, and term t, derive A ⊢ P t                  *)
  (*   abs_tm = the predicate, t = the argument                       *)
  (*   Needs INST_TYPE to match the type.                             *)
  (* ================================================================ *)

  (* ! at type (bool->bool)->bool, needed by do_SPEC_bool and others *)
  val const_forall_bool = mk_const "!" (mk_fun ty_bb ty_bool)

  (* For preamble use at type bool (A = bool): *)
  fun do_SPEC_bool abs_tm t th =
    let val pth = INST_TYPE SPEC_pth [(ty_A, ty_bool)]
        val pth2 = INST pth [(var_P_bool, abs_tm), (var_x_bool, t)]
        (* ⊢ (! abs_tm) ==> abs_tm t *)
    in do_MP pth2 (mk_comb const_forall_bool abs_tm)
                  (mk_comb abs_tm t) th
    end

  (* ================================================================ *)
  (* 5. Define ?                                                      *)
  (*    ? = \P:A->bool. !q. (!x. P x ==> q) ==> q                   *)
  (* ================================================================ *)

  val var_Q = mk_var "Q" ty_bool

  (* Build the body: !q. (!x. P x ==> q) ==> q *)
  (* P x ==> q *)
  val tm_Px_imp_q = mk_comb (mk_comb const_imp tm_Px) var_q
  (* \x. P x ==> q *)
  val lam_x_Px_imp_q = mk_abs var_x tm_Px_imp_q
  (* !x. P x ==> q  — need ! at type A *)
  val tm_forall_x_Px_imp_q = mk_comb const_forall lam_x_Px_imp_q
  (* (!x. P x ==> q) ==> q *)
  val tm_inner_imp = mk_comb (mk_comb const_imp tm_forall_x_Px_imp_q) var_q
  (* \q. (!x. P x ==> q) ==> q *)
  val lam_q_inner = mk_abs var_q tm_inner_imp
  (* !q. (!x. P x ==> q) ==> q *)
  val exists_body = mk_comb const_forall_bool lam_q_inner

  val exists_rhs = mk_abs var_P exists_body         (* \P. !q. ... *)
  val ty_Ab_A = mk_fun ty_Ab ty_A                   (* (A->bool) -> A *)

  val var_exists_v = mk_var "?" ty_Ab_b
  val def_exists_tm = mk_eq eq_Ab_b var_exists_v exists_rhs
  val EXISTS_DEF = NEW_SPEC (ASSUME def_exists_tm) ["?"]
  val () = save "candle$EXISTS_DEF" EXISTS_DEF

  val const_exists = mk_const "?" ty_Ab_b

  (* exists_unfold: ⊢ ?P = !q. (!x. P x ==> q) ==> q *)
  val exists_unfold_th =
    let val th1 = AP_THM EXISTS_DEF var_P
        val th2 = beta_reduce exists_rhs var_P var_P
    in TRANS th1 th2 end

  val tm_exists_P = mk_comb const_exists var_P       (* ?P *)

  (* ================================================================ *)
  (* EXISTS_pth: {P x} ⊢ ?P                                         *)
  (* Following HOL Light's EXISTS derivation (pth).                   *)
  (* ================================================================ *)

  (* th1 = exists_unfold: ⊢ ?P = !q. (!x. P x ==> q) ==> q *)
  (* We need: {P x} ⊢ !q. (!x. P x ==> q) ==> q *)
  (* Then EQ_MP (SYM exists_unfold) gives {P x} ⊢ ?P *)

  (* Step 1: ASSUME (P x): {P x} ⊢ P x *)
  val th_assume_Px = ASSUME tm_Px

  (* Step 2: ASSUME (!x. P x ==> q) *)
  val th_assume_forall = ASSUME tm_forall_x_Px_imp_q

  (* Step 3: SPEC x from step 2: {!x. P x ==> q} ⊢ P x ==> q *)
  (* Use SPEC_pth at type A, with P := \x. P x ==> q, x := x *)
  val spec_inst = INST (INST_TYPE SPEC_pth [(ty_A, ty_A)])
                       [(var_P, lam_x_Px_imp_q), (var_x, var_x)]
  (* ⊢ (!(\x. P x ==> q)) ==> (\x. P x ==> q) x *)
  (* Need to beta-reduce (\x. P x ==> q) x *)
  val tm_lam_app = mk_comb lam_x_Px_imp_q var_x
  val th_beta_lam = beta_reduce lam_x_Px_imp_q var_x var_x
  (* ⊢ (\x. P x ==> q) x = (P x ==> q) *)

  (* The SPEC conclusion has (\x. P x ==> q) x on the RHS. After MP
     and beta, we get P x ==> q. Let me do this step by step. *)
  val th_spec_result = do_MP spec_inst tm_forall_x_Px_imp_q tm_lam_app
                            th_assume_forall
  (* {!x. P x ==> q} ⊢ (\x. P x ==> q) x *)

  (* Beta-reduce: *)
  val th_Px_imp_q = EQ_MP th_beta_lam th_spec_result
  (* {!x. P x ==> q} ⊢ P x ==> q *)

  (* Step 4: MP with P x *)
  val th_q_from_all = do_MP th_Px_imp_q tm_Px var_q th_assume_Px
  (* {P x, !x. P x ==> q} ⊢ q *)

  (* Step 5: DISCH (!x. P x ==> q) *)
  val tm_conj_forall_q = mk_comb (mk_comb const_and tm_forall_x_Px_imp_q) var_q
  val th_disch_forall = do_DISCH tm_forall_x_Px_imp_q th_q_from_all var_q
                                 tm_conj_forall_q
  (* {P x} ⊢ (!x. P x ==> q) ==> q *)

  (* Step 6: GEN q *)
  val lam_q_forall_imp_q = mk_abs var_q tm_inner_imp  (* same as lam_q_inner *)
  val lam_q_T_bool = mk_abs var_q const_T
  val th_gen_q = do_GEN var_q th_disch_forall tm_inner_imp
                        lam_q_forall_imp_q lam_q_T_bool
  (* {P x} ⊢ !q. (!x. P x ==> q) ==> q *)

  (* Step 7: EQ_MP *)
  val EXISTS_pth = EQ_MP (SYM exists_unfold_th) th_gen_q
  (* {P x} ⊢ ?P *)
  val () = save "candle$EXISTS" EXISTS_pth

  (* ================================================================ *)
  (* CHOOSE_pth: ⊢ (?P) ==> (!x. P x ==> Q) ==> Q                  *)
  (* Following HOL Light's CHOOSE derivation.                         *)
  (* ================================================================ *)

  (* exists_unfold: ⊢ ?P = !q. (!x. P x ==> q) ==> q *)
  (* EQ_IMP_RULE1: {?P = stuff} ⊢ ?P ==> stuff *)
  (* EQ_MP: {?P} ⊢ !q. (!x. P x ==> q) ==> q *)
  (* SPEC Q: ⊢ (!x. P x ==> Q) ==> Q *)
  (* Combine via MP *)

  (* {?P} ⊢ !q. (!x. P x ==> q) ==> q *)
  val th_exists_unfolded = EQ_MP exists_unfold_th (ASSUME tm_exists_P)

  (* SPEC Q from the above (at type bool) *)
  (* We need do_SPEC_bool with abs = lam_q_inner, t = var_Q *)
  val tm_inner_imp_Q = mk_comb (mk_comb const_imp
    (mk_comb const_forall (mk_abs var_x (mk_comb (mk_comb const_imp tm_Px) var_Q))))
    var_Q
  val th_spec_Q_pre = do_SPEC_bool lam_q_inner var_Q th_exists_unfolded
  (* {?P} ⊢ (\q. (!x. P x ==> q) ==> q) Q — un-beta-reduced *)
  val th_spec_Q = EQ_MP (beta_reduce lam_q_inner var_q var_Q) th_spec_Q_pre
  (* {?P} ⊢ (!x. P x ==> Q) ==> Q *)

  (* DISCH (?P) *)
  val tm_Px_imp_Q = mk_comb (mk_comb const_imp tm_Px) var_Q
  val lam_x_Px_imp_Q = mk_abs var_x tm_Px_imp_Q
  val tm_forall_x_Px_imp_Q = mk_comb const_forall lam_x_Px_imp_Q
  val tm_conj_ep_inner = mk_comb (mk_comb const_and tm_exists_P) tm_inner_imp_Q
  val CHOOSE_pth = do_DISCH tm_exists_P th_spec_Q tm_inner_imp_Q tm_conj_ep_inner
  (* ⊢ (?P) ==> (!x. P x ==> Q) ==> Q *)
  val () = save "candle$CHOOSE" CHOOSE_pth

  (* ================================================================ *)
  (* 6. Define \/                                                     *)
  (*    \/ = \p q. !r. (p ==> r) ==> (q ==> r) ==> r                *)
  (* ================================================================ *)

  val var_r = mk_var "r" ty_bool

  (* p ==> r *)
  val tm_p_imp_r = mk_comb (mk_comb const_imp var_p) var_r
  (* q ==> r *)
  val tm_q_imp_r = mk_comb (mk_comb const_imp var_q) var_r
  (* (q ==> r) ==> r *)
  val tm_qr_imp_r = mk_comb (mk_comb const_imp tm_q_imp_r) var_r
  (* (p ==> r) ==> (q ==> r) ==> r *)
  val tm_pr_qr_r = mk_comb (mk_comb const_imp tm_p_imp_r) tm_qr_imp_r
  (* \r. (p ==> r) ==> (q ==> r) ==> r *)
  val lam_r_body = mk_abs var_r tm_pr_qr_r
  (* !r. ... *)
  val or_body = mk_comb const_forall_bool lam_r_body

  val or_inner = mk_abs var_q or_body                (* \q. !r. ... *)
  val or_rhs = mk_abs var_p or_inner                 (* \p. \q. !r. ... *)

  val var_or_v = mk_var "\\/" ty_bbb
  val def_or_tm = mk_eq eq_bbb var_or_v or_rhs
  val OR_DEF = NEW_SPEC (ASSUME def_or_tm) ["\\/"]
  val () = save "candle$OR_DEF" OR_DEF

  val const_or = mk_const "\\/" ty_bbb

  (* or_unfold: ⊢ p \/ q = !r. (p ==> r) ==> (q ==> r) ==> r *)
  val or_unfold = unfold2 OR_DEF or_rhs or_inner var_p var_q
  val or_p = mk_comb const_or var_p
  val tm_p_or_q = mk_comb or_p var_q                 (* p \/ q *)

  (* ================================================================ *)
  (* DISJ1_pth: {p} ⊢ p \/ q                                        *)
  (* ================================================================ *)

  (* Need: {p} ⊢ !r. (p ==> r) ==> (q ==> r) ==> r *)
  (* From ASSUME (p ==> r) and ASSUME p, MP gives {p, p==>r} ⊢ r *)
  val th_assume_p_imp_r = ASSUME tm_p_imp_r
  val th_r_from_p = do_MP th_assume_p_imp_r var_p var_r (ASSUME var_p)
  (* {p, p ==> r} ⊢ r *)

  (* DISCH (q ==> r): {p, p ==> r} ⊢ (q ==> r) ==> r *)
  val tm_conj_qr_r = mk_comb (mk_comb const_and tm_q_imp_r) var_r
  val th_disch_qr = do_DISCH tm_q_imp_r th_r_from_p var_r tm_conj_qr_r
  (* {p, p ==> r} ⊢ (q ==> r) ==> r *)

  (* DISCH (p ==> r): {p} ⊢ (p ==> r) ==> (q ==> r) ==> r *)
  val tm_conj_pr_rest = mk_comb (mk_comb const_and tm_p_imp_r) tm_qr_imp_r
  val th_disch_pr = do_DISCH tm_p_imp_r th_disch_qr tm_qr_imp_r tm_conj_pr_rest
  (* {p} ⊢ (p ==> r) ==> (q ==> r) ==> r *)

  (* GEN r *)
  val lam_r_pr_qr_r = lam_r_body  (* already have it *)
  val lam_r_T = mk_abs var_r const_T
  val th_gen_r = do_GEN var_r th_disch_pr tm_pr_qr_r lam_r_pr_qr_r lam_r_T
  (* {p} ⊢ !r. (p ==> r) ==> (q ==> r) ==> r *)

  (* EQ_MP (SYM or_unfold) *)
  val DISJ1_pth = EQ_MP (SYM or_unfold) th_gen_r
  (* {p} ⊢ p \/ q *)
  val () = save "candle$DISJ1" DISJ1_pth

  (* ================================================================ *)
  (* DISJ2_pth: {q} ⊢ p \/ q                                        *)
  (* ================================================================ *)

  (* Same structure but MP with q ==> r instead of p ==> r *)
  val th_assume_q_imp_r = ASSUME tm_q_imp_r
  val th_r_from_q = do_MP th_assume_q_imp_r var_q var_r (ASSUME var_q)
  (* {q, q ==> r} ⊢ r *)

  val th_disch_qr2 = do_DISCH tm_q_imp_r th_r_from_q var_r
    (mk_comb (mk_comb const_and tm_q_imp_r) var_r)
  (* {q} ⊢ (q ==> r) ==> r *)

  (* DISCH (p ==> r): but we already have r, just need to add the implication *)
  val tm_conj_pr_rest2 = mk_comb (mk_comb const_and tm_p_imp_r) tm_qr_imp_r
  val th_disch_pr2 = do_DISCH tm_p_imp_r th_disch_qr2 tm_qr_imp_r tm_conj_pr_rest2
  (* {q} ⊢ (p ==> r) ==> (q ==> r) ==> r *)

  val th_gen_r2 = do_GEN var_r th_disch_pr2 tm_pr_qr_r lam_r_pr_qr_r lam_r_T
  (* {q} ⊢ !r. ... *)

  val DISJ2_pth = EQ_MP (SYM or_unfold) th_gen_r2
  (* {q} ⊢ p \/ q *)
  val () = save "candle$DISJ2" DISJ2_pth

  (* ================================================================ *)
  (* DISJ_CASES_pth: {p \/ q, p ==> r, q ==> r} ⊢ r                *)
  (* ================================================================ *)

  (* EQ_MP or_unfold (ASSUME (p \/ q)):
     {p \/ q} ⊢ !r. (p ==> r) ==> (q ==> r) ==> r *)
  val th_or_unfolded = EQ_MP or_unfold (ASSUME tm_p_or_q)

  (* SPEC r *)
  val th_spec_r_pre = do_SPEC_bool lam_r_body var_r th_or_unfolded
  (* {p \/ q} ⊢ (\r. (p ==> r) ==> (q ==> r) ==> r) r — un-beta-reduced *)
  val th_spec_r = EQ_MP (beta_reduce lam_r_body var_r var_r) th_spec_r_pre
  (* {p \/ q} ⊢ (p ==> r) ==> (q ==> r) ==> r *)

  (* MP with (p ==> r) *)
  val th_mp1 = do_MP th_spec_r tm_p_imp_r tm_qr_imp_r (ASSUME tm_p_imp_r)
  (* {p \/ q, p ==> r} ⊢ (q ==> r) ==> r *)

  (* MP with (q ==> r) *)
  val DISJ_CASES_pth = do_MP th_mp1 tm_q_imp_r var_r (ASSUME tm_q_imp_r)
  (* {p \/ q, p ==> r, q ==> r} ⊢ r *)
  val () = save "candle$DISJ_CASES" DISJ_CASES_pth

  (* ================================================================ *)
  (* 7. Define F                                                      *)
  (*    F = !p:bool. p                                                *)
  (* ================================================================ *)

  (* !p. p  (reuse lam_p_p = \p:bool. p from T_DEF) *)
  val F_body = mk_comb const_forall_bool lam_p_p      (* !(\p. p) = !p. p *)

  val var_F_v = mk_var "F" ty_bool
  val def_F_tm = mk_eq eq_bool var_F_v F_body
  val F_DEF = NEW_SPEC (ASSUME def_F_tm) ["F"]
  val () = save "candle$F_DEF" F_DEF

  val const_F = mk_const "F" ty_bool

  (* F_unfold: ⊢ F = !p. p *)
  (* F_DEF already IS ⊢ F = !p. p, no beta needed *)

  (* CONTR_pth: {F} ⊢ p  (falsity elimination) *)
  (* F = !p. p, so {F} ⊢ !p. p, then SPEC p gives {F} ⊢ p *)
  val th_F_unfolded = EQ_MP F_DEF (ASSUME const_F)
  (* {F} ⊢ !p. p  (i.e., !(\p.p)) *)
  val CONTR_pth_pre = do_SPEC_bool lam_p_p var_p th_F_unfolded
  (* {F} ⊢ (\p. p) p — un-beta-reduced *)
  val CONTR_pth = EQ_MP (beta_reduce lam_p_p var_p var_p) CONTR_pth_pre
  (* {F} ⊢ p *)
  val () = save "candle$CONTR" CONTR_pth

  (* ================================================================ *)
  (* 8. Define ~                                                      *)
  (*    ~ = \p. p ==> F                                               *)
  (* ================================================================ *)

  val tm_p_imp_F = mk_comb (mk_comb const_imp var_p) const_F  (* p ==> F *)
  val neg_rhs = mk_abs var_p tm_p_imp_F               (* \p. p ==> F *)

  val var_neg_v = mk_var "~" ty_bb
  val def_neg_tm = mk_eq eq_bb var_neg_v neg_rhs
  val NEG_DEF = NEW_SPEC (ASSUME def_neg_tm) ["~"]
  val () = save "candle$NOT_DEF" NEG_DEF

  val const_neg = mk_const "~" ty_bb

  (* neg_unfold: ⊢ ~p = (p ==> F) *)
  val neg_unfold =
    let val th1 = AP_THM NEG_DEF var_p
        val th2 = beta_reduce neg_rhs var_p var_p
    in TRANS th1 th2 end

  val tm_neg_p = mk_comb const_neg var_p               (* ~p *)

  (* NOT_ELIM_pth: {~p} ⊢ p ==> F *)
  val NOT_ELIM_pth = EQ_MP neg_unfold (ASSUME tm_neg_p)
  val () = save "candle$NOT_ELIM" NOT_ELIM_pth

  (* NOT_INTRO_pth: {p ==> F} ⊢ ~p *)
  val NOT_INTRO_pth = EQ_MP (SYM neg_unfold) (ASSUME tm_p_imp_F)
  val () = save "candle$NOT_INTRO" NOT_INTRO_pth

  (* ================================================================ *)
  (* 9. Introduce @ and axioms                                        *)
  (* ================================================================ *)

  (* NEW_CONST for @ : (A -> bool) -> A *)
  val () = PFTWriter.new_const out "@" ty_Ab_A

  val const_select = mk_const "@" ty_Ab_A

  (* SELECT_AX: ⊢ !P. !x. P x ==> P (@ P) *)
  val tm_select_P = mk_comb const_select var_P        (* @ P *)
  val tm_P_select = mk_comb var_P tm_select_P          (* P (@ P) *)
  val tm_Px_imp_Pselect = mk_comb (mk_comb const_imp tm_Px) tm_P_select
  val lam_x_Px_imp_Ps = mk_abs var_x tm_Px_imp_Pselect
  val tm_forall_x_inner = mk_comb const_forall lam_x_Px_imp_Ps
  val lam_P_body = mk_abs var_P tm_forall_x_inner
  val const_forall_Ab = mk_const "!" ty_Ab_b_b
  val tm_forall_P_body = mk_comb const_forall_Ab lam_P_body

  val SELECT_AX_th = alloc_th()
  val () = PFTWriter.axiom out SELECT_AX_th tm_forall_P_body (SOME "SELECT_AX")
  val () = save "candle$SELECT_AX" SELECT_AX_th

  (* SELECT_AX with outer ∀P specialized out (P free):
     ⊢ !x. P x ==> P (@ P)
     Used by exist_to_witness which needs to INST P. *)
  val select_ax_spec = let
    (* SPEC_pth at type (A->bool): ⊢ (!P') ==> P' x'
       where P' : (A->bool)->bool and x' : A->bool.
       Need fresh variables at the post-INST_TYPE types. *)
    val spec_Ab = INST_TYPE SPEC_pth [(ty_A, ty_Ab)]
    val var_P' = mk_var "P" ty_Ab_b       (* P : (A->bool) -> bool *)
    val var_x' = mk_var "x" ty_Ab         (* x : A->bool *)
    val pth = INST spec_Ab [(var_P', lam_P_body), (var_x', var_P)]
    (* pth: ⊢ (∀P. ∀x. P x ==> P(@P)) ==> (λP. ∀x. P x ==> P(@P)) P *)
    val lam_P_body_app = mk_comb lam_P_body var_P
    val mp_result = do_MP pth tm_forall_P_body lam_P_body_app SELECT_AX_th
    (* mp_result: ⊢ (λP. ∀x. P x ==> P(@P)) P *)
  in EQ_MP (beta_reduce lam_P_body var_P var_P) mp_result end
  (* select_ax_spec: ⊢ !x. P x ==> P (@ P)  with P : A->bool free *)
  val () = save "candle$SELECT_AX_SPEC" select_ax_spec

  (* ================================================================ *)
  (* ETA_AX: ⊢ !t:A->B. (\x. t x) = t                              *)
  (* ================================================================ *)

  val ty_B = mk_tyvar "B"
  val ty_AB = mk_fun ty_A ty_B                        (* A -> B *)
  val var_eta_t = mk_var "t" ty_AB                     (* t : A -> B *)

  val tm_tx = mk_comb var_eta_t var_x                  (* t x *)
  val lam_x_tx = mk_abs var_x tm_tx                    (* \x. t x *)
  val eq_AB = mk_const "=" (mk_fun ty_AB (mk_fun ty_AB ty_bool))
  val eta_body = mk_eq eq_AB lam_x_tx var_eta_t        (* (\x. t x) = t *)
  val lam_t_eta = mk_abs var_eta_t eta_body             (* \t. (\x. t x) = t *)

  (* ! at type A->B *)
  val ty_AB_b = mk_fun ty_AB ty_bool
  val ty_AB_b_b = mk_fun ty_AB_b ty_bool
  val const_forall_AB = mk_const "!" ty_AB_b_b

  val tm_eta_ax = mk_comb const_forall_AB lam_t_eta

  val ETA_AX_th = alloc_th()
  val () = PFTWriter.axiom out ETA_AX_th tm_eta_ax (SOME "ETA_AX")
  val () = save "candle$ETA_AX" ETA_AX_th

  (* ================================================================ *)
  (* Helpers for DISJ operations                                      *)
  (* ================================================================ *)

  (* DISJ1: from th: A ⊢ l, produce A ⊢ l ∨ q *)
  fun do_DISJ1 th l q =
    let val pth = INST DISJ1_pth [(var_p, l), (var_q, q)]
    in PROVE_HYP th pth end

  (* DISJ2: from th: A ⊢ r, produce A ⊢ l ∨ r *)
  fun do_DISJ2 l th r =
    let val pth = INST DISJ2_pth [(var_p, l), (var_q, r)]
    in PROVE_HYP th pth end

  (* DISJ_CASES: from th0: A ⊢ l∨r, th1: B∪{l} ⊢ c, th2: C∪{r} ⊢ c,
     produce A ∪ (B\{l}) ∪ (C\{r}) ⊢ c *)
  fun do_DISJ_CASES th0 l r th1 th2 c =
    let val pth = INST DISJ_CASES_pth [(var_p, l), (var_q, r), (var_r, c)]
        val th3 = PROVE_HYP th0 pth
        val l_and_c = mk_comb (mk_comb const_and l) c
        val r_and_c = mk_comb (mk_comb const_and r) c
        val th_disch_l = do_DISCH l th1 c l_and_c
        val th_disch_r = do_DISCH r th2 c r_and_c
        val th4 = PROVE_HYP th_disch_l th3
    in PROVE_HYP th_disch_r th4 end

  (* NOT_INTRO: from th: A ⊢ a ==> F, produce A ⊢ ¬a *)
  fun do_NOT_INTRO th a =
    let val pth = INST NOT_INTRO_pth [(var_p, a)]
    in PROVE_HYP th pth end

  (* CONTR: from th: A ⊢ F, produce A ⊢ c *)
  fun do_CONTR th c =
    let val pth = INST CONTR_pth [(var_p, c)]
    in PROVE_HYP th pth end

  (* ================================================================ *)
  (* 10. EXCLUDED_MIDDLE: ⊢ ∀t. t ∨ ¬t                              *)
  (* Diaconescu proof from SELECT_AX.                                 *)
  (* ================================================================ *)

  val const_select_bool = mk_const "@" (mk_fun ty_bb ty_bool)

  (* Predicates: pred_T = λs. (s=T)∨t, pred_F = λs. (s=F)∨t *)
  val var_s = mk_var "s" ty_bool
  val s_eq_T = mk_eq eq_bool var_s const_T
  val s_eq_F = mk_eq eq_bool var_s const_F
  val s_eq_T_or_t = mk_comb (mk_comb const_or s_eq_T) var_t
  val s_eq_F_or_t = mk_comb (mk_comb const_or s_eq_F) var_t
  val pred_T = mk_abs var_s s_eq_T_or_t     (* λs. (s=T) ∨ t *)
  val pred_F = mk_abs var_s s_eq_F_or_t     (* λs. (s=F) ∨ t *)

  val tm_a = mk_comb const_select_bool pred_T   (* @(λs.(s=T)∨t) *)
  val tm_b = mk_comb const_select_bool pred_F   (* @(λs.(s=F)∨t) *)

  (* a=T, b=F terms *)
  val a_eq_T = mk_eq eq_bool tm_a const_T
  val b_eq_F = mk_eq eq_bool tm_b const_F
  val a_eq_T_or_t = mk_comb (mk_comb const_or a_eq_T) var_t
  val b_eq_F_or_t = mk_comb (mk_comb const_or b_eq_F) var_t

  (* t ∨ ¬t *)
  val tm_neg_t = mk_comb const_neg var_t
  val tm_t_or_neg_t = mk_comb (mk_comb const_or var_t) tm_neg_t

  (* Step 1: ⊢ (a=T) ∨ t from SELECT_AX *)
  (* SELECT_AX at bool: ⊢ ∀P:(bool->bool). ∀x:bool. P x ==> P(@P) *)
  val sel_ax_bool = INST_TYPE SELECT_AX_th [(ty_A, ty_bool)]

  (* Variables and constants at type bool->bool for SPEC'ing SELECT_AX *)
  val var_P_bb = mk_var "P" ty_bb
  val const_forall_bb = mk_const "!" (mk_fun ty_bb_b ty_bool)

  (* Build the inner structure of SELECT_AX at type bool:
     ∀P:(bb). ∀s:bool. P s ==> P(@P) *)

  (* inner body: λs. P s ==> P(@P) *)
  val tm_P_bb_x = mk_comb var_P_bb var_s      (* P s — using s as bool var *)
  val tm_select_P_bb = mk_comb const_select_bool var_P_bb  (* @ P *)
  val tm_P_bb_select = mk_comb var_P_bb tm_select_P_bb     (* P (@ P) *)
  val tm_Ps_imp_Psel = mk_comb (mk_comb const_imp tm_P_bb_x) tm_P_bb_select
  val lam_s_inner = mk_abs var_s tm_Ps_imp_Psel
  (* λs. P s ==> P (@ P) *)
  val tm_forall_s_inner = mk_comb const_forall_bool lam_s_inner
  (* ∀s. P s ==> P (@ P) *)
  val lam_P_outer = mk_abs var_P_bb tm_forall_s_inner
  (* λP. ∀s. P s ==> P (@ P) *)

  (* Unfold outer ∀ by SPEC at type bb *)
  (* sel_ax_bool = ⊢ const_forall_bb (lam_P_outer) *)

  (* SPEC pred_T from sel_ax_bool:
     Need: ⊢ const_forall_bb (lam_P_outer) ==> lam_P_outer pred_T
     This is SPEC_pth at type bb with P := lam_P_outer, x := pred_T.

     But SPEC_pth uses type variable A. I need INST_TYPE [(A, bb)].
     Then INST [(P, lam_P_outer), (x, pred_T)]. *)

  (* Beta-reduce pred_T and pred_F at specific arguments *)
  val pred_T_at_T = mk_comb pred_T const_T
  val beta_pred_T_T = beta_reduce pred_T var_s const_T
  (* ⊢ pred_T T = (T=T) ∨ t *)
  val pred_T_at_a = mk_comb pred_T tm_a
  val beta_pred_T_a = beta_reduce pred_T var_s tm_a
  (* ⊢ pred_T a = (a=T) ∨ t *)

  (* Prove ⊢ pred_T T  via DISJ1 (REFL T) *)
  val T_eq_T = mk_eq eq_bool const_T const_T
  val th_T_eq_T_or_t = do_DISJ1 (REFL const_T) T_eq_T var_t
  val th_pred_T_at_T = EQ_MP (SYM beta_pred_T_T) th_T_eq_T_or_t

  (* Prove ⊢ pred_F F  via DISJ1 (REFL F) *)
  val pred_F_at_F = mk_comb pred_F const_F
  val beta_pred_F_F = beta_reduce pred_F var_s const_F
  val F_eq_F = mk_eq eq_bool const_F const_F
  val th_F_eq_F_or_t = do_DISJ1 (REFL const_F) F_eq_F var_t
  val th_pred_F_at_F = EQ_MP (SYM beta_pred_F_F) th_F_eq_F_or_t

  (* Beta-reduce pred_F at b *)
  val beta_pred_F_b = beta_reduce pred_F var_s tm_b

  (* SPEC chain: derive ⊢ pred_T a and ⊢ pred_F b from SELECT_AX *)
  val spec_pth_bb = INST_TYPE SPEC_pth [(ty_A, ty_bb)]
  (* ⊢ (!P:(bb->bool)) ==> P (x:bb) — with P at type bb->bool, x at bb *)
  (* After INST_TYPE, P has type (bb)->bool = bb_b and x has type bb *)
  val var_P_bb_b = mk_var "P" ty_bb_b        (* P : (bool->bool) -> bool *)
  val var_x_bb   = mk_var "x" ty_bb          (* x : bool -> bool *)
  val spec_outer_T = INST spec_pth_bb [(var_P_bb_b, lam_P_outer), (var_x_bb, pred_T)]
  (* ⊢ (! lam_P_outer) ==> lam_P_outer pred_T *)

  (* MP with sel_ax_bool *)
  val tm_sel_ax_concl = mk_comb const_forall_bb lam_P_outer
  val tm_lam_P_outer_pred_T = mk_comb lam_P_outer pred_T
  val th_spec1_pre = do_MP spec_outer_T tm_sel_ax_concl tm_lam_P_outer_pred_T
                          sel_ax_bool
  (* ⊢ lam_P_outer pred_T *)

  (* Beta-reduce: lam_P_outer pred_T = ∀s. pred_T s ==> pred_T(@pred_T) *)
  val beta_outer_T = beta_reduce lam_P_outer var_P_bb pred_T
  val th_forall_s_T = EQ_MP beta_outer_T th_spec1_pre
  (* ⊢ ∀s. pred_T s ==> pred_T (@ pred_T) *)
  (* i.e., ⊢ ∀s. pred_T s ==> pred_T a *)

  (* SPEC T (inner): need SPEC_pth at type bool *)
  val spec_pth_bool = INST_TYPE SPEC_pth [(ty_A, ty_bool)]
  (* Construct the inner predicate: λs. pred_T s ==> pred_T a *)
  val tm_pred_T_a2 = mk_comb pred_T tm_a  (* same as pred_T_at_a, memoized *)
  val tm_pred_Ts_imp_pred_Ta = mk_comb (mk_comb const_imp (mk_comb pred_T var_s))
                                        tm_pred_T_a2
  val lam_s_pred_T = mk_abs var_s tm_pred_Ts_imp_pred_Ta
  val spec_inner_T = INST spec_pth_bool [(var_P_bool, lam_s_pred_T), (var_x_bool, const_T)]
  (* ⊢ (! lam_s_pred_T) ==> lam_s_pred_T T *)
  val tm_forall_lam_s = mk_comb const_forall_bool lam_s_pred_T
  val tm_lam_s_T = mk_comb lam_s_pred_T const_T
  val th_spec2_pre = do_MP spec_inner_T tm_forall_lam_s tm_lam_s_T th_forall_s_T
  (* ⊢ lam_s_pred_T T *)

  (* Beta-reduce: lam_s_pred_T T = pred_T T ==> pred_T a *)
  val beta_inner_T = beta_reduce lam_s_pred_T var_s const_T
  val th_imp_pred_T = EQ_MP beta_inner_T th_spec2_pre
  (* ⊢ pred_T T ==> pred_T a *)

  (* MP with ⊢ pred_T T *)
  val th_pred_T_a = do_MP th_imp_pred_T pred_T_at_T tm_pred_T_a2 th_pred_T_at_T
  (* ⊢ pred_T a *)

  (* EQ_MP to unfold: ⊢ (a=T) ∨ t *)
  val th_a_eq_T_or_t = EQ_MP beta_pred_T_a th_pred_T_a

  (* Same for pred_F: ⊢ (b=F) ∨ t *)
  val spec_outer_F = INST spec_pth_bb [(var_P_bb_b, lam_P_outer), (var_x_bb, pred_F)]
  val tm_lam_P_outer_pred_F = mk_comb lam_P_outer pred_F
  val th_spec1_F_pre = do_MP spec_outer_F tm_sel_ax_concl tm_lam_P_outer_pred_F
                            sel_ax_bool
  val beta_outer_F = beta_reduce lam_P_outer var_P_bb pred_F
  val th_forall_s_F = EQ_MP beta_outer_F th_spec1_F_pre

  val tm_pred_F_b = mk_comb pred_F tm_b
  val tm_pred_Fs_imp_pred_Fb = mk_comb (mk_comb const_imp (mk_comb pred_F var_s))
                                        tm_pred_F_b
  val lam_s_pred_F = mk_abs var_s tm_pred_Fs_imp_pred_Fb
  val spec_inner_F = INST spec_pth_bool [(var_P_bool, lam_s_pred_F), (var_x_bool, const_F)]
  val tm_forall_lam_s_F = mk_comb const_forall_bool lam_s_pred_F
  val tm_lam_s_F = mk_comb lam_s_pred_F const_F
  val th_spec2_F_pre = do_MP spec_inner_F tm_forall_lam_s_F tm_lam_s_F th_forall_s_F
  val beta_inner_F = beta_reduce lam_s_pred_F var_s const_F
  val th_imp_pred_F = EQ_MP beta_inner_F th_spec2_F_pre
  val th_pred_F_b = do_MP th_imp_pred_F pred_F_at_F tm_pred_F_b th_pred_F_at_F
  val th_b_eq_F_or_t = EQ_MP beta_pred_F_b th_pred_F_b

  (* Now we have:
     th_a_eq_T_or_t: ⊢ (a=T) ∨ t
     th_b_eq_F_or_t: ⊢ (b=F) ∨ t *)

  (* --- "t" case: {t} ⊢ t ∨ ¬t --- *)
  val th_t_case = do_DISJ1 (ASSUME var_t) var_t tm_neg_t

  (* --- "a=T, b=F" case: {a=T, b=F} ⊢ t ∨ ¬t --- *)
  (* Step: {t} ⊢ pred_T = pred_F
     From {t} ⊢ (s=T)∨t and {t} ⊢ (s=F)∨t, both equal T.
     {t} ⊢ (s=T)∨t by DISJ2 *)
  val th_disj2_t = do_DISJ2 s_eq_T (ASSUME var_t) var_t
  (* {t} ⊢ (s=T) ∨ t *)
  val th_eqt_1 = eqtIntro th_disj2_t s_eq_T_or_t
  (* {t} ⊢ ((s=T) ∨ t) = T *)
  val th_disj2_t_F = do_DISJ2 s_eq_F (ASSUME var_t) var_t
  (* {t} ⊢ (s=F) ∨ t *)
  val th_eqt_2 = eqtIntro th_disj2_t_F s_eq_F_or_t
  (* {t} ⊢ ((s=F) ∨ t) = T *)
  val th_both_eq = TRANS th_eqt_1 (SYM th_eqt_2)
  (* {t} ⊢ ((s=T)∨t) = ((s=F)∨t) *)
  val th_pred_eq = ABS_thm var_s th_both_eq
  (* {t} ⊢ (λs.(s=T)∨t) = (λs.(s=F)∨t) = pred_T = pred_F *)
  val th_a_eq_b = AP_TERM const_select_bool th_pred_eq
  (* {t} ⊢ a = b *)

  (* {a=T} ⊢ a = T *)
  val th_assume_aeqT = ASSUME a_eq_T
  (* {b=F} ⊢ b = F *)
  val th_assume_beqF = ASSUME b_eq_F

  (* {t, a=T} ⊢ T = b: TRANS (SYM (a=T)) (a=b) *)
  val th_T_eq_b = TRANS (SYM th_assume_aeqT) th_a_eq_b
  (* {t, a=T, b=F} ⊢ T = F *)
  val th_T_eq_F = TRANS th_T_eq_b th_assume_beqF
  (* {t, a=T, b=F} ⊢ F *)
  val th_absurd = EQ_MP th_T_eq_F TRUTH
  (* DISCH t: {a=T, b=F} ⊢ t ==> F *)
  val tm_t_and_F = mk_comb (mk_comb const_and var_t) const_F
  val th_t_imp_F = do_DISCH var_t th_absurd const_F tm_t_and_F
  (* NOT_INTRO: {a=T, b=F} ⊢ ¬t *)
  val th_neg_t = do_NOT_INTRO th_t_imp_F var_t
  (* DISJ2: {a=T, b=F} ⊢ t ∨ ¬t *)
  val th_disj2_neg_t = do_DISJ2 var_t th_neg_t tm_neg_t

  (* Inner DISJ_CASES on (b=F) ∨ t *)
  val th_inner = do_DISJ_CASES th_b_eq_F_or_t b_eq_F var_t
                               th_disj2_neg_t th_t_case tm_t_or_neg_t
  (* {a=T} ⊢ t ∨ ¬t *)

  (* Outer DISJ_CASES on (a=T) ∨ t *)
  val th_excl_mid_t = do_DISJ_CASES th_a_eq_T_or_t a_eq_T var_t
                                     th_inner th_t_case tm_t_or_neg_t
  (* ⊢ t ∨ ¬t *)

  (* GEN t: ⊢ ∀t. t ∨ ¬t *)
  val lam_t_tor = mk_abs var_t tm_t_or_neg_t
  val lam_t_T2 = mk_abs var_t const_T
  val EXCLUDED_MIDDLE = do_GEN var_t th_excl_mid_t tm_t_or_neg_t
                              lam_t_tor lam_t_T2
  val () = save "candle$EXCLUDED_MIDDLE" EXCLUDED_MIDDLE

  (* ================================================================ *)
  (* 11. CCONTR_pth: ⊢ (¬p ==> F) ==> p                            *)
  (* From EXCLUDED_MIDDLE: SPEC p gives ⊢ p ∨ ¬p.                   *)
  (* Case p: trivial.                                                 *)
  (* Case ¬p: MP with ASSUME(¬p==>F) gives F, CONTR gives p.         *)
  (* ================================================================ *)

  (* SPEC_pth at bool with P := lam_t_tor, x := var_p *)
  val excl_mid_p = do_SPEC_bool lam_t_tor var_p EXCLUDED_MIDDLE
  (* ⊢ (λt. t ∨ ¬t) p — need beta *)
  val tm_lam_t_tor_p = mk_comb lam_t_tor var_p
  val beta_excl = beta_reduce lam_t_tor var_t var_p
  (* ⊢ (λt.t∨¬t) p = p∨¬p *)
  val tm_p_or_neg_p = mk_comb (mk_comb const_or var_p) tm_neg_p
  val th_p_or_neg_p = EQ_MP beta_excl excl_mid_p
  (* ⊢ p ∨ ¬p *)

  (* Case p: {p} ⊢ p *)
  val th_case_p = ASSUME var_p

  (* Case ¬p: {¬p, ¬p==>F} ⊢ p *)
  val tm_neg_p_imp_F = mk_comb (mk_comb const_imp tm_neg_p) const_F
  val th_assume_neg_imp_F = ASSUME tm_neg_p_imp_F   (* {¬p==>F} ⊢ ¬p==>F *)
  val th_assume_neg_p = ASSUME tm_neg_p              (* {¬p} ⊢ ¬p *)
  val th_F_from_neg = do_MP th_assume_neg_imp_F tm_neg_p const_F th_assume_neg_p
  (* {¬p, ¬p==>F} ⊢ F *)
  val th_p_from_F = do_CONTR th_F_from_neg var_p
  (* {¬p, ¬p==>F} ⊢ p *)

  (* DISJ_CASES: {¬p==>F} ⊢ p *)
  val th_ccontr_inner = do_DISJ_CASES th_p_or_neg_p var_p tm_neg_p
                                       th_case_p th_p_from_F var_p
  (* {¬p==>F} ⊢ p *)

  (* DISCH: ⊢ (¬p==>F) ==> p *)
  val tm_conj_negF_p = mk_comb (mk_comb const_and tm_neg_p_imp_F) var_p
  val CCONTR_pth = do_DISCH tm_neg_p_imp_F th_ccontr_inner var_p tm_conj_negF_p
  val () = save "candle$CCONTR" CCONTR_pth

  (* ================================================================ *)
  (* Footer                                                           *)
  (* ================================================================ *)

  val () = PFTWriter.closeOut out
    {n_ty = !next_ty, n_tm = !next_tm, n_th = !next_th, n_ci = 0}
in () end

end
