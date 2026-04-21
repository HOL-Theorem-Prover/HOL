structure PFTCandleComputePreamble :> PFTCandleComputePreamble = struct

fun emit {out, alloc_ty, alloc_tm, alloc_th, load_theorem} = let

  (* ================================================================ *)
  (* Memoized type construction                                       *)
  (* ================================================================ *)

  val tyop_memo : (string * int list * int) list ref = ref []

  fun mk_tyop name args =
    case List.find (fn (n,a,_) => n = name andalso a = args) (!tyop_memo) of
      SOME (_, _, id) => id
    | NONE =>
        let val id = alloc_ty()
        in PFTWriter.tyop out id name args;
           tyop_memo := (name, args, id) :: !tyop_memo;
           id
        end

  fun mk_tyvar name =
    case List.find (fn (n,[],_) => n = name | _ => false) (!tyop_memo) of
      SOME (_, _, id) => id
    | NONE =>
        let val id = alloc_ty()
        in PFTWriter.tyvar out id name;
           tyop_memo := (name, [], id) :: !tyop_memo;
           id
        end

  fun mk_fun a b = mk_tyop "fun" [a, b]

  (* ================================================================ *)
  (* Memoized term construction                                       *)
  (* ================================================================ *)

  val comb_memo : (int * int * int) list ref = ref []
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

  (* ================================================================ *)
  (* Theorem constructors (Candle core rules)                         *)
  (* ================================================================ *)

  fun REFL tm =
    let val id = alloc_th() in PFTWriter.Candle.refl out id tm; id end
  fun TRANS th1 th2 =
    let val id = alloc_th() in PFTWriter.Candle.trans out id th1 th2; id end
  fun MK_COMB th1 th2 =
    let val id = alloc_th() in PFTWriter.Candle.mk_comb out id th1 th2; id end
  fun ABS_THM v th =
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

  (* General beta: given lambda term, its bound var, and desired argument,
     derive ⊢ (λvar. body) arg = body[arg/var].
     When arg = var (same term ID), uses restricted BETA directly.
     Otherwise uses restricted BETA + INST. *)
  fun beta_reduce lam var arg =
    let val app = mk_comb lam var
        val th = BETA app
    in if var = arg then th
       else INST th [(var, arg)]
    end

  (* ================================================================ *)
  (* Types                                                            *)
  (* ================================================================ *)

  val ty_bool = mk_tyop "bool" []
  val ty_num  = mk_tyop "num" []
  val ty_cv   = mk_tyop "cv" []

  val ty_nn   = mk_fun ty_num ty_num           (* num -> num *)
  val ty_nnn  = mk_fun ty_num ty_nn            (* num -> num -> num *)
  val ty_nb   = mk_fun ty_num ty_bool          (* num -> bool *)
  val ty_nnb  = mk_fun ty_num ty_nb            (* num -> num -> bool *)
  val ty_bb   = mk_fun ty_bool ty_bool         (* bool -> bool *)
  val ty_bbb  = mk_fun ty_bool ty_bb           (* bool -> bool -> bool *)
  val ty_cv_cv = mk_fun ty_cv ty_cv            (* cv -> cv *)
  val ty_cv_cv_cv = mk_fun ty_cv ty_cv_cv      (* cv -> cv -> cv *)
  val ty_cv_cv_cv_cv = mk_fun ty_cv ty_cv_cv_cv (* cv -> cv -> cv -> cv *)
  val ty_num_cv = mk_fun ty_num ty_cv          (* num -> cv *)

  (* ================================================================ *)
  (* Equality constants at various types                              *)
  (* ================================================================ *)

  fun mk_eq_ty ty = mk_fun ty (mk_fun ty ty_bool)

  val eq_num  = mk_const "=" (mk_eq_ty ty_num)
  val eq_bool = mk_const "=" (mk_eq_ty ty_bool)
  val eq_nn   = mk_const "=" (mk_eq_ty ty_nn)
  val eq_cv   = mk_const "=" (mk_eq_ty ty_cv)

  fun mk_eq_tm eq_c l r = mk_comb (mk_comb eq_c l) r

  (* ================================================================ *)
  (* Standard constants                                               *)
  (* ================================================================ *)

  val const_T = mk_const "T" ty_bool
  val const_F = mk_const "F" ty_bool
  val const_zero = mk_const "_0" ty_num
  val const_SUC = mk_const "SUC" ty_nn
  val const_plus = mk_const "+" ty_nnn
  val const_minus = mk_const "-" ty_nnn
  val const_times = mk_const "*" ty_nnn
  val const_DIV = mk_const "DIV" ty_nnn
  val const_MOD = mk_const "MOD" ty_nnn
  val const_LESS = mk_const "<" ty_nnb
  val const_NUMERAL = mk_const "NUMERAL" ty_nn
  val const_BIT1 = mk_const "BIT1" ty_nn
  val const_BIT2 = mk_const "BIT2" ty_nn
  val const_COND_num = mk_const "COND" (mk_fun ty_bool (mk_fun ty_num (mk_fun ty_num ty_num)))
  val const_COND_bool = mk_const "COND" (mk_fun ty_bool ty_bbb)
  val const_COND_cv = mk_const "COND" (mk_fun ty_bool (mk_fun ty_cv ty_cv_cv))
  val const_LET_cv = mk_const "LET" (mk_fun (mk_fun ty_cv ty_cv) ty_cv_cv)

  (* cv constants - use Candle names per the name map *)
  val const_Num = mk_const "Cexp_num" ty_num_cv
  val const_Pair = mk_const "Cexp_pair" ty_cv_cv_cv
  val const_cv_add = mk_const "Cexp_add" ty_cv_cv_cv
  val const_cv_sub = mk_const "Cexp_sub" ty_cv_cv_cv
  val const_cv_mul = mk_const "Cexp_mul" ty_cv_cv_cv
  val const_cv_div = mk_const "Cexp_div" ty_cv_cv_cv
  val const_cv_mod = mk_const "Cexp_mod" ty_cv_cv_cv
  val const_cv_lt = mk_const "Cexp_less" ty_cv_cv_cv
  val const_cv_if = mk_const "Cexp_if" ty_cv_cv_cv_cv
  val const_cv_fst = mk_const "Cexp_fst" ty_cv_cv
  val const_cv_snd = mk_const "Cexp_snd" ty_cv_cv
  val const_cv_ispair = mk_const "Cexp_ispair" ty_cv_cv
  val const_cv_eq = mk_const "Cexp_eq" ty_cv_cv_cv

  (* ================================================================ *)
  (* Standard variables                                               *)
  (* ================================================================ *)

  val var_m = mk_var "m" ty_num
  val var_n = mk_var "n" ty_num
  val var_t = mk_var "t" ty_bool
  val var_p = mk_var "p" ty_bool   (* for bool conjuncts *)
  val var_q = mk_var "q" ty_bool

  val var_p_cv = mk_var "p" ty_cv
  val var_q_cv = mk_var "q" ty_cv
  val var_r_cv = mk_var "r" ty_cv
  val var_s_cv = mk_var "s" ty_cv
  val var_p1 = mk_var "p1" ty_cv
  val var_q1 = mk_var "q1" ty_cv
  val var_p2 = mk_var "p2" ty_cv
  val var_q2 = mk_var "q2" ty_cv
  val var_f_cv = mk_var "f" (mk_fun ty_cv ty_cv)

  (* ================================================================ *)
  (* Helper term builders                                             *)
  (* ================================================================ *)

  fun mk_SUC n = mk_comb const_SUC n
  fun mk_plus m n = mk_comb (mk_comb const_plus m) n
  fun mk_minus m n = mk_comb (mk_comb const_minus m) n
  fun mk_times m n = mk_comb (mk_comb const_times m) n
  fun mk_DIV m n = mk_comb (mk_comb const_DIV m) n
  fun mk_MOD m n = mk_comb (mk_comb const_MOD m) n
  fun mk_LESS m n = mk_comb (mk_comb const_LESS m) n
  fun mk_NUMERAL n = mk_comb const_NUMERAL n
  fun mk_Num n = mk_comb const_Num n
  fun mk_Pair p q = mk_comb (mk_comb const_Pair p) q
  fun mk_COND_num b t e = mk_comb (mk_comb (mk_comb const_COND_num b) t) e
  fun mk_COND_bool b t e = mk_comb (mk_comb (mk_comb const_COND_bool b) t) e

  (* ================================================================ *)
  (* CONJUNCT helpers from the main preamble                          *)
  (* ================================================================ *)

  val CONJUNCT1_pth = load_theorem "candle$CONJUNCT1"
  val CONJUNCT2_pth = load_theorem "candle$CONJUNCT2"

  (* Extract first conjunct: from th: ⊢ a ∧ b, get ⊢ a *)
  fun do_CONJUNCT1 th a b =
    let val pth = INST CONJUNCT1_pth [(var_p, a), (var_q, b)]
    in PROVE_HYP th pth end

  (* Extract second conjunct: from th: ⊢ a ∧ b, get ⊢ b *)
  fun do_CONJUNCT2 th a b =
    let val pth = INST CONJUNCT2_pth [(var_p, a), (var_q, b)]
    in PROVE_HYP th pth end

  (* ================================================================ *)
  (* EQT_INTRO helper                                                 *)
  (* ================================================================ *)

  val EQT_INTRO_pth = load_theorem "candle$EQT_INTRO"
  (* EQT_INTRO_pth: ⊢ t = (t = T) *)

  (* From ⊢ P, derive ⊢ P = T *)
  fun do_EQT_INTRO th tm_P =
    let val pth = INST EQT_INTRO_pth [(var_t, tm_P)]
        (* pth: ⊢ P = (P = T) *)
    in EQ_MP pth th end

  (* ================================================================ *)
  (* 1. Define BIT0                                                   *)
  (*    BIT0 = λn. n + n                                              *)
  (* ================================================================ *)

  val bit0_body = mk_plus var_n var_n           (* n + n *)
  val bit0_rhs = mk_abs var_n bit0_body         (* λn. n + n *)

  val var_BIT0 = mk_var "BIT0" ty_nn
  val bit0_def_tm = mk_eq_tm eq_nn var_BIT0 bit0_rhs   (* BIT0 = λn. n + n *)

  val () = PFTWriter.new_const out "BIT0" ty_nn
  val const_BIT0 = mk_const "BIT0" ty_nn

  val BIT0_DEF = NEW_SPEC (ASSUME bit0_def_tm) ["BIT0"]
  (* BIT0_DEF: ⊢ BIT0 = λn. n + n *)
  val () = save "candle$BIT0_DEF" BIT0_DEF

  (* Derive: ⊢ BIT0 n = n + n *)
  val bit0_unfold =
    let val th1 = AP_THM BIT0_DEF var_n           (* ⊢ BIT0 n = (λn. n+n) n *)
        val th2 = beta_reduce bit0_rhs var_n var_n (* ⊢ (λn. n+n) n = n+n *)
    in TRANS th1 th2 end
  val () = save "candle$BIT0" bit0_unfold

  (* ================================================================ *)
  (* 2. Prove BIT1 in Candle form                                     *)
  (*    ⊢ BIT1 n = SUC (n + n)                                       *)
  (*                                                                  *)
  (*    HOL4's BIT1: BIT1 n = n + (n + SUC 0)                        *)
  (*    Need: n + (n + SUC 0) = SUC (n + n)                          *)
  (*                                                                  *)
  (*    Using:                                                        *)
  (*      ADD_SUC: ⊢ m + SUC n = SUC (m + n)                        *)
  (*      ADD_0:   ⊢ m + 0 = m                                       *)
  (* ================================================================ *)

  (* LOAD HOL4's BIT1 equation: ⊢ BIT1 n = n + (n + SUC 0) *)
  val hol4_BIT1 = load_theorem "arithmetic$BIT1"

  (* LOAD arithmetic equations *)
  val ADD_SUC = load_theorem "arithmetic$ADD_SUC"   (* ⊢ m + SUC n = SUC (m + n) *)
  val ADD_0 = load_theorem "arithmetic$ADD_0"       (* ⊢ m + 0 = m *)

  (* Instantiate ADD_SUC: m := n, n := 0 gives ⊢ n + SUC 0 = SUC (n + 0) *)
  val tm_SUC_0 = mk_SUC const_zero                  (* SUC 0 *)
  val ADD_SUC_inst = INST ADD_SUC [(var_m, var_n), (var_n, const_zero)]
  (* ⊢ n + SUC 0 = SUC (n + 0) *)

  (* Instantiate ADD_0: m := n gives ⊢ n + 0 = n *)
  val ADD_0_inst = INST ADD_0 [(var_m, var_n)]
  (* ⊢ n + 0 = n *)

  (* Build: ⊢ SUC (n + 0) = SUC n *)
  val SUC_n_plus_0_eq = AP_TERM const_SUC ADD_0_inst
  (* ⊢ SUC (n + 0) = SUC n *)

  (* Chain: n + SUC 0 = SUC (n + 0) = SUC n *)
  val n_plus_SUC_0_eq_SUC_n = TRANS ADD_SUC_inst SUC_n_plus_0_eq
  (* ⊢ n + SUC 0 = SUC n *)

  (* Now derive: n + (n + SUC 0) = n + SUC n = SUC (n + n)
     Using ADD_SUC again: m := n, n := n gives ⊢ n + SUC n = SUC (n + n) *)
  val tm_SUC_n = mk_SUC var_n

  val ADD_SUC_nn = INST ADD_SUC [(var_m, var_n), (var_n, var_n)]
  (* ⊢ n + SUC n = SUC (n + n) *)

  (* Build: ⊢ n + (n + SUC 0) = n + SUC n *)
  val step1 = AP_TERM (mk_comb const_plus var_n) n_plus_SUC_0_eq_SUC_n
  (* ⊢ n + (n + SUC 0) = n + SUC n *)

  (* Chain: n + (n + SUC 0) = n + SUC n = SUC (n + n) *)
  val rhs_eq = TRANS step1 ADD_SUC_nn
  (* ⊢ n + (n + SUC 0) = SUC (n + n) *)

  (* Now combine with BIT1 definition: BIT1 n = n + (n + SUC 0) = SUC (n + n) *)
  val BIT1_candle = TRANS hol4_BIT1 rhs_eq
  (* ⊢ BIT1 n = SUC (n + n) *)
  val () = save "candle$BIT1" BIT1_candle

  (* ================================================================ *)
  (* 3. Derive LESS equations in structural form                      *)
  (*    Candle needs:                                                 *)
  (*      ⊢ m < 0 = F                                                *)
  (*      ⊢ 0 < SUC n = T                                            *)
  (*      ⊢ SUC m < SUC n = (m < n)                                  *)
  (* ================================================================ *)

  (* LOAD from cv theory *)
  val LT_RECURSIVE = load_theorem "cv$LT_RECURSIVE"
  (* LT_RECURSIVE: ⊢ (m < 0 = F) ∧ (m < SUC n = (if m = n then T else m < n)) *)

  (* Build terms for the conjuncts *)
  val tm_m_lt_0 = mk_LESS var_m const_zero
  val tm_m_lt_0_eq_F = mk_eq_tm eq_bool tm_m_lt_0 const_F
  val tm_m_lt_SUC_n = mk_LESS var_m tm_SUC_n
  val tm_m_eq_n = mk_eq_tm eq_num var_m var_n
  val tm_m_lt_n = mk_LESS var_m var_n
  val tm_cond_lt = mk_COND_bool tm_m_eq_n const_T tm_m_lt_n
  val tm_m_lt_SUC_n_eq = mk_eq_tm eq_bool tm_m_lt_SUC_n tm_cond_lt

  (* LESS_eq1: ⊢ m < 0 = F *)
  val LESS_eq1 = do_CONJUNCT1 LT_RECURSIVE tm_m_lt_0_eq_F tm_m_lt_SUC_n_eq
  val () = save "candle$LESS_1" LESS_eq1

  (* For LESS_eq2 and LESS_eq3, use prim_rec theorems directly *)
  val LESS_0 = load_theorem "prim_rec$LESS_0"
  (* LESS_0: ⊢ 0 < SUC n *)

  val LESS_MONO_EQ = load_theorem "prim_rec$LESS_MONO_EQ"
  (* LESS_MONO_EQ: ⊢ SUC m < SUC n ⇔ m < n *)

  (* LESS_eq2: ⊢ 0 < SUC n = T *)
  val tm_0_lt_SUC_n = mk_LESS const_zero tm_SUC_n
  val LESS_eq2 = do_EQT_INTRO LESS_0 tm_0_lt_SUC_n
  val () = save "candle$LESS_2" LESS_eq2

  (* LESS_eq3: ⊢ SUC m < SUC n = (m < n) *)
  val LESS_eq3 = LESS_MONO_EQ
  val () = save "candle$LESS_3" LESS_eq3

  (* ================================================================ *)
  (* 4. Assemble the 62 characteristic equations                      *)
  (*                                                                  *)
  (* Most equations are LOADed from replayed theories.                *)
  (* For now, we save what we have and mark the rest as TODO.         *)
  (* ================================================================ *)

  (* Equation 5: NUMERAL n = n *)
  val eq5 = load_theorem "arithmetic$NUMERAL_DEF"
  val () = save "candle$COMPUTE_EQ_5" eq5

  (* Equation 6: BIT0 n = n + n *)
  val () = save "candle$COMPUTE_EQ_6" bit0_unfold

  (* Equation 7: BIT1 n = SUC (n + n) *)
  val () = save "candle$COMPUTE_EQ_7" BIT1_candle

  (* Equations 17-19: LESS *)
  val () = save "candle$COMPUTE_EQ_17" LESS_eq1
  val () = save "candle$COMPUTE_EQ_18" LESS_eq2
  val () = save "candle$COMPUTE_EQ_19" LESS_eq3

  (* TODO: Complete remaining equations 1-4, 8-16, 20-62 *)
  (* These require:
     - COND equations (1-4)
     - ADD equations (8-9)
     - SUB equations (10-12)
     - MUL equations (13-14)
     - DIV/MOD equations (15-16)
     - num equality equations (20-23)
     - cv operation equations (24-62)
  *)

in () end

end (* struct *)
