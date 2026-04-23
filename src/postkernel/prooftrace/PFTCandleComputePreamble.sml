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
  val ty_cv   = mk_tyop "Cexp" []
  val ty_A    = mk_tyvar "'a"

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

  (* Polymorphic types *)
  val ty_AA   = mk_fun ty_A ty_A
  val ty_AAA  = mk_fun ty_A ty_AA
  val ty_bAAA = mk_fun ty_bool ty_AAA

  (* ================================================================ *)
  (* Equality constants at various types                              *)
  (* ================================================================ *)

  fun mk_eq_ty ty = mk_fun ty (mk_fun ty ty_bool)

  val eq_num  = mk_const "=" (mk_eq_ty ty_num)
  val eq_bool = mk_const "=" (mk_eq_ty ty_bool)
  val eq_nn   = mk_const "=" (mk_eq_ty ty_nn)
  val eq_cv   = mk_const "=" (mk_eq_ty ty_cv)
  val eq_A    = mk_const "=" (mk_eq_ty ty_A)

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

  (* COND at various types *)
  val const_COND_num = mk_const "COND" (mk_fun ty_bool (mk_fun ty_num (mk_fun ty_num ty_num)))
  val const_COND_bool = mk_const "COND" (mk_fun ty_bool ty_bbb)
  val const_COND_cv = mk_const "COND" (mk_fun ty_bool (mk_fun ty_cv ty_cv_cv))
  val const_COND_A = mk_const "COND" ty_bAAA

  (* LET at cv type *)
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

  (* Polymorphic variables *)
  val var_a = mk_var "a" ty_A
  val var_b = mk_var "b" ty_A
  val var_x = mk_var "x" ty_bool
  val var_y = mk_var "y" ty_bool

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
  fun mk_COND_cv b t e = mk_comb (mk_comb (mk_comb const_COND_cv b) t) e

  (* Commonly used terms *)
  val tm_SUC_n = mk_SUC var_n
  val tm_SUC_m = mk_SUC var_m
  val tm_zero = mk_NUMERAL const_zero   (* NUMERAL _0 *)

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
  (* EQT_INTRO / EQF_INTRO helpers                                    *)
  (* ================================================================ *)

  val EQT_INTRO_pth = load_theorem "candle$EQT_INTRO"
  (* EQT_INTRO_pth: ⊢ t = (t = T) *)

  (* From ⊢ P, derive ⊢ P = T *)
  fun do_EQT_INTRO th tm_P =
    let val pth = INST EQT_INTRO_pth [(var_t, tm_P)]
    in EQ_MP pth th end

  val SPEC_pth = load_theorem "candle$SPEC"
  (* SPEC_pth: ⊢ !(P:'a→bool) ⇒ P x *)

  val MP_pth = load_theorem "candle$MP"
  (* MP_pth: {p:bool} ⊢ (p ⇒ q) = q *)

  (* do_MP: from ith: ⊢ a ⇒ b and ant_th: ⊢ a, derive ⊢ b.
     Uses candle$MP: {p} ⊢ (p ⇒ q) = q.
     1. INST MP_pth [(p,a),(q,b)] gives {a} ⊢ (a ⇒ b) = b
     2. DEDUCT_ANTISYM ant_th rth gives ⊢ a = ((a ⇒ b) = b)
     3. EQ_MP with ant_th gives ⊢ (a ⇒ b) = b
     4. EQ_MP with ith gives ⊢ b *)
  fun do_MP ith a_tm b_tm ant_th =
    let val rth = INST MP_pth [(var_p, a_tm), (var_q, b_tm)]
        val da = DEDUCT_ANTISYM ant_th rth
        val eq_imp = EQ_MP da ant_th
    in EQ_MP eq_imp ith end

  (* do_SPEC: strip one ∀-quantifier from a theorem.
     Given th: ⊢ !(λv. body) where v has type v_ty,
     pred = (λv. body), and t: a term of type v_ty,
     derive ⊢ body[t/v].
     Uses candle$SPEC: ⊢ !(P:'a→bool) ⇒ P x.
     1. INST_TYPE + INST SPEC_pth to get ⊢ !(pred) ⇒ pred t
     2. do_MP with th gives ⊢ (λv. body) t
     3. beta_reduce + EQ_MP gives ⊢ body[t/v] *)
  fun do_SPEC pred t v v_ty th =
    let val Ab = mk_fun v_ty ty_bool
        val var_P = mk_var "P" Ab
        val var_x = mk_var "x" v_ty
        val spec_inst = INST (INST_TYPE SPEC_pth [(ty_A, v_ty)])
                            [(var_P, pred), (var_x, t)]
        val const_forall = mk_const "!" (mk_fun Ab ty_bool)
        val forall_tm = mk_comb const_forall pred
        val pred_t = mk_comb pred t
        val mp_result = do_MP spec_inst forall_tm pred_t th
        val beta_th = beta_reduce pred v t
    in EQ_MP beta_th mp_result end

  (* ================================================================ *)
  (* 1. Define BIT0                                                   *)
  (*    BIT0 = λn. n + n                                              *)
  (* ================================================================ *)

  val bit0_body = mk_plus var_n var_n           (* n + n *)
  val bit0_rhs = mk_abs var_n bit0_body         (* λn. n + n *)

  val var_BIT0 = mk_var "BIT0" ty_nn
  val bit0_def_tm = mk_eq_tm eq_nn var_BIT0 bit0_rhs   (* BIT0 = λn. n + n *)

  (* new_specification creates the constant BIT0 and returns ⊢ BIT0 = λn. n + n *)
  val BIT0_DEF = NEW_SPEC (ASSUME bit0_def_tm) ["BIT0"]

  (* Now we can reference the constant BIT0 *)
  val const_BIT0 = mk_const "BIT0" ty_nn
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
  (* ================================================================ *)

  val hol4_BIT1 = load_theorem "arithmetic$BIT1"
  val ADD_SUC = load_theorem "arithmetic$ADD_SUC"
  val ADD_0 = load_theorem "arithmetic$ADD_0"

  val tm_SUC_0 = mk_SUC tm_zero       (* SUC (NUMERAL _0) = 1 *)
  val tm_SUC_bare0 = mk_SUC const_zero  (* SUC _0 = bare 1, for ADD_0 SPEC *)

  (* hol4_BIT1: ⊢ !n. BIT1 n = n + (n + SUC _0)  — strip the ∀n *)
  val bit1_pred = mk_abs var_n
    (mk_eq_tm eq_num (mk_comb const_BIT1 var_n)
                    (mk_plus var_n (mk_plus var_n tm_SUC_bare0)))
  val BIT1_free = do_SPEC bit1_pred var_n var_n ty_num hol4_BIT1

  (* ADD_0: ⊢ !m. m + _0 = m — strip ∀m by specializing with n *)
  val add0_pred = mk_abs var_m (mk_eq_tm eq_num (mk_plus var_m const_zero) var_m)
  val ADD_0_free = do_SPEC add0_pred var_n var_m ty_num ADD_0

  val ADD_SUC_inst = INST ADD_SUC [(var_m, var_n), (var_n, const_zero)]
  val SUC_n_plus_0_eq = AP_TERM const_SUC ADD_0_free
  val n_plus_SUC_0_eq_SUC_n = TRANS ADD_SUC_inst SUC_n_plus_0_eq
  val ADD_SUC_nn = INST ADD_SUC [(var_m, var_n), (var_n, var_n)]
  val step1 = AP_TERM (mk_comb const_plus var_n) n_plus_SUC_0_eq_SUC_n
  val rhs_eq = TRANS step1 ADD_SUC_nn
  val BIT1_candle = TRANS BIT1_free rhs_eq
  val () = save "candle$BIT1" BIT1_candle

  (* ================================================================ *)
  (* 3. Derive LESS equations                                         *)
  (* ================================================================ *)

  val LT_RECURSIVE = load_theorem "cv$LT_RECURSIVE"
  val tm_m_lt_0 = mk_LESS var_m tm_zero
  val tm_m_lt_0_eq_F = mk_eq_tm eq_bool tm_m_lt_0 const_F
  val tm_m_lt_SUC_n = mk_LESS var_m tm_SUC_n
  val tm_m_eq_n = mk_eq_tm eq_num var_m var_n
  val tm_m_lt_n = mk_LESS var_m var_n
  val tm_cond_lt = mk_COND_bool tm_m_eq_n const_T tm_m_lt_n
  val tm_m_lt_SUC_n_eq = mk_eq_tm eq_bool tm_m_lt_SUC_n tm_cond_lt

  val LESS_eq1 = do_CONJUNCT1 LT_RECURSIVE tm_m_lt_0_eq_F tm_m_lt_SUC_n_eq
  val () = save "candle$LESS_1" LESS_eq1

  val LESS_0 = load_theorem "prim_rec$LESS_0"
  val LESS_MONO_EQ = load_theorem "prim_rec$LESS_MONO_EQ"

  val tm_0_lt_SUC_n = mk_LESS tm_zero tm_SUC_n
  val LESS_eq2 = do_EQT_INTRO LESS_0 tm_0_lt_SUC_n
  val () = save "candle$LESS_2" LESS_eq2

  val LESS_eq3 = LESS_MONO_EQ
  val () = save "candle$LESS_3" LESS_eq3

  (* ================================================================ *)
  (* 4. Assemble the 62 characteristic equations                      *)
  (* ================================================================ *)

  (* --- Equations 1-4: COND --- *)
  (* COND_CLAUSES: ⊢ ∀t1 t2. (COND T t1 t2 = t1) ∧ (COND F t1 t2 = t2) *)
  val COND_CLAUSES = load_theorem "bool$COND_CLAUSES"

  (* COND_CLAUSES uses variables named t1 and t2 *)
  val var_t1_num = mk_var "t1" ty_num
  val var_t2_num = mk_var "t2" ty_num
  val var_t1_bool = mk_var "t1" ty_bool
  val var_t2_bool = mk_var "t2" ty_bool

  (* Instantiate at num type for equations 1-2 *)
  val COND_CLAUSES_num = INST_TYPE COND_CLAUSES [(ty_A, ty_num)]
  val COND_CLAUSES_num_inst = INST COND_CLAUSES_num [(var_t1_num, var_m), (var_t2_num, var_n)]

  (* Build term for conjunct extraction *)
  val tm_COND_T_m_n = mk_comb (mk_comb (mk_comb const_COND_num const_T) var_m) var_n
  val tm_COND_F_m_n = mk_comb (mk_comb (mk_comb const_COND_num const_F) var_m) var_n
  val tm_eq1 = mk_eq_tm eq_num tm_COND_T_m_n var_m
  val tm_eq2 = mk_eq_tm eq_num tm_COND_F_m_n var_n

  val eq1 = do_CONJUNCT1 COND_CLAUSES_num_inst tm_eq1 tm_eq2
  val eq2 = do_CONJUNCT2 COND_CLAUSES_num_inst tm_eq1 tm_eq2
  val () = save "candle$COMPUTE_EQ_1" eq1
  val () = save "candle$COMPUTE_EQ_2" eq2

  (* Instantiate at bool type for equations 3-4 (IF = COND on bool) *)
  val COND_CLAUSES_bool = INST_TYPE COND_CLAUSES [(ty_A, ty_bool)]
  val COND_CLAUSES_bool_inst = INST COND_CLAUSES_bool [(var_t1_bool, var_x), (var_t2_bool, var_y)]

  val tm_IF_T_x_y = mk_comb (mk_comb (mk_comb const_COND_bool const_T) var_x) var_y
  val tm_IF_F_x_y = mk_comb (mk_comb (mk_comb const_COND_bool const_F) var_x) var_y
  val tm_eq3 = mk_eq_tm eq_bool tm_IF_T_x_y var_x
  val tm_eq4 = mk_eq_tm eq_bool tm_IF_F_x_y var_y

  val eq3 = do_CONJUNCT1 COND_CLAUSES_bool_inst tm_eq3 tm_eq4
  val eq4 = do_CONJUNCT2 COND_CLAUSES_bool_inst tm_eq3 tm_eq4
  val () = save "candle$COMPUTE_EQ_3" eq3
  val () = save "candle$COMPUTE_EQ_4" eq4

  (* --- Equation 5: NUMERAL n = n --- *)
  val eq5 = load_theorem "arithmetic$NUMERAL_DEF"
  val () = save "candle$COMPUTE_EQ_5" eq5

  (* --- Equation 6: BIT0 n = n + n --- *)
  val () = save "candle$COMPUTE_EQ_6" bit0_unfold

  (* --- Equation 7: BIT1 n = SUC (n + n) --- *)
  val () = save "candle$COMPUTE_EQ_7" BIT1_candle

  (* --- Equations 8-9: ADD --- *)
  (* ADD: ⊢ (0 + n = n) ∧ (SUC m + n = SUC (m + n)) *)
  val ADD = load_theorem "arithmetic$ADD"

  (* Note: HOL4's ADD uses NUMERAL _0, not bare _0 *)
  val tm_0_plus_n = mk_plus tm_zero var_n
  val tm_eq8 = mk_eq_tm eq_num tm_0_plus_n var_n
  val tm_SUC_m_plus_n = mk_plus tm_SUC_m var_n
  val tm_m_plus_n = mk_plus var_m var_n
  val tm_SUC_m_plus_n_rhs = mk_SUC tm_m_plus_n
  val tm_eq9 = mk_eq_tm eq_num tm_SUC_m_plus_n tm_SUC_m_plus_n_rhs

  val eq8 = do_CONJUNCT1 ADD tm_eq8 tm_eq9
  val eq9 = do_CONJUNCT2 ADD tm_eq8 tm_eq9
  val () = save "candle$COMPUTE_EQ_8" eq8
  val () = save "candle$COMPUTE_EQ_9" eq9

  (* --- Equations 10-12: SUB --- *)
  (* Candle needs:
       10: 0 - n = 0
       11: m - 0 = m
       12: SUC m - SUC n = m - n
     SUB_0: ⊢ (0 - m = 0) ∧ (m - 0 = m) *)
  val SUB_0 = load_theorem "arithmetic$SUB_0"

  val tm_0_minus_m = mk_minus tm_zero var_m
  val tm_eq10a = mk_eq_tm eq_num tm_0_minus_m tm_zero
  val tm_m_minus_0 = mk_minus var_m tm_zero
  val tm_eq11a = mk_eq_tm eq_num tm_m_minus_0 var_m

  val eq10_m = do_CONJUNCT1 SUB_0 tm_eq10a tm_eq11a
  val eq10 = INST eq10_m [(var_m, var_n)]  (* rename m to n *)
  val () = save "candle$COMPUTE_EQ_10" eq10

  val eq11 = do_CONJUNCT2 SUB_0 tm_eq10a tm_eq11a
  val () = save "candle$COMPUTE_EQ_11" eq11

  val SUB_MONO_EQ = load_theorem "arithmetic$SUB_MONO_EQ"
  (* SUB_MONO_EQ: ⊢ SUC n - SUC m = n - m, need to swap n/m *)
  val eq12 = INST SUB_MONO_EQ [(var_n, var_m), (var_m, var_n)]
  val () = save "candle$COMPUTE_EQ_12" eq12

  (* --- Equations 13-14: MUL --- *)
  (* MULT: ⊢ (0 * n = 0) ∧ (SUC m * n = (m * n) + n)
     Candle needs: (SUC m) * n = n + (m * n)  [operands swapped]
     We extract from MULT, then use ADD_COMM to swap. *)
  val MULT = load_theorem "arithmetic$MULT"
  val ADD_COMM = load_theorem "arithmetic$ADD_COMM"

  val tm_0_times_n = mk_times tm_zero var_n
  val tm_eq13 = mk_eq_tm eq_num tm_0_times_n tm_zero
  val tm_SUC_m_times_n = mk_times tm_SUC_m var_n
  val tm_m_times_n = mk_times var_m var_n
  val tm_m_times_n_plus_n = mk_plus tm_m_times_n var_n
  val tm_eq14_hol4 = mk_eq_tm eq_num tm_SUC_m_times_n tm_m_times_n_plus_n

  val eq13 = do_CONJUNCT1 MULT tm_eq13 tm_eq14_hol4

  (* Extract HOL4 form: SUC m * n = (m * n) + n *)
  val eq14_hol4 = do_CONJUNCT2 MULT tm_eq13 tm_eq14_hol4

  (* ADD_COMM: ⊢ m + n = n + m. Instantiate with m := (m * n), n := n *)
  val var_m_add = mk_var "m" ty_num  (* ADD_COMM uses m and n *)
  val var_n_add = mk_var "n" ty_num
  val ADD_COMM_inst = INST ADD_COMM [(var_m_add, tm_m_times_n), (var_n_add, var_n)]
  (* ⊢ (m * n) + n = n + (m * n) *)

  (* TRANS: SUC m * n = (m * n) + n = n + (m * n) *)
  val eq14 = TRANS eq14_hol4 ADD_COMM_inst
  val () = save "candle$COMPUTE_EQ_13" eq13
  val () = save "candle$COMPUTE_EQ_14" eq14

  (* --- Equations 15-16: DIV, MOD --- *)
  val eq15 = load_theorem "cv$DIV_RECURSIVE"
  val eq16 = load_theorem "cv$MOD_RECURSIVE"
  val () = save "candle$COMPUTE_EQ_15" eq15
  val () = save "candle$COMPUTE_EQ_16" eq16

  (* --- Equations 17-19: LESS --- *)
  val () = save "candle$COMPUTE_EQ_17" LESS_eq1
  val () = save "candle$COMPUTE_EQ_18" LESS_eq2
  val () = save "candle$COMPUTE_EQ_19" LESS_eq3

  (* --- Equations 20-23: num equality --- *)
  (* Need:
       20: (0 = 0) = T
       21: (0 = SUC n) = F
       22: (SUC m = 0) = F
       23: (SUC m = SUC n) = (m = n)
     From cv$SUC_EQ we get 22 and 23. Need to derive 20 and 21. *)

  (* Equation 20: (0 = 0) = T *)
  val tm_0_eq_0 = mk_eq_tm eq_num tm_zero tm_zero
  val REFL_0 = REFL tm_zero
  val eq20 = do_EQT_INTRO REFL_0 tm_0_eq_0
  val () = save "candle$COMPUTE_EQ_20" eq20

  (* SUC_EQ: ⊢ (SUC m = 0 = F) ∧ (SUC m = SUC n = (m = n)) *)
  val SUC_EQ = load_theorem "cv$SUC_EQ"

  val tm_SUC_m_eq_0 = mk_eq_tm eq_num tm_SUC_m tm_zero
  val tm_eq22 = mk_eq_tm eq_bool tm_SUC_m_eq_0 const_F
  val tm_SUC_m_eq_SUC_n = mk_eq_tm eq_num tm_SUC_m tm_SUC_n
  val tm_m_eq_n = mk_eq_tm eq_num var_m var_n
  val tm_eq23 = mk_eq_tm eq_bool tm_SUC_m_eq_SUC_n tm_m_eq_n

  val eq22 = do_CONJUNCT1 SUC_EQ tm_eq22 tm_eq23
  val eq23 = do_CONJUNCT2 SUC_EQ tm_eq22 tm_eq23
  val () = save "candle$COMPUTE_EQ_22" eq22
  val () = save "candle$COMPUTE_EQ_23" eq23

  (* Equation 21: (0 = SUC n) = F *)
  (* From eq22 (SUC m = 0 = F), we need (0 = SUC n) = F.
     Use the fact that (a = b) = (b = a). Specifically:
       1. eq22 with m := n gives: (SUC n = 0) = F
       2. We need a theorem that (0 = SUC n) = (SUC n = 0)
       3. Then TRANS gives (0 = SUC n) = F
     The symmetry of equality: (a = b) = (b = a) follows from
     DEDUCT_ANTISYM_RULE on ASSUME (a = b) with SYM.
     For now, use a simpler approach: derive from NOT_SUC *)

  (* NOT_SUC: ⊢ ¬(SUC n = 0), i.e., (SUC n = 0) ==> F *)
  (* To get (0 = SUC n) = F, we use:
     1. REFL gives ⊢ 0 = 0
     2. If 0 = SUC n, then SUC n = 0 by SYM, contradiction with NOT_SUC
     3. So (0 = SUC n) = F *)
  (* Actually, just derive eq21 from eq22 using equality symmetry *)
  val eq22_inst_n = INST eq22 [(var_m, var_n)]  (* ⊢ (SUC n = 0) = F *)

  (* Build: ⊢ (0 = SUC n) = (SUC n = 0) using DEDUCT_ANTISYM *)
  val tm_0_eq_SUC_n = mk_eq_tm eq_num tm_zero tm_SUC_n
  val tm_SUC_n_eq_0 = mk_eq_tm eq_num tm_SUC_n tm_zero
  val assum1 = ASSUME tm_0_eq_SUC_n        (* {0 = SUC n} ⊢ 0 = SUC n *)
  val sym1 = SYM assum1                     (* {0 = SUC n} ⊢ SUC n = 0 *)
  val assum2 = ASSUME tm_SUC_n_eq_0        (* {SUC n = 0} ⊢ SUC n = 0 *)
  val sym2 = SYM assum2                     (* {SUC n = 0} ⊢ 0 = SUC n *)
  val eq_sym = DEDUCT_ANTISYM sym2 sym1    (* ⊢ (0 = SUC n) = (SUC n = 0) *)

  val eq21 = TRANS eq_sym eq22_inst_n      (* ⊢ (0 = SUC n) = F *)
  val () = save "candle$COMPUTE_EQ_21" eq21

  (* --- Equations 24-62: cv operations --- *)

  (* Helper to extract conjuncts from right-associated conjunction
     a ∧ (b ∧ (c ∧ d)) structure.
     extract4 th [tm1, tm2, tm3, tm4] returns [th1, th2, th3, th4]
     where th is ⊢ tm1 ∧ (tm2 ∧ (tm3 ∧ tm4)) *)
  fun extract4 th [tm1, tm2, tm3, tm4] =
    let
      val tm234 = mk_comb (mk_comb (mk_const "/\\" ty_bbb) tm2)
                    (mk_comb (mk_comb (mk_const "/\\" ty_bbb) tm3) tm4)
      val th1 = do_CONJUNCT1 th tm1 tm234
      val th234 = do_CONJUNCT2 th tm1 tm234
      val tm34 = mk_comb (mk_comb (mk_const "/\\" ty_bbb) tm3) tm4
      val th2 = do_CONJUNCT1 th234 tm2 tm34
      val th34 = do_CONJUNCT2 th234 tm2 tm34
      val th3 = do_CONJUNCT1 th34 tm3 tm4
      val th4 = do_CONJUNCT2 th34 tm3 tm4
    in [th1, th2, th3, th4] end
    | extract4 _ _ = raise Fail "extract4: expected 4 terms"

  (* Helper for 3-way conjunction *)
  fun extract3 th [tm1, tm2, tm3] =
    let
      val tm23 = mk_comb (mk_comb (mk_const "/\\" ty_bbb) tm2) tm3
      val th1 = do_CONJUNCT1 th tm1 tm23
      val th23 = do_CONJUNCT2 th tm1 tm23
      val th2 = do_CONJUNCT1 th23 tm2 tm3
      val th3 = do_CONJUNCT2 th23 tm2 tm3
    in [th1, th2, th3] end
    | extract3 _ _ = raise Fail "extract3: expected 3 terms"

  (* Helper for 2-way conjunction *)
  fun extract2 th [tm1, tm2] = [do_CONJUNCT1 th tm1 tm2, do_CONJUNCT2 th tm1 tm2]
    | extract2 _ _ = raise Fail "extract2: expected 2 terms"

  (* Common cv terms *)
  val tm_Num_m = mk_Num var_m
  val tm_Num_n = mk_Num var_n
  val tm_Num_0 = mk_Num tm_zero
  val tm_Pair_p_q = mk_Pair var_p_cv var_q_cv
  val tm_Pair_r_s = mk_Pair var_r_cv var_s_cv
  val tm_Pair_p1_q1 = mk_Pair var_p1 var_q1
  val tm_Pair_p2_q2 = mk_Pair var_p2 var_q2
  val tm_Num_SUC_0 = mk_Num tm_SUC_0   (* Num (SUC (NUMERAL _0)) = Num 1 *)

  (* --- Equations 24-27: cv_add --- *)
  val cv_add_def = load_theorem "cv$cv_add_def"
  (* cv_add (Num m) (Num n) = Num (m + n) ∧
     cv_add (Num m) (Pair p q) = Num m ∧
     cv_add (Pair p q) (Num n) = Num n ∧
     cv_add (Pair p q) (Pair r s) = Num 0 *)

  val tm_eq24 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_add tm_Num_m) tm_Num_n)
                               (mk_Num tm_m_plus_n)
  val tm_eq25 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_add tm_Num_m) tm_Pair_p_q)
                               tm_Num_m
  val tm_eq26 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_add tm_Pair_p_q) tm_Num_n)
                               tm_Num_n
  val tm_eq27 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_add tm_Pair_p_q) tm_Pair_r_s)
                               tm_Num_0

  val [eq24, eq25, eq26, eq27] = extract4 cv_add_def [tm_eq24, tm_eq25, tm_eq26, tm_eq27]
  val () = save "candle$COMPUTE_EQ_24" eq24
  val () = save "candle$COMPUTE_EQ_25" eq25
  val () = save "candle$COMPUTE_EQ_26" eq26
  val () = save "candle$COMPUTE_EQ_27" eq27

  (* --- Equations 28-31: cv_sub --- *)
  val cv_sub_def = load_theorem "cv$cv_sub_def"
  val tm_m_minus_n = mk_minus var_m var_n

  val tm_eq28 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_sub tm_Num_m) tm_Num_n)
                               (mk_Num tm_m_minus_n)
  val tm_eq29 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_sub tm_Num_m) tm_Pair_p_q)
                               tm_Num_m
  val tm_eq30 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_sub tm_Pair_p_q) tm_Num_n)
                               tm_Num_0
  val tm_eq31 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_sub tm_Pair_p_q) tm_Pair_r_s)
                               tm_Num_0

  val [eq28, eq29, eq30, eq31] = extract4 cv_sub_def [tm_eq28, tm_eq29, tm_eq30, tm_eq31]
  val () = save "candle$COMPUTE_EQ_28" eq28
  val () = save "candle$COMPUTE_EQ_29" eq29
  val () = save "candle$COMPUTE_EQ_30" eq30
  val () = save "candle$COMPUTE_EQ_31" eq31

  (* --- Equations 32-35: cv_mul --- *)
  val cv_mul_def = load_theorem "cv$cv_mul_def"
  val tm_m_times_n = mk_times var_m var_n

  val tm_eq32 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_mul tm_Num_m) tm_Num_n)
                               (mk_Num tm_m_times_n)
  val tm_eq33 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_mul tm_Num_m) tm_Pair_p_q)
                               tm_Num_0
  val tm_eq34 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_mul tm_Pair_p_q) tm_Num_n)
                               tm_Num_0
  val tm_eq35 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_mul tm_Pair_p_q) tm_Pair_r_s)
                               tm_Num_0

  val [eq32, eq33, eq34, eq35] = extract4 cv_mul_def [tm_eq32, tm_eq33, tm_eq34, tm_eq35]
  val () = save "candle$COMPUTE_EQ_32" eq32
  val () = save "candle$COMPUTE_EQ_33" eq33
  val () = save "candle$COMPUTE_EQ_34" eq34
  val () = save "candle$COMPUTE_EQ_35" eq35

  (* --- Equations 36-39: cv_div --- *)
  val cv_div_def = load_theorem "cv$cv_div_def"
  val tm_m_DIV_n = mk_DIV var_m var_n

  val tm_eq36 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_div tm_Num_m) tm_Num_n)
                               (mk_Num tm_m_DIV_n)
  val tm_eq37 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_div tm_Num_m) tm_Pair_p_q)
                               tm_Num_0
  val tm_eq38 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_div tm_Pair_p_q) tm_Num_n)
                               tm_Num_0
  val tm_eq39 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_div tm_Pair_p_q) tm_Pair_r_s)
                               tm_Num_0

  val [eq36, eq37, eq38, eq39] = extract4 cv_div_def [tm_eq36, tm_eq37, tm_eq38, tm_eq39]
  val () = save "candle$COMPUTE_EQ_36" eq36
  val () = save "candle$COMPUTE_EQ_37" eq37
  val () = save "candle$COMPUTE_EQ_38" eq38
  val () = save "candle$COMPUTE_EQ_39" eq39

  (* --- Equations 40-43: cv_mod --- *)
  val cv_mod_def = load_theorem "cv$cv_mod_def"
  val tm_m_MOD_n = mk_MOD var_m var_n

  val tm_eq40 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_mod tm_Num_m) tm_Num_n)
                               (mk_Num tm_m_MOD_n)
  val tm_eq41 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_mod tm_Num_m) tm_Pair_p_q)
                               tm_Num_m
  val tm_eq42 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_mod tm_Pair_p_q) tm_Num_n)
                               tm_Num_0
  val tm_eq43 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_mod tm_Pair_p_q) tm_Pair_r_s)
                               tm_Num_0

  val [eq40, eq41, eq42, eq43] = extract4 cv_mod_def [tm_eq40, tm_eq41, tm_eq42, tm_eq43]
  val () = save "candle$COMPUTE_EQ_40" eq40
  val () = save "candle$COMPUTE_EQ_41" eq41
  val () = save "candle$COMPUTE_EQ_42" eq42
  val () = save "candle$COMPUTE_EQ_43" eq43

  (* --- Equations 44-47: cv_lt --- *)
  val cv_lt_def = load_theorem "cv$cv_lt_def"
  (* cv_lt (Num m) (Num n) = Num (if m < n then SUC 0 else 0) ∧ ... *)
  val tm_lt_cond = mk_COND_num (mk_LESS var_m var_n) tm_SUC_0 tm_zero

  val tm_eq44 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_lt tm_Num_m) tm_Num_n)
                               (mk_Num tm_lt_cond)
  val tm_eq45 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_lt tm_Num_m) tm_Pair_p_q)
                               tm_Num_0
  val tm_eq46 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_lt tm_Pair_p_q) tm_Num_n)
                               tm_Num_0
  val tm_eq47 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_lt tm_Pair_p_q) tm_Pair_r_s)
                               tm_Num_0

  val [eq44, eq45, eq46, eq47] = extract4 cv_lt_def [tm_eq44, tm_eq45, tm_eq46, tm_eq47]
  val () = save "candle$COMPUTE_EQ_44" eq44
  val () = save "candle$COMPUTE_EQ_45" eq45
  val () = save "candle$COMPUTE_EQ_46" eq46
  val () = save "candle$COMPUTE_EQ_47" eq47

  (* --- Equations 48-50: cv_if --- *)
  val cv_if_def = load_theorem "cv$cv_if_def"
  (* HOL4 order:
     cv_if (Num (SUC m)) p q = p ∧
     cv_if (Num 0) p q = q ∧
     cv_if (Pair r s) p q = q
     Candle spec order: 48=SUC, 49=Pair, 50=0 *)
  val tm_Num_SUC_m = mk_Num tm_SUC_m

  val tm_if_SUC = mk_eq_tm eq_cv (mk_comb (mk_comb (mk_comb const_cv_if tm_Num_SUC_m) var_p_cv) var_q_cv)
                                  var_p_cv
  val tm_if_0 = mk_eq_tm eq_cv (mk_comb (mk_comb (mk_comb const_cv_if tm_Num_0) var_p_cv) var_q_cv)
                                var_q_cv
  val tm_if_Pair = mk_eq_tm eq_cv (mk_comb (mk_comb (mk_comb const_cv_if tm_Pair_r_s) var_p_cv) var_q_cv)
                                   var_q_cv

  (* Extract in HOL4 order, then assign to Candle equation numbers *)
  val [th_if_SUC, th_if_0, th_if_Pair] = extract3 cv_if_def [tm_if_SUC, tm_if_0, tm_if_Pair]
  val eq48 = th_if_SUC   (* Candle eq 48: cv_if (Num (SUC m)) ... *)
  val eq49 = th_if_Pair  (* Candle eq 49: cv_if (Pair ...) ... *)
  val eq50 = th_if_0     (* Candle eq 50: cv_if (Num 0) ... *)
  val () = save "candle$COMPUTE_EQ_48" eq48
  val () = save "candle$COMPUTE_EQ_49" eq49
  val () = save "candle$COMPUTE_EQ_50" eq50

  (* --- Equations 51-52: cv_fst --- *)
  val cv_fst_def = load_theorem "cv$cv_fst_def"
  (* cv_fst (Pair p q) = p ∧ cv_fst (Num m) = Num 0 *)

  val tm_eq51 = mk_eq_tm eq_cv (mk_comb const_cv_fst tm_Pair_p_q) var_p_cv
  val tm_eq52 = mk_eq_tm eq_cv (mk_comb const_cv_fst tm_Num_m) tm_Num_0

  val [eq51, eq52] = extract2 cv_fst_def [tm_eq51, tm_eq52]
  val () = save "candle$COMPUTE_EQ_51" eq51
  val () = save "candle$COMPUTE_EQ_52" eq52

  (* --- Equations 53-54: cv_snd --- *)
  val cv_snd_def = load_theorem "cv$cv_snd_def"

  val tm_eq53 = mk_eq_tm eq_cv (mk_comb const_cv_snd tm_Pair_p_q) var_q_cv
  val tm_eq54 = mk_eq_tm eq_cv (mk_comb const_cv_snd tm_Num_m) tm_Num_0

  val [eq53, eq54] = extract2 cv_snd_def [tm_eq53, tm_eq54]
  val () = save "candle$COMPUTE_EQ_53" eq53
  val () = save "candle$COMPUTE_EQ_54" eq54

  (* --- Equations 55-56: cv_ispair --- *)
  val cv_ispair_def = load_theorem "cv$cv_ispair_def"
  (* cv_ispair (Pair p q) = Num (SUC 0) ∧ cv_ispair (Num m) = Num 0 *)

  val tm_eq55 = mk_eq_tm eq_cv (mk_comb const_cv_ispair tm_Pair_p_q) tm_Num_SUC_0
  val tm_eq56 = mk_eq_tm eq_cv (mk_comb const_cv_ispair tm_Num_m) tm_Num_0

  val [eq55, eq56] = extract2 cv_ispair_def [tm_eq55, tm_eq56]
  val () = save "candle$COMPUTE_EQ_55" eq55
  val () = save "candle$COMPUTE_EQ_56" eq56

  (* --- Equation 57: cv_eq --- *)
  val cv_eq_def = load_theorem "cv$cv_eq_def"
  (* cv_eq p q = Num (if p = q then SUC 0 else 0) *)
  val tm_p_eq_q = mk_eq_tm eq_cv var_p_cv var_q_cv
  val tm_eq_cond = mk_COND_num tm_p_eq_q tm_SUC_0 tm_zero

  val tm_eq57 = mk_eq_tm eq_cv (mk_comb (mk_comb const_cv_eq var_p_cv) var_q_cv)
                               (mk_Num tm_eq_cond)
  (* cv_eq_def is a single equation, not a conjunction *)
  val eq57 = cv_eq_def
  val () = save "candle$COMPUTE_EQ_57" eq57

  (* --- Equations 58-61: CV_EQ (cv equality) --- *)
  val CV_EQ = load_theorem "cv$CV_EQ"
  (* (Pair p q = Pair r s) = (if p = r then q = s else F) ∧
     (Pair p q = Num n) = F ∧
     (Num m = Num n) = (m = n) *)
  (* Note: spec has 4 equations but CV_EQ has 3; equation 60/61 are symmetric *)

  val tm_Pair_eq_Pair = mk_eq_tm eq_cv tm_Pair_p_q tm_Pair_r_s
  val tm_p_eq_r = mk_eq_tm eq_cv var_p_cv var_r_cv
  val tm_q_eq_s = mk_eq_tm eq_cv var_q_cv var_s_cv
  val tm_IF_body = mk_COND_bool tm_p_eq_r tm_q_eq_s const_F
  val tm_eq58 = mk_eq_tm eq_bool tm_Pair_eq_Pair tm_IF_body

  val tm_Pair_eq_Num = mk_eq_tm eq_cv tm_Pair_p_q tm_Num_n
  val tm_eq59_cveq = mk_eq_tm eq_bool tm_Pair_eq_Num const_F

  val tm_Num_eq_Num = mk_eq_tm eq_cv tm_Num_m tm_Num_n
  val tm_eq60_cveq = mk_eq_tm eq_bool tm_Num_eq_Num tm_m_eq_n

  val [eq58, eq59_wrong, eq60_wrong] = extract3 CV_EQ [tm_eq58, tm_eq59_cveq, tm_eq60_cveq]
  (* CV_EQ has: (Pair=Pair), (Pair=Num), (Num=Num)
     Candle spec wants: 58=(Pair=Pair), 59=(Num=Num), 60=(Num=Pair), 61=(Pair=Num) *)
  val eq59 = eq60_wrong   (* (Num m = Num n) = (m = n) *)
  val eq61 = eq59_wrong   (* (Pair p q = Num n) = F *)

  (* Equation 60: (Num m = Pair p q) = F - derive from eq61 by symmetry *)
  val tm_Num_eq_Pair = mk_eq_tm eq_cv tm_Num_m tm_Pair_p_q
  val tm_eq60 = mk_eq_tm eq_bool tm_Num_eq_Pair const_F
  (* Use same symmetry trick as eq21 *)
  val assum_np = ASSUME tm_Num_eq_Pair       (* {Num m = Pair p q} ⊢ Num m = Pair p q *)
  val sym_np = SYM assum_np                   (* {Num m = Pair p q} ⊢ Pair p q = Num m *)
  val assum_pn = ASSUME tm_Pair_eq_Num       (* {Pair p q = Num m} ⊢ Pair p q = Num m *)
  val sym_pn = SYM assum_pn                   (* {Pair p q = Num m} ⊢ Num m = Pair p q *)
  (* Need to instantiate eq61 with n := m *)
  val eq61_m = INST eq61 [(var_n, var_m)]
  val eq_sym_cv = DEDUCT_ANTISYM sym_np sym_pn  (* ⊢ (Num m = Pair p q) = (Pair p q = Num m) *)
  val eq60 = TRANS eq_sym_cv eq61_m            (* ⊢ (Num m = Pair p q) = F *)

  val () = save "candle$COMPUTE_EQ_58" eq58
  val () = save "candle$COMPUTE_EQ_59" eq59
  val () = save "candle$COMPUTE_EQ_60" eq60
  val () = save "candle$COMPUTE_EQ_61" eq61

  (* --- Equation 62: LET --- *)
  val LET_THM = load_theorem "bool$LET_THM"
  (* LET_THM: ⊢ ∀f x. LET f x = f x, where f:'a->'b, x:'a *)
  (* Candle needs: LET f p1 = f p1, where f:cv->cv, p1:cv *)
  val ty_alpha = mk_tyvar "'a"
  val ty_beta = mk_tyvar "'b"
  val LET_cv = INST_TYPE LET_THM [(ty_alpha, ty_cv), (ty_beta, ty_cv)]
  (* Now f : cv -> cv, x : cv. The variables in LET_THM are named f and x. *)
  val var_f_for_let = mk_var "f" ty_cv_cv
  val var_x_for_let = mk_var "x" ty_cv
  val eq62 = INST LET_cv [(var_x_for_let, var_p1)]
  val () = save "candle$COMPUTE_EQ_62" eq62

  (* ================================================================ *)
  (* Numeral translation: HOL4 (BIT1/BIT2) <-> Candle (BIT0/BIT1)     *)
  (*                                                                  *)
  (* HOL4:   BIT1 n = 2n + 1,  BIT2 n = 2n + 2                       *)
  (* Candle: BIT0 n = 2n,      BIT1 n = 2n + 1                       *)
  (*                                                                  *)
  (* Key equations to derive:                                         *)
  (*   BIT2 n = BIT0 (SUC n)     [core BIT2 elimination]             *)
  (*   SUC _0 = BIT1 _0          [SUC of zero]                       *)
  (*   SUC (BIT0 n) = BIT1 n     [SUC of even]                       *)
  (*   SUC (BIT1 n) = BIT0 (SUC n) [SUC of odd]                      *)
  (* ================================================================ *)

  (* Definitions we have:
       BIT0 n = n + n                    (defined in this preamble)
       BIT1 n = SUC (n + n)              (derived in this preamble) 
       BIT2 n = n + (n + SUC (SUC 0))    (from HOL4 arithmetic)

     Key arithmetic facts needed:
       ADD_CLAUSES: 0 + n = n, SUC m + n = SUC (m + n), etc.
       SUC properties
  *)

  (* --- Derive: SUC _0 = BIT1 _0 --- *)
  (* BIT1 _0 = SUC (_0 + _0) = SUC _0, so by symmetry SUC _0 = BIT1 _0 *)
  val tm_BIT1_0 = mk_comb const_BIT1 const_zero
  val tm_SUC_0_local = mk_SUC const_zero
  (* BIT1_candle: ⊢ BIT1 n = SUC (n + n), instantiate n := _0 *)
  val BIT1_at_0 = INST BIT1_candle [(var_n, const_zero)]
  (* ⊢ BIT1 _0 = SUC (_0 + _0) *)
  (* Need: _0 + _0 = _0, i.e., 0 + 0 = 0 *)
  val ADD_0_0 = INST eq8 [(var_n, const_zero)]  (* 0 + 0 = 0 from eq8: 0 + n = n *)
  val SUC_0_plus_0 = AP_TERM const_SUC ADD_0_0  (* SUC (0 + 0) = SUC 0 *)
  val BIT1_0_eq = TRANS BIT1_at_0 SUC_0_plus_0  (* BIT1 _0 = SUC _0 *)
  val SUC_0_eq_BIT1_0 = SYM BIT1_0_eq           (* SUC _0 = BIT1 _0 *)
  val () = save "candle$SUC_0" SUC_0_eq_BIT1_0

  (* --- Derive: SUC (BIT0 n) = BIT1 n --- *)
  (* BIT0 n = n + n, so SUC (BIT0 n) = SUC (n + n) = BIT1 n *)
  (* bit0_unfold: ⊢ BIT0 n = n + n *)
  val tm_BIT0_n = mk_comb const_BIT0 var_n
  val tm_SUC_BIT0_n = mk_SUC tm_BIT0_n
  val tm_n_plus_n = mk_plus var_n var_n
  val SUC_BIT0_step1 = AP_TERM const_SUC bit0_unfold  (* SUC (BIT0 n) = SUC (n + n) *)
  (* BIT1_candle: ⊢ BIT1 n = SUC (n + n) *)
  val SUC_BIT0_eq_BIT1 = TRANS SUC_BIT0_step1 (SYM BIT1_candle)  (* SUC (BIT0 n) = BIT1 n *)
  val () = save "candle$SUC_BIT0" SUC_BIT0_eq_BIT1

  (* --- Derive: SUC (BIT1 n) = BIT0 (SUC n) --- *)
  (* BIT1 n = SUC (n + n), so SUC (BIT1 n) = SUC (SUC (n + n))
     BIT0 (SUC n) = SUC n + SUC n
     Need: SUC (SUC (n + n)) = SUC n + SUC n
     From ADD: SUC m + n = SUC (m + n)
     So: SUC n + SUC n = SUC (n + SUC n) = SUC (SUC (n + n))  [using n + SUC m = SUC (n + m)] *)
  val tm_BIT1_n = mk_comb const_BIT1 var_n
  val tm_SUC_BIT1_n = mk_SUC tm_BIT1_n
  val tm_SUC_n = mk_SUC var_n
  val tm_BIT0_SUC_n = mk_comb const_BIT0 tm_SUC_n
  (* SUC (BIT1 n) = SUC (SUC (n + n)) *)
  val SUC_BIT1_step1 = AP_TERM const_SUC BIT1_candle  (* SUC (BIT1 n) = SUC (SUC (n + n)) *)
  (* BIT0 (SUC n) = SUC n + SUC n *)
  val bit0_SUC_n = INST bit0_unfold [(var_n, tm_SUC_n)]  (* BIT0 (SUC n) = SUC n + SUC n *)
  (* Need: SUC n + SUC n = SUC (SUC (n + n)) *)
  (* eq9: SUC m + n = SUC (m + n), inst m := n, n := SUC n *)
  val step_a = INST eq9 [(var_m, var_n), (var_n, tm_SUC_n)]  (* SUC n + SUC n = SUC (n + SUC n) *)
  (* ADD_SUC: m + SUC n = SUC (m + n), inst m := n, n := n *)
  val ADD_SUC_nn = INST ADD_SUC [(var_m, var_n), (var_n, var_n)]  (* n + SUC n = SUC (n + n) *)
  val step_b = AP_TERM const_SUC ADD_SUC_nn  (* SUC (n + SUC n) = SUC (SUC (n + n)) *)
  val SUC_n_plus_SUC_n = TRANS step_a step_b  (* SUC n + SUC n = SUC (SUC (n + n)) *)
  val BIT0_SUC_n_eq = TRANS bit0_SUC_n SUC_n_plus_SUC_n  (* BIT0 (SUC n) = SUC (SUC (n + n)) *)
  val SUC_BIT1_eq_BIT0_SUC = TRANS SUC_BIT1_step1 (SYM BIT0_SUC_n_eq)  (* SUC (BIT1 n) = BIT0 (SUC n) *)
  val () = save "candle$SUC_BIT1" SUC_BIT1_eq_BIT0_SUC

  (* --- Derive: BIT2 n = BIT0 (SUC n) --- *)
  (* BIT2 n = n + (n + SUC (SUC 0)) = 2n + 2
     BIT0 (SUC n) = SUC n + SUC n = 2(n + 1) = 2n + 2
     So BIT2 n = BIT0 (SUC n) *)
  val hol4_BIT2 = load_theorem "arithmetic$BIT2"
  (* BIT2: ⊢ BIT2 n = n + (n + SUC (SUC 0)) *)
  (* We already derived BIT0 (SUC n) = SUC (SUC (n + n)) above.
     Need to show: n + (n + SUC (SUC 0)) = SUC (SUC (n + n)) *)
  (* This requires several steps of arithmetic manipulation.
     For now, derive via a different route using the equations we have. *)

  (* Alternative: derive BIT2 n = SUC (BIT1 n) first, then use SUC_BIT1 *)
  (* BIT2 n = n + (n + SUC (SUC 0)) = n + (n + 2)
     BIT1 n = SUC (n + n) = 2n + 1
     SUC (BIT1 n) = 2n + 2 = BIT2 n *)
  (* From BIT1_candle: BIT1 n = SUC (n + n)
     SUC (BIT1 n) = SUC (SUC (n + n))
     Need: BIT2 n = SUC (SUC (n + n)) *)

  (* BIT2 n = n + (n + SUC (SUC 0))
     Let's compute n + SUC (SUC 0):
       n + SUC (SUC 0) = SUC (n + SUC 0)   [ADD_SUC]
                       = SUC (SUC (n + 0)) [ADD_SUC]
                       = SUC (SUC n)       [ADD_0]
     So BIT2 n = n + SUC (SUC n)
               = SUC (n + SUC n)           [ADD_SUC with args swapped... need ADD_SUC form]
     Hmm, eq9 is SUC m + n = SUC (m + n), not m + SUC n = SUC (m + n)
     We have ADD_SUC: m + SUC n = SUC (m + n) *)

  val tm_BIT2_n = mk_comb const_BIT2 var_n
  val tm_two = mk_SUC (mk_SUC const_zero)  (* SUC (SUC 0) = 2 *)
  val tm_n_plus_two = mk_plus var_n tm_two
  val tm_n_plus_n_plus_two = mk_plus var_n tm_n_plus_two

  (* Step 1: n + SUC (SUC 0) = SUC (n + SUC 0) *)
  val step1_a = INST ADD_SUC [(var_m, var_n), (var_n, mk_SUC const_zero)]
  (* n + SUC (SUC 0) = SUC (n + SUC 0) *)

  (* Step 2: n + SUC 0 = SUC (n + 0) *)
  val step2_a = INST ADD_SUC [(var_m, var_n), (var_n, const_zero)]
  (* n + SUC 0 = SUC (n + 0) *)

  (* Step 3: n + _0 = n, from ADD_0: ⊢ !m. m + _0 = m *)
  val ADD_0_n = do_SPEC add0_pred var_n var_m ty_num ADD_0

  (* Combine: n + SUC 0 = SUC (n + 0) = SUC n *)
  val n_plus_SUC_0 = TRANS step2_a (AP_TERM const_SUC ADD_0_n)
  (* n + SUC 0 = SUC n *)

  (* Combine: n + SUC (SUC 0) = SUC (n + SUC 0) = SUC (SUC n) *)
  val n_plus_two_eq = TRANS step1_a (AP_TERM const_SUC n_plus_SUC_0)
  (* n + SUC (SUC 0) = SUC (SUC n) *)

  (* Step 4: n + (n + SUC (SUC 0)) = n + SUC (SUC n) *)
  val BIT2_rhs_step = AP_TERM (mk_comb const_plus var_n) n_plus_two_eq
  (* n + (n + SUC (SUC 0)) = n + SUC (SUC n) *)

  (* Step 5: n + SUC (SUC n) = SUC (n + SUC n) *)
  val step5 = INST ADD_SUC [(var_m, var_n), (var_n, tm_SUC_n)]
  (* n + SUC (SUC n) = SUC (n + SUC n) *)

  (* Step 6: n + SUC n = SUC (n + n) *)
  (* Already have ADD_SUC_nn from above *)

  (* Combine: n + SUC (SUC n) = SUC (n + SUC n) = SUC (SUC (n + n)) *)
  val step6 = TRANS step5 (AP_TERM const_SUC ADD_SUC_nn)
  (* n + SUC (SUC n) = SUC (SUC (n + n)) *)

  (* Combine all: n + (n + SUC (SUC 0)) = SUC (SUC (n + n)) *)
  val BIT2_rhs_final = TRANS BIT2_rhs_step step6

  (* BIT2 n = n + (n + SUC (SUC 0)) = SUC (SUC (n + n)) *)
  val BIT2_eq_SUC_SUC = TRANS hol4_BIT2 BIT2_rhs_final

  (* BIT0 (SUC n) = SUC (SUC (n + n))  [from BIT0_SUC_n_eq above] *)
  (* So BIT2 n = BIT0 (SUC n) *)
  val BIT2_eq_BIT0_SUC = TRANS BIT2_eq_SUC_SUC (SYM BIT0_SUC_n_eq)
  val () = save "candle$BIT2_eq_BIT0_SUC" BIT2_eq_BIT0_SUC

  (* --- Generate cached numeral translations for 0-255 --- *)
  (* Only cache translations for numerals containing BIT2 in HOL4 form.
     Numbers that are 2^k - 1 (0,1,3,7,15,31,63,127,255) use only BIT1
     and need no translation (just REFL). *)

  (* Helper: does this number need translation? (contains BIT2 in HOL4 form) *)
  fun needs_translation 0 = false
    | needs_translation n =
        let val r = n mod 2
        in if r = 1 then needs_translation ((n - 1) div 2)  (* BIT1 case *)
           else true  (* BIT2 case: r = 0 means n = 2k+2, so n-2 = 2k *)
        end

  (* Build HOL4 numeral term (using BIT1/BIT2/_0) for value v > 0 *)
  fun mk_hol4_numeral_bits 0 = const_zero  (* _0 *)
    | mk_hol4_numeral_bits n =
        let val r = n mod 2
            val q = if r = 1 then (n - 1) div 2 else (n - 2) div 2
        in if r = 1
           then mk_comb const_BIT1 (mk_hol4_numeral_bits q)
           else mk_comb const_BIT2 (mk_hol4_numeral_bits q)
        end

  (* Build Candle numeral term (using BIT0/BIT1/_0) for value v > 0 *)
  fun mk_candle_numeral_bits 0 = const_zero  (* _0 *)
    | mk_candle_numeral_bits n =
        let val r = n mod 2
            val q = n div 2
        in if r = 1
           then mk_comb const_BIT1 (mk_candle_numeral_bits q)
           else mk_comb const_BIT0 (mk_candle_numeral_bits q)
        end

  (* Derive: SUC (candle_bits) = candle_bits'
     Given a Candle numeral term, compute SUC of it and return theorem.
     Uses SUC_0, SUC_BIT0, SUC_BIT1 equations. *)
  fun derive_SUC_candle candle_tm =
    (* Determine structure of candle_tm *)
    if candle_tm = const_zero then
      (* SUC _0 = BIT1 _0 *)
      SUC_0_eq_BIT1_0
    else
      (* candle_tm is BIT0 arg or BIT1 arg *)
      (* We need to inspect the term structure, but we only have term IDs.
         Instead, we track the numeric value and reconstruct. *)
      raise Fail "derive_SUC_candle: not implemented for non-zero"

  (* Derive translation theorem: HOL4_bits = Candle_bits
     Uses BIT2_eq_BIT0_SUC and SUC equations to eliminate BIT2 and SUC.

     Strategy: recursively translate, building proof as we go.
     - _0 -> REFL _0
     - BIT1 inner -> if inner needs translation, use MK_COMB on BIT1 + translate(inner)
                     else REFL
     - BIT2 inner -> BIT2 inner = BIT0 (SUC inner)  [BIT2_eq_BIT0_SUC]
                     then simplify SUC inner using SUC equations
                     then recursively handle the result
  *)

  (* Since we can't inspect term structure (only have IDs), we work with
     numeric values and build both terms and proofs together. *)

  (* translate_bits n returns (hol4_tm, candle_tm, th) where th: hol4_tm = candle_tm
     For n that needs no translation, returns REFL. *)
  fun translate_bits 0 = (const_zero, const_zero, REFL const_zero)
    | translate_bits n =
        let val r = n mod 2
        in if r = 1 then
             (* HOL4: BIT1 ((n-1)/2), Candle: BIT1 (n/2) but (n-1)/2 = n/2 for odd n *)
             let val q = (n - 1) div 2
                 val (inner_h, inner_c, inner_th) = translate_bits q
                 val hol4_tm = mk_comb const_BIT1 inner_h
                 val candle_tm = mk_comb const_BIT1 inner_c
             in if inner_h = inner_c then
                  (hol4_tm, candle_tm, REFL hol4_tm)
                else
                  (* BIT1 inner_h = BIT1 inner_c by MK_COMB *)
                  (hol4_tm, candle_tm, AP_TERM const_BIT1 inner_th)
             end
           else
             (* HOL4: BIT2 ((n-2)/2), Candle: BIT0 (n/2) *)
             let val q_hol4 = (n - 2) div 2   (* argument to BIT2 *)
                 val q_candle = n div 2       (* argument to BIT0 *)
                 (* Note: q_candle = q_hol4 + 1 *)

                 val inner_h = mk_hol4_numeral_bits q_hol4
                 val candle_tm = mk_candle_numeral_bits n
                 val hol4_tm = mk_comb const_BIT2 inner_h

                 (* BIT2 inner_h = BIT0 (SUC inner_h) by BIT2_eq_BIT0_SUC *)
                 val step1 = INST BIT2_eq_BIT0_SUC [(var_n, inner_h)]
                 (* step1: BIT2 inner_h = BIT0 (SUC inner_h) *)

                 (* Now we need: SUC inner_h = candle_bits(q_hol4 + 1) = candle_bits(q_candle) *)
                 (* And then: BIT0 (candle_bits(q_candle)) = candle_tm *)

                 (* Get translation for inner: inner_h = inner_c *)
                 val (_, inner_c, inner_th) = translate_bits q_hol4

                 (* SUC inner_h = SUC inner_c (if inner_h ≠ inner_c) *)
                 val SUC_inner_h = mk_SUC inner_h
                 val SUC_inner_c = mk_SUC inner_c
                 val suc_eq = if inner_h = inner_c then REFL SUC_inner_h
                              else AP_TERM const_SUC inner_th
                 (* suc_eq: SUC inner_h = SUC inner_c *)

                 (* Now simplify SUC inner_c to get candle form *)
                 (* SUC of candle numeral: use derive_SUC_result *)
                 val (suc_result, suc_simp_th) = derive_SUC_result q_hol4
                 (* suc_simp_th: SUC inner_c = suc_result (a candle numeral) *)

                 (* Chain: SUC inner_h = SUC inner_c = suc_result *)
                 val suc_full = TRANS suc_eq suc_simp_th
                 (* suc_full: SUC inner_h = suc_result *)

                 (* BIT0 (SUC inner_h) = BIT0 suc_result *)
                 val bit0_eq = AP_TERM const_BIT0 suc_full

                 (* Chain: BIT2 inner_h = BIT0 (SUC inner_h) = BIT0 suc_result *)
                 val full_th = TRANS step1 bit0_eq

             in (hol4_tm, mk_comb const_BIT0 suc_result, full_th) end
        end

  (* derive_SUC_result n: given numeric value n, compute SUC of its Candle representation
     Returns (result_tm, th) where th: SUC (candle_bits n) = result_tm *)
  and derive_SUC_result n =
    let val candle_n = mk_candle_numeral_bits n
        val suc_candle_n = mk_SUC candle_n
    in if n = 0 then
         (* SUC _0 = BIT1 _0 *)
         (mk_comb const_BIT1 const_zero, SUC_0_eq_BIT1_0)
       else
         let val r = n mod 2
             val q = n div 2
         in if r = 0 then
              (* candle_n = BIT0 (candle_bits q) *)
              (* SUC (BIT0 x) = BIT1 x *)
              let val inner = mk_candle_numeral_bits q
                  val th = INST SUC_BIT0_eq_BIT1 [(var_n, inner)]
                  (* th: SUC (BIT0 inner) = BIT1 inner *)
              in (mk_comb const_BIT1 inner, th) end
            else
              (* candle_n = BIT1 (candle_bits q) *)
              (* SUC (BIT1 x) = BIT0 (SUC x) *)
              let val inner = mk_candle_numeral_bits q
                  val th1 = INST SUC_BIT1_eq_BIT0_SUC [(var_n, inner)]
                  (* th1: SUC (BIT1 inner) = BIT0 (SUC inner) *)

                  (* Recursively simplify SUC inner *)
                  val (suc_inner_result, suc_inner_th) = derive_SUC_result q
                  (* suc_inner_th: SUC inner = suc_inner_result *)

                  (* BIT0 (SUC inner) = BIT0 suc_inner_result *)
                  val th2 = AP_TERM const_BIT0 suc_inner_th

                  val result = mk_comb const_BIT0 suc_inner_result
              in (result, TRANS th1 th2) end
         end
    end

  (* Cache forward translations (HOL4 -> Candle) for 2-255 that need them *)
  val () = let
    fun cache_one n =
      if needs_translation n then
        let val (_, _, th) = translate_bits n
        in save ("candle$NUM_XLATE_" ^ Int.toString n) th end
      else ()
  in List.app cache_one (List.tabulate (256, fn i => i)) end

  (* For reverse translation (Candle -> HOL4), we just use SYM of forward.
     The same numbers need translation in both directions. *)
  val () = let
    fun cache_reverse n =
      if needs_translation n then
        let val (_, _, th) = translate_bits n
            val th_rev = SYM th
        in save ("candle$NUM_XLATE_REV_" ^ Int.toString n) th_rev end
      else ()
  in List.app cache_reverse (List.tabulate (256, fn i => i)) end

in () end

end (* struct *)
