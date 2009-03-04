(* ========================================================================= *)
(* Linear decision procedure for the reals, plus some proof procedures.      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*                                                                           *)
(*       Ported to hol98 by Joe Hurd, 2 Oct 1998                             *)
(* ========================================================================= *)


structure RealArith :> RealArith =
struct


(*
app load ["Arbint",
          "reduceLib",
          "pairTheory",
          "numLib",
          "realTheory",
          "PairedLambda",
          "tautLib",
          "Ho_rewrite",
          "jrhUtils",
          "Canon_Port",
          "liteLib", "AC", "numLib" (*goofy*)];
*)

open HolKernel Parse boolLib pairLib hol88Lib numLib reduceLib tautLib
     pairTheory numTheory prim_recTheory arithmeticTheory
     realTheory Ho_Rewrite jrhUtils Canon_Port AC numSyntax Arbint;


(*---------------------------------------------------------------------------*)
(* Establish the required grammar(s) for executing this file                 *)
(*---------------------------------------------------------------------------*)

val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars realTheory.real_grammars;

(*----------------------------------------------------------------------- *)
(* The trace system.                                                      *)
(* ---------------------------------------------------------------------- *)

local
  open Int
  val traceval = ref 0

  fun trace_pure s () = print s
  fun check f = if !traceval > 0 then f() else ()
  infix >>
  fun (f >> g) () = (f () ; g ())
  val _ = register_trace ("RealArith dp", traceval, 1)
  fun trace_line () = print "\n"
  local
    fun tl f [] = (fn () => ())
      | tl f [h] = f h
      | tl f (h::t) = (f h >> trace_pure ", " >> tl f t)
  in
    fun trace_list_pure f l () =
        (trace_pure "[" >> tl f l >> trace_pure "]") ()
  end
  fun trace_term_pure t () = print (term_to_string t)
  fun trace_thm_pure t = trace_term_pure (concl t)
in
  fun trace s = check (trace_pure (s ^ "\n"))
  fun trace_term t = check (trace_term_pure t >> trace_line)
  fun trace_term_list l =
      check (trace_list_pure trace_term_pure l >> trace_line)
  fun trace_thm t = check (trace_thm_pure t >> trace_line)
  fun trace_thm_list l = check (trace_list_pure trace_thm_pure l >> trace_line)
end;

(* ------------------------------------------------------------------------- *)
(* Functions to be compatible with hol-light.                                *)
(* ------------------------------------------------------------------------- *)

fun failwith s = liteLib.failwith s
fun fail () = failwith "No message";

fun term_lt u t = Term.compare(u,t) = LESS
fun term_le t u = not (term_lt u t);

fun el0 n l = if n <= zero then hd l
              else el0 (n - one) (tl l) handle _ => raise Fail "RealArith.el0"

fun index x =
  let
    fun ind n [] = failwith "index"
      | ind n (h::t) = if x = h then n else ind (n + one) t
  in
    ind zero
  end

fun index_ac x = let
  fun ind n [] = failwith "index_ac"
    | ind n (h::t) = if aconv x h then n else ind (n + one) t
in
  ind zero
end


fun remove P [] = failwith "remove"
  | remove P (h::t) = if P h then (h,t) else
      let
        val (e,l) = remove P t
      in
        (e, h::l)
      end;

fun chop_list n l =
  if n = zero then ([],l) else
    let
      val (m,l') = chop_list (n-one) (Lib.trye tl l)
    in
      (Lib.trye hd l::m, l')
    end
    handle HOL_ERR _ => failwith "chop_list";

val mk_binop =
  let
    fun mk_binop_alt t = curry (liteLib.mk_binop t);
  in
    mk_binop_alt
  end;

fun list_mk_binop op_alt = end_itlist (mk_binop op_alt);

val REFUTE_THEN =
  let
    val conv = REWR_CONV(TAUT_PROVE (Term`p = ~p ==> F`))
  in
    fn ttac => CONV_TAC conv THEN DISCH_THEN ttac
  end;

val PRESIMP_CONV =
  GEN_REWRITE_CONV DEPTH_CONV
   [NOT_CLAUSES, AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES,
    FORALL_SIMP, EXISTS_SIMP, EXISTS_OR_THM, FORALL_AND_THM,
    LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM,
    LEFT_FORALL_OR_THM, RIGHT_FORALL_OR_THM];

val TAUT = TAUT_PROVE;

val NUM_LE_CONV = LE_CONV;
val NUM_LT_CONV = LT_CONV;
val NUM_ADD_CONV = ADD_CONV;

(* ------------------------------------------------------------------------- *)
(* Functions dealing with numbers (numerals) in theorems.                    *)
(* ------------------------------------------------------------------------- *)


val mk_numeral = mk_numeral o toNat
val dest_numeral = fromNat o dest_numeral

val amp = Term`(&)`;

val is_numconst =
 fn tm =>
      let
        val (l,r) = dest_comb tm
      in
        l = amp andalso is_numeral r
      end
      handle HOL_ERR _ => false;

fun mk_numconst n = mk_comb(amp, mk_numeral n);

fun dest_numconst tm =
  let
    val (l,r) = dest_comb tm
  in
    if l = amp then
      dest_numeral r
    else
      failwith "dest_numconst"
  end;

val dsub = Term`$~ :real->real`;
val is_intconst =
    fn tm =>
      is_numconst tm orelse
      let
        val (l,r) = dest_comb tm
      in
        l = dsub andalso is_numconst r
      end
      handle HOL_ERR _ => false;


fun mk_intconst n =
  if n < zero then
    mk_comb(dsub,mk_numconst(~n))
  else
    mk_numconst(n);

fun dest_intconst tm =
  if (rator tm = dsub handle HOL_ERR _ => false) then
    ~(dest_numconst(rand tm))
  else
    dest_numconst(tm);


(* ------------------------------------------------------------------------- *)
(* Preparing the real linear decision procedure.                             *)
(* ------------------------------------------------------------------------- *)

val LE_0 = arithmeticTheory.ZERO_LESS_EQ;
val LE = arithmeticTheory.LE;
val NOT_LE = arithmeticTheory.NOT_LESS_EQUAL;
val LE_ANTISYM = GSYM arithmeticTheory.EQ_LESS_EQ;

val REAL_ADD_AC_98 = (REAL_ADD_ASSOC, REAL_ADD_SYM);

val REAL_MUL_AC_98 = (REAL_MUL_ASSOC, REAL_MUL_SYM)

val EQ_REFL_T = GEN_ALL (MATCH_MP (TAUT_PROVE (Term`a ==> (a = T)`) )
                                  (SPEC_ALL EQ_REFL));

val real_abs = realTheory.abs;

val ETA_THM = boolTheory.ETA_THM;


val EXISTS_UNIQUE_THM = prove
 (Term`!P. (?!x:'a. P x) = (?x. P x) /\ (!x x'. P x /\ P x' ==> (x = x'))`,
  GEN_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_DEF]
   THEN BETA_TAC THEN BETA_TAC THEN REFL_TAC);

val (NNF_CONV,NNFC_CONV) =
  let
    val NOT_EXISTS_UNIQUE_THM = prove
      (Term`~(?!x:'a. P x) = (!x. ~P x) \/ ?x x'. P x /\ P x' /\ ~(x = x')`,
       REWRITE_TAC[EXISTS_UNIQUE_THM, DE_MORGAN_THM, NOT_EXISTS_THM] THEN
       REWRITE_TAC[NOT_FORALL_THM, NOT_IMP, CONJ_ASSOC])
    val common_tauts =
      [TAUT (Term`~~p:bool = p`),
      TAUT  (Term`~(p /\ q) = ~p \/ ~q`),
      TAUT  (Term`~(p \/ q) = ~p /\ ~q`),
      TAUT  (Term`~(p ==> q) = p /\ ~q`),
      TAUT  (Term`p ==> q = ~p \/ q`),
      NOT_FORALL_THM,
      NOT_EXISTS_THM,
      EXISTS_UNIQUE_THM,
      NOT_EXISTS_UNIQUE_THM]
    val dnf_tauts =
      map (TAUT o Term)
              [`~(p = q) = (p /\ ~q) \/ (~p /\ q)`,
               `(p = q) = (p /\ q) \/ (~p /\ ~q)`]
    val cnf_tauts =
      map (TAUT o Term)
          [`~(p = q) = (p \/ q) /\ (~p \/ ~q)`,
           `(p = q) = (p \/ ~q) /\ (~p \/ q)`]
    val NNF_CONV =
      GEN_REWRITE_CONV TOP_SWEEP_CONV (common_tauts @ dnf_tauts)
    val NNFC_CONV =
      GEN_REWRITE_CONV TOP_SWEEP_CONV (common_tauts @ cnf_tauts)
    fun SINGLE_SWEEP_CONV conv tm =
      let
        val th = conv tm
        val tm' = rand(concl th)
        val th' = if is_abs tm' then NNFC_CONV tm'
                    else SUB_CONV (SINGLE_SWEEP_CONV conv) tm'
      in
        TRANS th th'
      end
      handle HOL_ERR _ =>
          if is_abs tm then NNFC_CONV tm else
          SUB_CONV (SINGLE_SWEEP_CONV conv) tm
  in
    (NNF_CONV,
     SINGLE_SWEEP_CONV (GEN_REWRITE_CONV I (common_tauts @ dnf_tauts)))
  end;

val PROP_DNF_CONV =
  GEN_REWRITE_CONV REDEPTH_CONV
   [TAUT (Term`a /\ (b \/ c) = (a /\ b) \/ (a /\ c)`),
    TAUT (Term`(a \/ b) /\ c = (a /\ c) \/ (b /\ c)`),
    GSYM CONJ_ASSOC, GSYM DISJ_ASSOC];

(* ------------------------------------------------------------------------- *)
(* First all the comparison operators.                                       *)
(* ------------------------------------------------------------------------- *)

val (REAL_INT_LE_CONV,REAL_INT_LT_CONV,
  REAL_INT_GE_CONV,REAL_INT_GT_CONV,REAL_INT_EQ_CONV) =
  let
    val tth =
    TAUT (Term`(F /\ F = F) /\ (F /\ T = F) /\ (T /\ F = F) /\ (T /\ T = T)`)
    val nth = TAUT (Term`(~T = F) /\ (~F = T)`)
    val NUM2_EQ_CONV =
      liteLib.COMB2_CONV (RAND_CONV NEQ_CONV) NEQ_CONV THENC
      GEN_REWRITE_CONV I [tth]
    val NUM2_NE_CONV =
      RAND_CONV NUM2_EQ_CONV THENC
      GEN_REWRITE_CONV I [nth]
    val [pth_le1, pth_le2a, pth_le2b, pth_le3] = (CONJUNCTS o prove)
      (Term`(~(&m) <= &n = T) /\
            (&m <= &n = m <= n) /\
            (~(&m) <= ~(&n) = n <= m) /\
            (&m <= ~(&n) = (m = 0) /\ (n = 0))`,
      REWRITE_TAC[REAL_LE_NEG2] THEN
      REWRITE_TAC[REAL_LE_LNEG, REAL_LE_RNEG] THEN
      REWRITE_TAC[REAL_ADD, REAL_OF_NUM_LE, LE_0] THEN
      REWRITE_TAC[LE, ADD_EQ_0])
    val REAL_INT_LE_CONV = FIRST_CONV
      [GEN_REWRITE_CONV I [pth_le1],
      GEN_REWRITE_CONV I [pth_le2a, pth_le2b] THENC NUM_LE_CONV,
      GEN_REWRITE_CONV I [pth_le3] THENC NUM2_EQ_CONV]
    val [pth_lt1, pth_lt2a, pth_lt2b, pth_lt3] = (CONJUNCTS o prove)
      (Term`(&m < ~(&n) = F) /\
            (&m < &n = m < n) /\
            (~(&m) < ~(&n) = n < m) /\
            (~(&m) < &n = ~((m = 0) /\ (n = 0)))`,
      REWRITE_TAC[pth_le1, pth_le2a, pth_le2b, pth_le3,
                GSYM NOT_LE, real_lt] THEN
      CONV_TAC tautLib.TAUT_CONV)
    val REAL_INT_LT_CONV = FIRST_CONV
      [GEN_REWRITE_CONV I [pth_lt1],
      GEN_REWRITE_CONV I [pth_lt2a, pth_lt2b] THENC NUM_LT_CONV,
      GEN_REWRITE_CONV I [pth_lt3] THENC NUM2_NE_CONV]
    val [pth_ge1, pth_ge2a, pth_ge2b, pth_ge3] = (CONJUNCTS o prove)
      (Term`(&m >= ~(&n) = T) /\
            (&m >= &n = n <= m) /\
            (~(&m) >= ~(&n) = m <= n) /\
            (~(&m) >= &n = (m = 0) /\ (n = 0))`,
      REWRITE_TAC[pth_le1, pth_le2a, pth_le2b, pth_le3, real_ge] THEN
      CONV_TAC tautLib.TAUT_CONV)
    val REAL_INT_GE_CONV = FIRST_CONV
      [GEN_REWRITE_CONV I [pth_ge1],
      GEN_REWRITE_CONV I [pth_ge2a, pth_ge2b] THENC NUM_LE_CONV,
      GEN_REWRITE_CONV I [pth_ge3] THENC NUM2_EQ_CONV]
    val [pth_gt1, pth_gt2a, pth_gt2b, pth_gt3] = (CONJUNCTS o prove)
      (Term`(~(&m) > &n = F) /\
            (&m > &n = n < m) /\
            (~(&m) > ~(&n) = m < n) /\
            (&m > ~(&n) = ~((m = 0) /\ (n = 0)))`,
      REWRITE_TAC[pth_lt1, pth_lt2a, pth_lt2b, pth_lt3, real_gt] THEN
      CONV_TAC tautLib.TAUT_CONV)
    val REAL_INT_GT_CONV = FIRST_CONV
      [GEN_REWRITE_CONV I [pth_gt1],
      GEN_REWRITE_CONV I [pth_gt2a, pth_gt2b] THENC NUM_LT_CONV,
      GEN_REWRITE_CONV I [pth_gt3] THENC NUM2_NE_CONV]
    val [pth_eq1a, pth_eq1b, pth_eq2a, pth_eq2b] = (CONJUNCTS o prove)
      (Term`((&m = &n) = (m = n)) /\
            ((~(&m) = ~(&n)) = (m = n)) /\
            ((~(&m) = &n) = (m = 0) /\ (n = 0)) /\
            ((&m = ~(&n)) = (m = 0) /\ (n = 0))`,
      REWRITE_TAC[GSYM REAL_LE_ANTISYM, GSYM LE_ANTISYM] THEN
      REWRITE_TAC[pth_le1, pth_le2a, pth_le2b, pth_le3, LE, LE_0] THEN
      CONV_TAC tautLib.TAUT_CONV)
    val REAL_INT_EQ_CONV = FIRST_CONV
      [GEN_REWRITE_CONV I [pth_eq1a, pth_eq1b] THENC NEQ_CONV,
      GEN_REWRITE_CONV I [pth_eq2a, pth_eq2b] THENC NUM2_EQ_CONV]
  in
    (REAL_INT_LE_CONV,REAL_INT_LT_CONV,
    REAL_INT_GE_CONV,REAL_INT_GT_CONV,REAL_INT_EQ_CONV)
  end;

(* ------------------------------------------------------------------------- *)
(* Negation & multiplication.                                                *)
(* ------------------------------------------------------------------------- *)

val REAL_INT_NEG_CONV =
  let
    val pth = prove
      (``(~(&0) = &0) /\
         (~(~(&x)) = &x)``,
      REWRITE_TAC[REAL_NEG_NEG, REAL_NEG_0])
  in
    GEN_REWRITE_CONV I [pth]
  end;

val REAL_INT_MUL_CONV =
  let
    val pth0 = prove
      (``(&0 * &x = &0) /\
         (&0 * ~(&x) = &0) /\
         (&x * &0 = &0) /\
         (~(&x) * &0 = &0)``,
      REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO])
    val (pth1,pth2) = (CONJ_PAIR o prove)
      (``((&m * &n = &(m * n)) /\
         (~(&m) * ~(&n) = &(m * n))) /\
         ((~(&m) * &n = ~(&(m * n))) /\
         (&m * ~(&n) = ~(&(m * n))))``,
      REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL])
  in
    FIRST_CONV
    [GEN_REWRITE_CONV I [pth0],
    GEN_REWRITE_CONV I [pth1] THENC RAND_CONV MUL_CONV,
    GEN_REWRITE_CONV I [pth2] THENC RAND_CONV(RAND_CONV MUL_CONV)]
  end;

(* ------------------------------------------------------------------------- *)
(* Conversion to normalize product terms, i.e:                               *)
(*                                                                           *)
(* Separate out (and multiply out) integer constants, put the term in        *)
(* the form "([-]&n) * x" where either x is a canonically ordered product    *)
(* of the non-integer-constants, or is "&1".                                 *)
(* ------------------------------------------------------------------------- *)

val REAL_PROD_NORM_CONV =
  let
    val REAL_MUL_AC = AC REAL_MUL_AC_98
    val x_tm = ``x:real``
    val mul_tm = ``$* : real -> real -> real``
    val pth1 = SYM(SPEC x_tm REAL_MUL_RID)
    val pth2 = SYM(SPEC x_tm REAL_MUL_LID)
    val binops_mul = liteLib.binops mul_tm
    val list_mk_binop_mul = list_mk_binop mul_tm
    val mk_binop_mul = mk_binop mul_tm
  in
    fn tm =>
      let
        val _ = trace "REAL_PROD_NORM_CONV"
        val _ = trace_term tm
        val factors = binops_mul tm
        val (consts,others) = partition is_intconst factors
        val res =
        if others = [] then
          let
            val th1 = QCONV (DEPTH_CONV REAL_INT_MUL_CONV) tm
          in
            TRANS th1 (INST [(rand(concl th1),x_tm)] pth1)
          end
        else
          let
            val sothers = sort term_lt others
          in
            if consts = [] then
              let
                val t = mk_eq (tm, list_mk_binop_mul sothers)
                val th1 = REAL_MUL_AC t
              in
                TRANS th1 (INST [(rand(concl th1),x_tm)] pth2)
              end
            else
              let
                val th1 = REAL_MUL_AC
                  (mk_eq(tm,mk_binop_mul(list_mk_binop_mul consts)
                           (list_mk_binop_mul sothers)))
                val tm1 = rand(concl th1)
                val th2 = AP_TERM mul_tm (QCONV (DEPTH_CONV REAL_INT_MUL_CONV)
                                                (liteLib.lhand tm1))
              in
                TRANS th1 (AP_THM th2 (rand tm1))
              end
          end
        val _ = trace_thm res
        val _ = trace "done REAL_PROD_NORM_CONV"
      in
        res
      end
  end;

(* ------------------------------------------------------------------------- *)
(* Addition and subtraction.                                                 *)
(* ------------------------------------------------------------------------- *)

val REAL_INT_ADD_CONV =
  let
    val neg_tm = ``$~ :real->real``
    val amp_tm = ``(&)``
    val add_tm = ``$+ : real -> real -> real``
    val dest = liteLib.dest_binop add_tm
    val m_tm = ``m:num`` and n_tm = ``n:num``
    val pth0 = prove
      (``(~(&m) + &m = &0) /\
         (&m + ~(&m) = &0)``,
      REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_RINV])
    val [pth1, pth2, pth3, pth4, pth5, pth6] = (CONJUNCTS o prove)
      (``(~(&m) + ~(&n) = ~(&(m + n))) /\
         (~(&m) + &(m + n) = &n) /\
         (~(&(m + n)) + &m = ~(&n)) /\
         (&(m + n) + ~(&m) = &n) /\
         (&m + ~(&(m + n)) = ~(&n)) /\
         (&m + &n = &(m + n))``,
      REWRITE_TAC[GSYM REAL_ADD, REAL_NEG_ADD] THEN
      REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID] THEN
      REWRITE_TAC[REAL_ADD_RINV, REAL_ADD_LID] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID] THEN
      REWRITE_TAC[REAL_ADD_RINV, REAL_ADD_LID])
  in
    GEN_REWRITE_CONV I [pth0] ORELSEC
    (fn tm =>
      let
        val (l,r) = dest tm
      in
        if rator l = neg_tm then
          if rator r = neg_tm then
            let
              val th1 = INST [(rand(rand l),m_tm), (rand(rand r),n_tm)] pth1
              val tm1 = rand(rand(rand(concl th1)))
              val th2 = AP_TERM neg_tm (AP_TERM amp_tm (NUM_ADD_CONV tm1))
            in
              TRANS th1 th2
            end
          else
            let
              val m = rand(rand l)
              val n = rand r
              val m' = dest_numeral m
              val n' = dest_numeral n
            in
              if m' <= n' then
                let
                  val p = mk_numeral (n' - m')
                  val th1 = INST [(m,m_tm), (p,n_tm)] pth2
                  val th2 = NUM_ADD_CONV (rand(rand(liteLib.lhand(concl th1))))
                  val th3 = AP_TERM (rator tm) (AP_TERM amp_tm (SYM th2))
                in
                  TRANS th3 th1
                end
              else
                let
                  val p = mk_numeral (m' - n')
                  val th1 = INST [(n,m_tm), (p,n_tm)] pth3
                  val th2 = NUM_ADD_CONV
                              (rand(rand(liteLib.lhand
                                   (liteLib.lhand(concl th1)))))
                  val th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2))
                  val th4 = AP_THM (AP_TERM add_tm th3) (rand tm)
                in
                  TRANS th4 th1
                end
            end
        else
          if rator r = neg_tm then
            let
              val m = rand l and n = rand(rand r)
              val m' = dest_numeral m and n' = dest_numeral n
            in
              if n' <= m' then
                let
                  val p = mk_numeral (m' - n')
                  val th1 = INST [(n,m_tm), (p,n_tm)] pth4
                  val th2 = NUM_ADD_CONV (rand(liteLib.lhand(liteLib.lhand(concl th1))))
                  val th3 = AP_TERM add_tm (AP_TERM amp_tm (SYM th2))
                  val th4 = AP_THM th3 (rand tm)
                in
                  TRANS th4 th1
                end
              else
                let
                  val p = mk_numeral (n' - m')
                  val th1 = INST [(m,m_tm), (p,n_tm)] pth5
                  val th2 = NUM_ADD_CONV (rand(rand(rand(liteLib.lhand(concl th1)))))
                  val th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2))
                  val th4 = AP_TERM (rator tm) th3
                in
                  TRANS th4 th1
                end
            end
          else
            let
              val th1 = INST [(rand l,m_tm), (rand r,n_tm)] pth6
              val tm1 = rand(rand(concl th1))
              val th2 = AP_TERM amp_tm (NUM_ADD_CONV tm1)
            in
              TRANS th1 th2
            end
      end
      handle HOL_ERR _ => failwith "REAL_INT_ADD_CONV")
  end;

(* ------------------------------------------------------------------------- *)
(* Add together canonically ordered standard linear lists.                   *)
(* ------------------------------------------------------------------------- *)

val LINEAR_ADD =
  let
    val pth0a = prove
      (``&0 + x = x``,
      REWRITE_TAC[REAL_ADD_LID])
    val pth0b = prove
      (``x + &0 = x``,
      REWRITE_TAC[REAL_ADD_RID])
    val x_tm = ``x:real``
    val [pth1, pth2, pth3, pth4, pth5, pth6] = (CONJUNCTS o prove)
      (``((l1 + r1) + (l2 + r2) = (l1 + l2) + (r1 + r2):real) /\
      ((l1 + r1) + tm2 = l1 + (r1 + tm2):real) /\
      (tm1 + (l2 + r2) = l2 + (tm1 + r2)) /\
      ((l1 + r1) + tm2 = (l1 + tm2) + r1) /\
      (tm1 + tm2 = tm2 + tm1) /\
      (tm1 + (l2 + r2) = (tm1 + l2) + r2)``,
(REPEAT CONJ_TAC
   THEN REWRITE_TAC[realTheory.REAL_ADD_ASSOC]
   THEN TRY (MATCH_ACCEPT_TAC realTheory.REAL_ADD_SYM) THENL
   [REWRITE_TAC[GSYM realTheory.REAL_ADD_ASSOC] THEN AP_TERM_TAC
      THEN ONCE_REWRITE_TAC [realTheory.REAL_ADD_SYM]
      THEN Rewrite.GEN_REWRITE_TAC RAND_CONV
               Rewrite.empty_rewrites [realTheory.REAL_ADD_SYM]
      THEN REWRITE_TAC[GSYM realTheory.REAL_ADD_ASSOC] THEN AP_TERM_TAC
      THEN MATCH_ACCEPT_TAC realTheory.REAL_ADD_SYM,
    ONCE_REWRITE_TAC [realTheory.REAL_ADD_SYM] THEN AP_TERM_TAC
      THEN MATCH_ACCEPT_TAC realTheory.REAL_ADD_SYM,
    REWRITE_TAC[GSYM realTheory.REAL_ADD_ASSOC] THEN AP_TERM_TAC
      THEN MATCH_ACCEPT_TAC realTheory.REAL_ADD_SYM]))
    val tm1_tm = ``tm1:real``
    val l1_tm = ``l1:real``
    val r1_tm = ``r1:real``
    val tm2_tm = ``tm2:real``
    val l2_tm = ``l2:real``
    val r2_tm = ``r2:real``
    val add_tm = ``$+ :real->real->real``
    val dest = liteLib.dest_binop add_tm
    val mk = mk_binop add_tm
    val zero_tm = ``&0``
    val COEFF_CONV =
      QCONV (REWR_CONV (GSYM REAL_ADD_RDISTRIB) THENC
             LAND_CONV REAL_INT_ADD_CONV)
    fun linear_add tm1 tm2 =
    let
      val _ = trace "linear_add"
      val _ = trace_term tm1
      val _ = trace_term tm2
      val res =
      let
        val ltm = mk tm1 tm2
      in
        if tm1 = zero_tm then INST [(tm2,x_tm)] pth0a
        else if tm2 = zero_tm then INST [(tm1,x_tm)] pth0b else
          let
            val (l1,r1) = dest tm1
            val v1 = rand l1
            val _ = trace "v1 ="
            val _ = trace_term v1
          in
            let
              val (l2,r2) = dest tm2
              val v2 = rand l2
              val _ = trace "v2 ="
              val _ = trace_term v2
            in
              if aconv v1 v2 then
                let
                  val th1 = INST [(l1,l1_tm), (l2,l2_tm),
                                  (r1,r1_tm), (r2,r2_tm)] pth1
                  val th2 = CONV_RULE (RAND_CONV(LAND_CONV COEFF_CONV)) th1
                  val ctm = rator(rand(concl th2))
                in
                  TRANS th2 (AP_TERM ctm (linear_add r1 r2))
                end
                (* handle e as HOL_ERR => Raise e *)
              else if term_lt v1 v2 then
                let
                  val th1 = INST [(l1,l1_tm), (r1,r1_tm), (tm2,tm2_tm)] pth2
                  val ctm = rator(rand(concl th1))
                in
                  TRANS th1 (AP_TERM ctm (linear_add r1 tm2))
                end
              else
                let
                  val th1 = INST [(tm1,tm1_tm), (l2,l2_tm), (r2,r2_tm)] pth3
                  val ctm = rator(rand(concl th1))
                in
                  TRANS th1 (AP_TERM ctm (linear_add tm1 r2))
                end
            end
            handle HOL_ERR _ =>
              let
                val _ = trace "can't add_dest term2"
                val v2 = rand tm2
                val _ = trace "v2 ="
                val _ = trace_term v2
              in
                if aconv v1 v2 then
                  let
                    val th1 = INST [(l1,l1_tm), (r1,r1_tm), (tm2,tm2_tm)] pth4
                  in
                    CONV_RULE (RAND_CONV(LAND_CONV COEFF_CONV)) th1
                  end
                else if term_lt v1 v2 then
                  let
                    val th1 = INST [(l1,l1_tm), (r1,r1_tm), (tm2,tm2_tm)] pth2
                    val ctm = rator(rand(concl th1))
                  in
                    TRANS th1 (AP_TERM ctm (linear_add r1 tm2))
                  end
                else
                  INST [(tm1,tm1_tm), (tm2,tm2_tm)] pth5
              end
          end
          handle _ =>
            let
              val _ = trace "can't add_dest term1"
              val v1 = rand tm1
            in
              let
                val (l2,r2) = dest tm2
                val v2 = rand l2
              in
                if aconv v1 v2 then
                  let
                    val th1 = INST [(tm1,tm1_tm), (l2,l2_tm), (r2,r2_tm)] pth6
                  in
                    CONV_RULE (RAND_CONV(LAND_CONV COEFF_CONV)) th1
                  end
                else if term_lt v1 v2 then
                  REFL ltm
                else
                  let
                    val th1 = INST [(tm1,tm1_tm), (l2,l2_tm), (r2,r2_tm)] pth3
                    val ctm = rator(rand(concl th1))
                  in
                    TRANS th1 (AP_TERM ctm (linear_add tm1 r2))
                  end
              end
              handle _ =>
                let
                  val _ = trace "can't add_dest term2 either"
                  val v2 = rand tm2
                in
                  if aconv v1 v2 then
                    COEFF_CONV ltm
                  else if term_lt v1 v2 then
                    REFL ltm
                  else
                    INST [(tm1,tm1_tm), (tm2,tm2_tm)] pth5
                end
            end
      end
    val _ = trace_thm res
    val _ = trace "done linear_add"
  in
    res
  end
  in
    fn tm1 => fn tm2 =>
      let
        val _ = trace "LINEAR_ADD"
        val _ = trace_term tm1
        val _ = trace_term tm2
        val th = linear_add tm1 tm2
        val tm = rand(concl th)
        val zth =
            QCONV (GEN_REWRITE_CONV
                     DEPTH_CONV
                     [REAL_MUL_LZERO, REAL_ADD_LID, REAL_ADD_RID]) tm
        val res = TRANS th zth
        val _ = trace_thm res
        val _ = trace "done LINEAR_ADD"
      in
        res
      end
  end;

(* ------------------------------------------------------------------------- *)
(* Collection of like terms.                                                 *)
(* ------------------------------------------------------------------------- *)

val COLLECT_CONV =
  let
    val add_tm = ``$+ :real->real->real``
    val dest = liteLib.dest_binop add_tm
    fun collect tm =
      let
        val (l,r) = dest tm
        val lth = collect l
        val rth = collect r
        val xth = LINEAR_ADD (rand(concl lth)) (rand(concl rth))
      in
        TRANS (MK_COMB(AP_TERM add_tm lth,rth)) xth
      end
      handle HOL_ERR _ => REFL tm
  in
    collect
  end;

(* ------------------------------------------------------------------------- *)
(* Normalize a term in the standard linear form.                             *)
(* ------------------------------------------------------------------------- *)

val REAL_SUM_NORM_CONV =
  let
    val REAL_ADD_AC = AC REAL_ADD_AC_98
    val pth1 = prove (``~x = ~(&1) * x``,
                     REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_LID])
    val pth2 = prove (``x - y:real = x + ~(&1) * y``,
                     REWRITE_TAC[real_sub, GSYM pth1])
    val ptm = ``$~ :real->real``
    val stm = ``$+ :real->real->real``
    val one_tm = ``&1``
    val binops_add = liteLib.binops stm
    val list_mk_binop_add = list_mk_binop stm
    fun prelim_conv t =
      let
        val _ = trace "prelim_conv"
        fun c1 t = (trace "gen_rewrite 1";
                    trace_term t;
                    GEN_REWRITE_CONV I [pth1] t)
        fun c2 t = (trace "gen_rewrite 2";
                    trace_term t;
                    GEN_REWRITE_CONV I [pth2] t)
        fun c3 t = (trace "gen_rewrite 3"; trace_term t;
                    GEN_REWRITE_CONV TOP_DEPTH_CONV
                    [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] t)
        fun c4 t = (trace "gen_rewrite 4"; trace_term t;
                    GEN_REWRITE_CONV DEPTH_CONV
                    [REAL_MUL_LZERO, REAL_MUL_RZERO,
                    REAL_MUL_LID, REAL_MUL_RID,
                    REAL_ADD_LID, REAL_ADD_RID] t)
        val c = DEPTH_CONV((c1 o assert(fn t => not (rand t = one_tm)))
                ORELSEC c2) THENC c3 THENC c4
        val res = c t
        val _ = trace "done prelim_conv"
      in
        res
      end
  in
    fn tm =>
      let
        val _ = trace "REAL_SUM_NORM_CONV"
        val _ = trace_term tm
        val th1 = QCONV prelim_conv tm
        val th2 = liteLib.DEPTH_BINOP_CONV stm
                     (QCONV REAL_PROD_NORM_CONV) (rand(concl th1))
        val tm2 = rand(concl th2)
        val elements = binops_add tm2
        val selements = sort (fn x => fn y => term_le (rand x) (rand y))
                             elements
        val th3 = REAL_ADD_AC(mk_eq(tm2,list_mk_binop_add selements))
        val th4 = COLLECT_CONV (rand(concl th3))
        val res = itlist TRANS [th1, th2, th3] th4
        val _ = trace "done REAL_SUM_NORM_CONV"
      in
        res
      end
  end;

(* ------------------------------------------------------------------------- *)
(* Produce negated forms of canonicalization theorems.                       *)
(* ------------------------------------------------------------------------- *)

val REAL_NEGATE_CANON =
  let
    val pth1 = prove
      (``((a:real <= b = &0 <= X) = (b < a = &0 < ~X)) /\
         ((a:real < b = &0 < X) = (b <= a = &0 <= ~X))``,
      REWRITE_TAC[real_lt, REAL_LE_LNEG, REAL_LE_RNEG] THEN
      REWRITE_TAC[REAL_ADD_RID, REAL_ADD_LID] THEN
      CONV_TAC tautLib.TAUT_CONV)
    val pth2 = prove
      (``~((~a) * x + z) = a * x + ~z``,
      REWRITE_TAC[GSYM REAL_MUL_LNEG, REAL_NEG_ADD, REAL_NEG_NEG])
    val pth3 = prove
      (``~(a * x + z) = ~a * x + ~z``,
      REWRITE_TAC[REAL_NEG_ADD, GSYM REAL_MUL_LNEG])
    val pth4 = prove
      (``~(~a * x) = a * x``,
      REWRITE_TAC[REAL_MUL_LNEG, REAL_NEG_NEG])
    val pth5 = prove
      (``~(a * x) = ~a * x``,
      REWRITE_TAC[REAL_MUL_LNEG])
    val rewr1_CONV = FIRST_CONV (map REWR_CONV [pth2, pth3])
    val rewr2_CONV = FIRST_CONV (map REWR_CONV [pth4, pth5])
    fun distrib_neg_conv tm =
      let
        val _ = trace "distrib_neg_conv"
        val _ = trace_term tm
        val res =
          let
            val th = rewr1_CONV tm
            val _ = trace "ok so far"
            val t = rand (concl th)
            val _ = trace_term t
          in
            TRANS th (RAND_CONV distrib_neg_conv t)
          end
          handle HOL_ERR _ => rewr2_CONV tm
        val _ = trace "done distrib_neg_conv"
      in
        res
      end
  in
    fn th =>
      let
        val _ = trace "REAL_NEGATE_CANON"
        val _ = trace_thm th
        val th1 = GEN_REWRITE_RULE I [pth1] th
        val _ = trace_thm th1
        val t = rand (concl th1)
        val _ = trace_term t
        val res = TRANS th1 (RAND_CONV distrib_neg_conv t)
        val _ = trace "done REAL_NEGATE_CANON"
      in
        res
      end
  end;

(* ------------------------------------------------------------------------- *)
(* Version for whole atom, with intelligent cacheing.                        *)
(* ------------------------------------------------------------------------- *)

val (clear_atom_cache,REAL_ATOM_NORM_CONV) =
  let
    val right_CONV = RAND_CONV REAL_SUM_NORM_CONV
    val atomcache = ref []
    fun lookup_cache tm = find (fn th => liteLib.lhand(concl th) = tm) (!atomcache)
    fun clear_atom_cache () = (atomcache := [])
    val pth2 = prove
          (``(a:real < b = c < d:real) = (b <= a = d <= c)``,
          REWRITE_TAC[real_lt] THEN CONV_TAC tautLib.TAUT_CONV)
    val pth3 = prove
          (``(a:real <= b = c <= d:real) = (b < a = d < c)``,
          REWRITE_TAC[real_lt] THEN CONV_TAC tautLib.TAUT_CONV)
    val negate_CONV = GEN_REWRITE_CONV I [pth2,pth3]
    val le_tm = ``$<= :real->real->bool``
    val lt_tm = ``$< :real->real->bool``
  in
    (clear_atom_cache,
    fn tm => (trace "REAL_ATOM_NORM_CONV"; lookup_cache tm
    handle HOL_ERR _ =>
      let
        val th = right_CONV tm
      in
        (atomcache := th::(!atomcache);
        let
          val th' = REAL_NEGATE_CANON th
        in
          atomcache := th'::(!atomcache)
        end
        handle HOL_ERR _ => ();
        th)
      end))
  end;

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

infix F_F;
fun (f F_F g) (x, y) = (f x, g y);

(* ------------------------------------------------------------------------- *)
(* Replication and sequences.                                                *)
(* ------------------------------------------------------------------------- *)

fun upto n =
  let
    fun down l n = if n < zero then l else down (n::l) (n - one)
  in
    down [] n
  end;

(* ------------------------------------------------------------------------- *)
(* Encodings of linear inequalities with justifications.                     *)
(* ------------------------------------------------------------------------- *)

datatype lineq_type = Eq | Le | Lt;

datatype injust = Given of thm
                | Multiplied of int * injust
                | Added of injust * injust;

datatype lineq = Lineq of int * lineq_type * int list * injust;

fun injust_eq (Given t, Given t') = (dest_thm t = dest_thm t')
  | injust_eq (Multiplied (i,j), Multiplied (i',j')) =
      (i = i') andalso injust_eq (j,j')
  | injust_eq (Added (j1,j2), Added (j1',j2')) =
      injust_eq (j1,j1') andalso injust_eq (j2,j2')
  | injust_eq (j,j') = false;

fun lineq_eq (Lineq(i,t,l,j),Lineq(i',t',l',j')) =
  i = i' andalso t = t' andalso l = l' andalso injust_eq (j,j');

(* ------------------------------------------------------------------------- *)
(* The main refutation-finding code.                                         *)
(* ------------------------------------------------------------------------- *)

fun is_trivial (Lineq(_,_,l,_)) = forall ((curry op=) zero) l;

fun find_answer (ans as Lineq (k,ty,l,_)) =
  if ty = Eq andalso (not (k = zero))
    orelse ty = Le andalso k > zero
    orelse ty = Lt andalso k >= zero
  then
    ans
  else
    failwith "find_answer";

fun calc_blowup l =
  let
    val (p,n) = partition ((curry op<) zero) (filter ((curry op<>) zero) l)
  in
    (fromInt (length p)) * (fromInt (length n))
  end;

(* ------------------------------------------------------------------------- *)
(* "Set" operations on lists.                                                *)
(* ------------------------------------------------------------------------- *)

fun union l1 l2 = itlist insert l1 l2;

fun Union l = itlist union l [];

(* ------------------------------------------------------------------------- *)
(* GCD and LCM.                                                              *)
(* ------------------------------------------------------------------------- *)

fun abs x = if x < zero then ~x else x;

fun sgn x = x >= zero;

val gcd =
  let
    fun gxd x y =
      if y = zero then x else gxd y (x mod y)
  in
    fn x => fn y => if x < y then gxd y x else gxd x y
  end;

fun lcm x y = (x * y) div gcd x y;

(* ------------------------------------------------------------------------- *)
(* Calculate new (in)equality type after addition.                           *)
(* ------------------------------------------------------------------------- *)

val find_add_type =
  fn (Eq,x) => x
    | (x,Eq) => x
    | (_,Lt) => Lt
    | (Lt,_) => Lt
    | (Le,Le) => Le;

(* ------------------------------------------------------------------------- *)
(* Add together (in)equations.                                               *)
(* ------------------------------------------------------------------------- *)

fun add_ineq (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let
    val l = map2 (curry op+) l1 l2
  in
    Lineq(k1+k2,find_add_type(ty1,ty2),l,Added(just1,just2))
  end;

(* ------------------------------------------------------------------------- *)
(* Multiply out an (in)equation.                                             *)
(* ------------------------------------------------------------------------- *)

fun multiply_ineq n (i as Lineq(k,ty,l,just)) =
  if n = one then i
  else if n = zero andalso ty = Lt then failwith "multiply_ineq"
  else if n < zero andalso (ty = Le orelse ty = Lt) then
    failwith "multiply_ineq"
  else Lineq(n * k,ty,map ((curry op* ) n) l,Multiplied(n,just));

(* ------------------------------------------------------------------------- *)
(* Elimination of variable between a single pair of (in)equations.           *)
(* If they're both inequalities, 1st coefficient must be +ve, 2nd -ve.       *)
(* ------------------------------------------------------------------------- *)

fun elim_var v (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let
    val c1 = el0 v l1
    val c2 = el0 v l2
    val m = lcm (abs c1) (abs c2)
    val m1 = m div (abs c1)
    val m2 = m div (abs c2)
    val (n1,n2) =
      if sgn(c1) = sgn(c2)
      then if ty1 = Eq
           then (~m1,m2)
           else if ty2 = Eq
                then (m1,~m2)
                else failwith "elim_var"
      else (m1,m2)
    val (p1,p2) =
      if ty1 = Eq andalso ty2 = Eq andalso (n1 = ~one orelse n2 = ~one)
      then (~n1,~n2)
      else (n1,n2)
  in
    add_ineq (multiply_ineq n1 i1) (multiply_ineq n2 i2)
  end;

(* ------------------------------------------------------------------------- *)
(* All pairs arising from applying a function over two lists.                *)
(* ------------------------------------------------------------------------- *)

fun allpairs f l1 l2 = itlist (union o C map l2 o f) l1 [];
fun op_allpairs eq f l1 l2 = itlist ((op_union eq) o C map l2 o f) l1 [];

(* ------------------------------------------------------------------------- *)
(* Main elimination code:                                                    *)
(*                                                                           *)
(* (1) Looks for immediate solutions (false assertions with no variables).   *)
(*                                                                           *)
(* (2) If there are any equations, picks a variable with the lowest absolute *)
(* coefficient in any of them, and uses it to eliminate.                     *)
(*                                                                           *)
(* (3) Otherwise, chooses a variable in the inequality to minimize the       *)
(* blowup (number of consequences generated) and eliminates it.              *)
(* ------------------------------------------------------------------------- *)

fun elim ineqs =
  let
    val _ = trace ("elim: #(ineqs) = " ^ (Int.toString (length ineqs)) ^ ".")
    val (triv,nontriv) = partition is_trivial ineqs
    val res =
      if not (null triv) then tryfind find_answer triv
                              handle HOL_ERR _ => elim nontriv
      else
        if null nontriv then failwith "elim" else
          let
            val (eqs,noneqs) = partition (fn (Lineq(_,ty,_,_)) => ty = Eq)
                                         nontriv
          in
            if not (null eqs) then
              let
                val clists = map (fn (Lineq(_,_,l,_)) => l) eqs
                val sclist = sort (fn x => fn y => abs(x) <= abs(y))
                  (filter ((curry op<>) zero) (Union clists))
                val _ = trace ("elim: #(sclist) = "
                               ^ (Int.toString (length sclist)) ^ ".")
                val c = hd sclist
                val (v,eq) = tryfind
                              (fn (i as Lineq(_,_,l,_)) => (index c l,i)) eqs
                val othereqs = filter (not o ((curry lineq_eq) eq)) eqs
                val (ioth,roth) =
                        partition (fn (Lineq(_,_,l,_)) => el0 v l = zero)
                                  (othereqs @ noneqs)
                val others = map (elim_var v eq) roth @ ioth
              in
                elim others
              end
            else
              let
                val lists = map (fn (Lineq(_,_,l,_)) => l) noneqs
                val _ = trace ("elim: #(lists) = "
                               ^ (Int.toString (length lists)) ^ ".")
                val numlist = upto (fromInt (length(hd lists)) - one)
                val coeffs = map (fn i => map (el0 i) lists) numlist
                val blows = map calc_blowup coeffs
                val iblows = zip blows numlist
                val _ = trace ("elim: #(iblows) = "
                               ^ (Int.toString (length iblows)) ^ ".")
                val iblows' = filter ((curry op<>) zero o fst) iblows
                val _ = trace ("elim: #(iblows') = "
                               ^ (Int.toString (length iblows')) ^ ".")
                val (c,v) = Lib.trye hd
                             (sort (fn x => fn y => fst(x) <= fst(y)) iblows')
                val (no,yes) = partition
                                 (fn (Lineq(_,_,l,_)) => el0 v l = zero) ineqs
                val (pos,neg) = partition
                                  (fn (Lineq(_,_,l,_)) => el0 v l > zero) yes
              in
                elim (no @ op_allpairs (curry lineq_eq) (elim_var v) pos neg)
              end
          end
    val _ = trace "done elim"
  in
    res
  end


(* ------------------------------------------------------------------------- *)
(* Multiply standard linear list by a constant.                              *)
(* ------------------------------------------------------------------------- *)

val LINEAR_MULT =
  let
    val mult_tm = ``$* :real->real->real``
    val zero_tm = ``&0``
    val x_tm = ``x:real``
    val add_tm = ``$+ :real->real->real``
    val pth = prove
      (``x * &0 = &0``,
      REWRITE_TAC[REAL_MUL_RZERO])
    val conv1 = GEN_REWRITE_CONV TOP_SWEEP_CONV [REAL_ADD_LDISTRIB]
    val conv2 = liteLib.DEPTH_BINOP_CONV add_tm
                  (REWR_CONV REAL_MUL_ASSOC THENC LAND_CONV REAL_INT_MUL_CONV)
  in
    fn n => fn tm =>
      if tm = zero_tm then INST [(n,x_tm)] pth else
        let
          val ltm = mk_comb(mk_comb(mult_tm,n),tm)
        in
          (conv1 THENC conv2) ltm
        end
  end;

(* ------------------------------------------------------------------------- *)
(* Translate back a proof.                                                   *)
(* ------------------------------------------------------------------------- *)

val REAL_LT_LADD_IMP = prove(
  ``!x y z:real. y < z ==> x + y < x + z``,
  ACCEPT_TAC (((GEN ``x:real``)
               o (GEN ``y:real``)
               o (GEN ``z:real``)
               o fst
               o EQ_IMP_RULE
               o SPEC_ALL
               o GSYM)
              REAL_LT_LADD));

fun op_assoc eq x [] = failwith "op_assoc: mapping does not exist"
  | op_assoc eq x ((x',y')::t) = if eq x x' then (x',y') else op_assoc eq x t;

val TRANSLATE_PROOF =
  let
    val TRIVIAL_CONV = DEPTH_CONV
      (CHANGED_CONV REAL_INT_NEG_CONV ORELSEC
      REAL_INT_ADD_CONV ORELSEC
      REAL_INT_MUL_CONV ORELSEC
      REAL_INT_LE_CONV ORELSEC
      REAL_INT_EQ_CONV ORELSEC
      REAL_INT_LT_CONV) THENC
      GEN_REWRITE_CONV TOP_DEPTH_CONV (implicit_rewrites())

    val ADD_INEQS =
      let
        val a_tm = ``a:real``
        val b_tm = ``b:real``
        val pths = (CONJUNCTS o prove)
          (``((&0 = a) /\ (&0 = b) ==> (&0 = a + b)) /\
             ((&0 = a) /\ (&0 <= b) ==> (&0 <= a + b)) /\
             ((&0 = a) /\ (&0 < b) ==> (&0 < a + b)) /\
             ((&0 <= a) /\ (&0 = b) ==> (&0 <= a + b)) /\
             ((&0 <= a) /\ (&0 <= b) ==> (&0 <= a + b)) /\
             ((&0 <= a) /\ (&0 < b) ==> (&0 < a + b)) /\
             ((&0 < a) /\ (&0 = b) ==> (&0 < a + b)) /\
             ((&0 < a) /\ (&0 <= b) ==> (&0 < a + b)) /\
             ((&0 < a) /\ (&0 < b) ==> (&0 < a + b))``,
          CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
          REPEAT STRIP_TAC THEN
          ASM_REWRITE_TAC[REAL_ADD_LID, REAL_ADD_RID] THENL
          [MATCH_MP_TAC REAL_LE_TRANS,
          MATCH_MP_TAC REAL_LET_TRANS,
          MATCH_MP_TAC REAL_LTE_TRANS,
          MATCH_MP_TAC REAL_LT_TRANS] THEN
          EXISTS_TAC ``a:real`` THEN ASM_REWRITE_TAC[] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
           (MATCH_MP_TAC REAL_LE_LADD_IMP ORELSE MATCH_MP_TAC REAL_LT_LADD_IMP)
          THEN ASM_REWRITE_TAC[])
      in
        fn th1 => fn th2 =>
          let
            val a = rand(concl th1)
            val b = rand(concl th2)
            val xth = tryfind
                       (C MP (CONJ th1 th2) o INST [(a,a_tm), (b,b_tm)]) pths
            val yth = LINEAR_ADD a b
          in
            EQ_MP (AP_TERM (rator(concl xth)) yth) xth
          end
      end
    val MULTIPLY_INEQS =
      let
        val pths = (CONJUNCTS o prove)
          (``((&0 = y) ==> (&0 = x * y)) /\
             (&0 <= y ==> &0 <= x ==> &0 <= x * y) /\
             (&0 < y ==> &0 < x ==> &0 < x * y)``,
          CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THENL
          [MATCH_MP_TAC REAL_LE_MUL,
          MATCH_MP_TAC REAL_LT_MUL] THEN
          ASM_REWRITE_TAC[])
        val x_tm = ``x:real``
        val y_tm = ``y:real``
      in
        fn x => fn th =>
          let
            val y = rand(concl th)
            val xth = tryfind (C MP th o INST[(x,x_tm), (y,y_tm)]) pths
            val wth = if is_imp(concl xth) then
              MP (CONV_RULE(LAND_CONV TRIVIAL_CONV) xth) TRUTH else xth
            val yth = LINEAR_MULT x (rand(rand(concl wth)))
          in
            EQ_MP (AP_TERM (rator(concl wth)) yth) wth
          end
      end
  in
    fn refutation =>
      let
        val _ = trace "TRANSLATE_PROOF"
        val cache = ref []
        fun translate refut =
          snd (op_assoc (curry injust_eq) refut (!cache))
          handle HOL_ERR _
          => case refut
              of Given(th) => (cache:= (refut,th)::(!cache); th)
               | Added(r1,r2) =>
                  let
                    val th1 = translate r1
                    val _ = trace_thm th1
                    val th2 = translate r2
                    val _ = trace_thm th2
                    val th = ADD_INEQS th1 th2
                    val _ = trace_thm th
                  in
                   (cache:= (refut,th)::(!cache); th)
                  end
               | Multiplied(n,r) =>
                  let
                    val th1 = translate r
                    val th = MULTIPLY_INEQS (mk_intconst n) th1
                  in
                    (cache:= (refut,th)::(!cache); th)
                  end
        val res = CONV_RULE TRIVIAL_CONV (translate refutation)
        val _ = trace "done TRANSLATE_PROOF"
      in
        res
      end
  end;

(* ------------------------------------------------------------------------- *)
(* Refute a conjunction of equations and/or inequations.                     *)
(* ------------------------------------------------------------------------- *)

val REAL_SIMPLE_ARITH_REFUTER =
  let
    val trivthm = prove(``&0 < &0 = F``, REWRITE_TAC[REAL_LE_REFL, real_lt])
    val add_tm = ``$+ :real->real->real``
    val one_tm = ``&1``
    val zero_tm = ``&0``
    val less_tm = ``$< :real->real->bool``
    val false_tm = ``F``
    fun fixup_atom th =
      let
        val _ = trace "fixup_atom"
        val _ = trace_term (snd (dest_thm th))
        val th0 = CONV_RULE REAL_ATOM_NORM_CONV th
        val _ = trace_thm th0
        val tm0 = concl th0
      in
        if rand tm0 = zero_tm then
          if rator(rator tm0) = less_tm then EQ_MP trivthm th0
          else failwith "trivially true, so useless in refutation"
        else th0
      end
    val eq_tm = ``$= :real->real->bool``
    val le_tm = ``$<= :real->real->bool``
    val lt_tm = ``$< :real->real->bool``
  in
    fn ths0 =>
      let
        val _ = trace "REAL_SIMPLE_ARITH_REFUTER"
        val _ = trace ("#(ths0) = " ^ (Int.toString (length ths0)) ^ ".")
        val _ = trace_thm_list ths0
        val ths = mapfilter fixup_atom ths0
        val _ = trace ("#(ths) = " ^ (Int.toString (length ths)) ^ ".")
        val _ = trace_thm_list ths
        val res =
        find (fn th => concl th = false_tm) ths
        handle HOL_ERR _ =>
          let
            val allvars = itlist
              (op_union aconv o map rand o liteLib.binops add_tm o
               rand o concl) ths []
            val vars =
              if mem one_tm allvars then one_tm::subtract allvars [one_tm]
              else one_tm::allvars
            fun unthmify th =
              let
                val t = concl th
                val op_alt = rator(rator t)
                val right = rand t
                val rights = liteLib.binops add_tm right
                val cvps = map (((dest_intconst o rand)
                                 F_F (C index_ac vars)) o dest_comb) rights
                val k = ~((fst (rev_assoc zero cvps))
                                handle HOL_ERR _ => zero)
                val l = Lib.trye tl (map (fn v => (fst (rev_assoc v cvps)
                                                    handle HOL_ERR _ => zero))
                                    (upto (fromInt (length(vars)) - one)))
                val ty = if op_alt = eq_tm then Eq
                         else if op_alt = le_tm then Le
                         else if op_alt = lt_tm then Lt
                         else failwith "unknown op"
              in
                Lineq(k,ty,l,Given th)
              end
            val ineqs = map unthmify ths
            val _ = trace ("#(ineqs) = " ^ (Int.toString (length ineqs)) ^ ".")
            val (Lineq(_,_,_,proof)) = elim ineqs
          in
            TRANSLATE_PROOF proof
          end
        val _ = trace_thm res
        val _ = trace "done REAL_SIMPLE_ARITH_REFUTER"
      in
        res
      end
  end;

(* ------------------------------------------------------------------------- *)
(* General case: canonicalize and split up, then refute the bits.            *)
(* ------------------------------------------------------------------------- *)

val PURE_REAL_ARITH_TAC =
  let
    val ZERO_LEFT_CONV =
      let
        val pth = prove
          (``((x = y) = (&0 = y + ~x)) /\
             (x <= y = &0 <= y + ~x) /\
             (x < y = &0 < y + ~x)``,
           REWRITE_TAC[real_lt, GSYM REAL_LE_LNEG, REAL_LE_NEG2] THEN
           REWRITE_TAC[GSYM REAL_LE_RNEG, REAL_NEG_NEG] THEN
           REWRITE_TAC[GSYM REAL_LE_ANTISYM, GSYM REAL_LE_LNEG,
                       GSYM REAL_LE_RNEG, REAL_LE_NEG2, REAL_NEG_NEG])
        val zero_tm = ``&0``
      in
        let
          val raw_CONV = GEN_REWRITE_CONV I [pth] THENC
            GEN_REWRITE_CONV TOP_SWEEP_CONV
            [REAL_ADD_LID, REAL_NEG_ADD, REAL_NEG_NEG]
        in
          fn tm => if liteLib.lhand tm = zero_tm then REFL tm else raw_CONV tm
        end
      end
    val init_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV [
        FORALL_SIMP, EXISTS_SIMP,
        real_gt, real_ge, real_sub,
        REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB,
        REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG, REAL_NEG_ADD,
        REAL_MUL_LZERO, REAL_MUL_RZERO,
        REAL_MUL_LID, REAL_MUL_RID,
        REAL_ADD_LID, REAL_ADD_RID] THENC
        REPEATC (CHANGED_CONV Sub_and_cond.COND_ELIM_CONV) THENC PRENEX_CONV
    val eq_tm = ``$= :real->real->bool``
    val le_tm = ``$<= :real->real->bool``
    val lt_tm = ``$< :real->real->bool``
    val (ABS_ELIM_TAC1,ABS_ELIM_TAC2,ABS_ELIM_TAC3) =
      let
        val plus_tm = ``$+ :real->real->real``
        val abs_tm = ``abs:real->real``
        val neg_tm = ``$~: real->real``
        val strip_plus = liteLib.binops plus_tm
        val list_mk_plus = list_mk_binop plus_tm
        fun is_abstm tm = is_comb tm andalso rator tm = abs_tm
        fun is_negtm tm = is_comb tm andalso rator tm = neg_tm
        val REAL_ADD_AC = AC REAL_ADD_AC_98
        fun is_negabstm tm = is_negtm tm andalso is_abstm(rand tm)
        val ABS_ELIM_THM = prove (
         ``(&0 <= ~(abs(x)) + y = &0 <= x + y /\ &0 <= ~x + y) /\
           (&0 < ~(abs(x)) + y = &0 < x + y /\ &0 < ~x + y)``,
                    REWRITE_TAC[real_abs] THEN COND_CASES_TAC
                    THEN ASM_REWRITE_TAC[] THEN
                    REWRITE_TAC[REAL_NEG_NEG] THEN
                    REWRITE_TAC [
                      TAUT_PROVE ``(a = a /\ b) = (a ==> b)``,
                      TAUT_PROVE ``(b = a /\ b) = (b ==> a)``
                    ]
                    THEN REPEAT STRIP_TAC THEN
                    MAP_FIRST MATCH_MP_TAC [REAL_LE_TRANS, REAL_LTE_TRANS] THEN
                    FIRST_ASSUM(fn th => EXISTS_TAC(rand(concl th)) THEN
                    CONJ_TAC THENL [ACCEPT_TAC th, ALL_TAC]) THEN
                    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
                    MATCH_MP_TAC REAL_LE_LADD_IMP THEN
                    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ``&0`` THEN
                    REWRITE_TAC[REAL_LE_LNEG, REAL_LE_RNEG] THEN
                    ASM_REWRITE_TAC[REAL_ADD_RID, REAL_ADD_LID] THEN
                    MP_TAC (SPEC(Term`&0`) (SPEC (Term`x:real`) REAL_LE_TOTAL))
                    THEN ASM_REWRITE_TAC[])
        val ABS_ELIM_RULE = GEN_REWRITE_RULE I [ABS_ELIM_THM]
        val NEG_DISTRIB_RULE =
                      GEN_REWRITE_RULE (RAND_CONV o TOP_SWEEP_CONV)
                      [REAL_NEG_ADD, REAL_NEG_NEG]
        val REDISTRIB_RULE = CONV_RULE init_CONV
        val ABS_CASES_THM = prove
                        (``(abs(x) = x) \/ (abs(x) = ~x)``,
                        REWRITE_TAC[real_abs] THEN COND_CASES_TAC
                        THEN REWRITE_TAC[])
        val ABS_STRONG_CASES_THM = prove (
                        ``&0 <= x /\ (abs(x) = x) \/
                           (&0 <= ~x) /\ (abs(x) = ~x)``,
                        REWRITE_TAC[real_abs] THEN COND_CASES_TAC
                        THEN REWRITE_TAC[] THEN
                        REWRITE_TAC[REAL_LE_RNEG, REAL_ADD_LID] THEN
                        MP_TAC (SPEC(Term`&0`)
                                  (SPEC (Term`x:real`) REAL_LE_TOTAL))
                        THEN ASM_REWRITE_TAC[])
        val x_tm = ``x:real``
        fun ABS_ELIM_TAC1 th =
          let
            val (tmx,tm0) = dest_comb(concl th)
            val op_alt = rator tmx
          in
            (trace "ABS_ELIM_TAC1";
            if op_alt <> le_tm andalso op_alt <> lt_tm
            then failwith "ABS_ELIM_TAC1" else
              let
                val tms = strip_plus tm0
                val tm = find is_negabstm tms
                val n = index tm tms
                val (ltms,rtms) = chop_list n tms
                val ntms = tm::(ltms @ tl rtms)
                val th1 = AP_TERM tmx
                  (REAL_ADD_AC (mk_eq(tm0, list_mk_plus ntms)))
                val th2 = ABS_ELIM_RULE (EQ_MP th1 th)
              in
                CONJUNCTS_THEN ASSUME_TAC (NEG_DISTRIB_RULE th2)
              end)
          end
        fun ABS_ELIM_TAC2 th =
          let
            val (tmx,tm0) = dest_comb(concl th)
            val op_alt = rator tmx
          in
            (trace "ABS_ELIM_TAC2";
            if op_alt <> le_tm andalso op_alt <> lt_tm
            then failwith "ABS_ELIM_TAC1"
            else
              let
                val tms = strip_plus tm0
                val tm = find is_abstm tms
              in
                DISJ_CASES_THEN2
                (fn th => RULE_ASSUM_TAC (SUBS [th]))
                (fn th => RULE_ASSUM_TAC (NEG_DISTRIB_RULE o SUBS [th]))
                (INST [(rand tm,x_tm)] ABS_CASES_THM)
              end)
          end
        fun ABS_ELIM_TAC3 th =
          let
            val tm = find_term is_abstm (concl th)
          in
            (trace "ABS_ELIM_TAC2";
            DISJ_CASES_THEN2
            (CONJUNCTS_THEN2 ASSUME_TAC (fn th => RULE_ASSUM_TAC (SUBS [th])))
            (CONJUNCTS_THEN2 (ASSUME_TAC o REDISTRIB_RULE)
            (fn th => RULE_ASSUM_TAC (REDISTRIB_RULE o SUBS [th])))
            (INST [(rand tm,x_tm)] ABS_STRONG_CASES_THM))
          end
      in
        (ABS_ELIM_TAC1,ABS_ELIM_TAC2,ABS_ELIM_TAC3)
      end
    val atom_CONV =
      let
        val pth = prove
          (``(~(x:real <= y) = y < x) /\
             (~(x:real < y) = y <= x) /\
             (~(x = y) = (x:real) < y \/ y < x)``,
          REWRITE_TAC[real_lt] THEN REWRITE_TAC[GSYM DE_MORGAN_THM] THEN
          REWRITE_TAC[REAL_LE_ANTISYM] THEN AP_TERM_TAC THEN
          MATCH_ACCEPT_TAC EQ_SYM_EQ)
      in
        GEN_REWRITE_CONV I [pth]
      end
    fun DISCARD_UNREAL_TAC th =
      let
        val tm = concl th
      in
        if is_comb tm andalso
          let
            val tm' = rator tm
          in
            is_comb tm' andalso
            let
              val tm'' = rator tm'
            in
              tm'' = eq_tm orelse tm'' = le_tm orelse tm'' = lt_tm
            end
          end
        then failwith "DISCARD_UNREAL_TAC"
        else
          ALL_TAC
      end
  in
    fn g =>
      let
        val _ = trace "PURE_REAL_ARITH_TAC"
        val tac =
          REPEAT GEN_TAC THEN
          CONV_TAC init_CONV THEN
          REPEAT GEN_TAC THEN
          REFUTE_THEN(MP_TAC o
                      CONV_RULE
                        (PRESIMP_CONV THENC NNF_CONV THENC SKOLEM_CONV THENC
                         PRENEX_CONV THENC ONCE_DEPTH_CONV atom_CONV THENC
                         PROP_DNF_CONV)) THEN
          DISCH_THEN(REPEAT_TCL
                       (CHOOSE_THEN ORELSE_TCL DISJ_CASES_THEN ORELSE_TCL
                        CONJUNCTS_THEN)
                       ASSUME_TAC) THEN
          TRY(FIRST_ASSUM CONTR_TAC) THEN
          REPEAT(FIRST_X_ASSUM DISCARD_UNREAL_TAC) THEN
          RULE_ASSUM_TAC(CONV_RULE ZERO_LEFT_CONV) THEN
          REPEAT(FIRST_X_ASSUM ABS_ELIM_TAC1 ORELSE
                 FIRST_ASSUM ABS_ELIM_TAC2 ORELSE
                 FIRST_ASSUM ABS_ELIM_TAC3) THEN
          POP_ASSUM_LIST(ACCEPT_TAC o REAL_SIMPLE_ARITH_REFUTER)
        val res = tac g
        val _ = trace "done PURE_REAL_ARITH_TAC"
      in
        res
      end
  end;

fun REAL_ARITH_TAC g =
  let
    val _ = trace "REAL_ARITH_TAC"
    val res = (POP_ASSUM_LIST(K ALL_TAC) THEN PURE_REAL_ARITH_TAC) g
    val _ = trace "done REAL_ARITH_TAC"
  in
    res
  end;

fun REAL_ASM_ARITH_TAC g =
  let
    val _ = trace "REAL_ASM_ARITH_TAC"
    val res = (REPEAT (POP_ASSUM MP_TAC) THEN PURE_REAL_ARITH_TAC) g
    val _ = trace "done REAL_ASM_ARITH_TAC"
  in
    res
  end;

(* ------------------------------------------------------------------------- *)
(* Rule version.                                                             *)
(* ------------------------------------------------------------------------- *)

fun REAL_ARITH tm =
  let
    val _ = trace "REAL_ARITH"
    val res = Tactical.default_prover (tm,REAL_ARITH_TAC)
    val _ = trace "done REAL_ARITH"
  in
    res
  end;

(* ------------------------------------------------------------------------- *)

(*Terms to test the real linear decison procedure:
REAL_ARITH (Term`x + y:real = y + x`);
REAL_ARITH (Term`&0 < x ==> &0 <= x`);
REAL_ARITH (Term`x + ~x = &0`);
REAL_ARITH (Term`&0 <= x ==> &0 <= y ==> &0 <= x + y`);
REAL_ARITH (Term`&1 * x + &0 = x`);
REAL_ARITH (Term`&3 * x + &4 * x = &7 * x`);
REAL_ARITH (Term`&300 * x + &400 * x = &700 * x`);
REAL_ARITH (Term`x < y:real ==> x <= y`);
REAL_ARITH (Term`(x + z:real = y + z) ==> (x = y)`);
REAL_ARITH (Term`(x <= y:real /\ y <= z) ==> x <= z`);
REAL_ARITH (Term`x:real <= y ==> y < z ==> x < z`);
REAL_ARITH (Term`&0 < x /\ &0 < y ==> x + y < &1
               ==> &144 * x + &100 * y < &144`);
REAL_ARITH (Term`!x y. x <= ~y = x + y <= &0`);
*)

(*---------------------------------------------------------------------------*)
(* Restore the ambient grammar in force when this file started executing.    *)
(*---------------------------------------------------------------------------*)

val _ = Parse.temp_set_grammars ambient_grammars;

end;
