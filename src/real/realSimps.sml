(* ------------------------------------------------------------------------- *)
(* A real simpset (includes Peano arithmetic and pairs).                     *)
(* ------------------------------------------------------------------------- *)
structure realSimps :> realSimps =
struct

open HolKernel Parse boolLib realTheory simpLib realSyntax

(* Fix the grammar used by this file *)
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars realTheory.real_grammars
end

open Parse

val arith_ss = boolSimps.bool_ss ++ pairSimps.PAIR_ss ++ numSimps.ARITH_ss ++
               numSimps.REDUCE_ss

val SSFRAG = simpLib.register_frag o simpLib.SSFRAG

val real_SS = SSFRAG
  {name = SOME"real",
   ac = [],
   congs = [],
   convs = [],
   dprocs = [],
   filter = NONE,
   rewrs = map (fn s => (SOME {Thy = "real", Name = s}, DB.fetch "real" s)) [
     (* addition *)
     "REAL_ADD_LID", "REAL_ADD_RID",
     (* subtraction *)
     "REAL_SUB_REFL", "REAL_SUB_RZERO",
     (* multiplication *)
     "REAL_MUL_LID", "REAL_MUL_RID", "REAL_MUL_LZERO", "REAL_MUL_RZERO",
     (* division *)
     "REAL_OVER1", "REAL_DIV_ADD",
     (* less than or equal *)
     "REAL_LE_REFL", "REAL_LE_01", "REAL_LE_RADD",
     (* less than *)
     "REAL_LT_01", "REAL_LT_INV_EQ",
     (* pushing out negations *)
     "REAL_NEGNEG", "REAL_LE_NEG2", "REAL_SUB_RNEG", "REAL_NEG_SUB",
     "REAL_MUL_RNEG", "REAL_MUL_LNEG",
     (* cancellations *)
     "REAL_SUB_ADD2", "REAL_MUL_SUB1_CANCEL", "REAL_MUL_SUB2_CANCEL",
     "REAL_LE_SUB_CANCEL2", "REAL_ADD_SUB", "REAL_SUB_ADD", "REAL_ADD_SUB_ALT",
     "REAL_SUB_SUB2",
     (* halves *)
     "REAL_LT_HALF1", "REAL_HALF_BETWEEN", "REAL_NEG_HALF",
     "REAL_DIV_DENOM_CANCEL2", "REAL_DIV_INNER_CANCEL2",
     "REAL_DIV_OUTER_CANCEL2", "REAL_DIV_REFL2",
     (* thirds *)
     "REAL_NEG_THIRD", "REAL_DIV_DENOM_CANCEL3", "REAL_THIRDS_BETWEEN",
     "REAL_DIV_INNER_CANCEL3", "REAL_DIV_OUTER_CANCEL3", "REAL_DIV_REFL3",
     (* injections to the naturals *)
     "REAL_INJ", "REAL_ADD", "REAL_LE", "REAL_LT", "REAL_MUL",
     (* pos *)
     "REAL_POS_EQ_ZERO", "REAL_POS_POS", "REAL_POS_INFLATE",
     "REAL_POS_LE_ZERO",
     (* min *)
     "REAL_MIN_REFL", "REAL_MIN_LE1", "REAL_MIN_LE2", "REAL_MIN_ADD",
     "REAL_MIN_SUB",
     (* max *)
     "REAL_MAX_REFL", "REAL_LE_MAX1", "REAL_LE_MAX2", "REAL_MAX_ADD",
     "REAL_MAX_SUB"]};

val real_ac_SS = SSFRAG {
  name = SOME"real_ac",
  ac = [(SPEC_ALL REAL_ADD_ASSOC, SPEC_ALL REAL_ADD_SYM),
        (SPEC_ALL REAL_MUL_ASSOC, SPEC_ALL REAL_MUL_SYM)],
  convs = [],
  dprocs = [],
  filter = NONE,
  rewrs = [],
  congs = []};

(* ----------------------------------------------------------------------
    simple calculation over the reals
   ---------------------------------------------------------------------- *)

(* there are a whole bunch of theorems at the bottom of realScript designed
   to be used as calculational rewrites, but they are too general: with
   a rewrite with a LHS such as x * (y/z), you will get far too many rewrites
   happening.  Instead we need to specialise these variables so that the
   rewrites only apply when the variables look as if they're literals.

   To do this, we specialise with terms of the form &v and ~&v.
   We could go "the whole hog" here and further specialise the v's to be
   one of either NUMERAL (BIT1 v), NUMERAL (BIT2 v) or 0,
   but this seems over the top.
*)



val num_eq_0 = prove(
  Term`~(NUMERAL (BIT1 n) = 0n) /\ ~(NUMERAL (BIT2 n) = 0n)`,
  REWRITE_TAC [numeralTheory.numeral_distrib, numeralTheory.numeral_eq]);

fun two_nats  rv nv th = let
  open numSyntax
  val nb1_t = mk_injected (mk_comb(numeral_tm, mk_comb(bit1_tm, nv)))
  val nb2_t = mk_injected (mk_comb(numeral_tm, mk_comb(bit2_tm, nv)))
in
  [INST [rv |-> nb1_t] th, INST [rv |-> nb2_t] th]
end

fun posnegonly rv nv th = let
  val injected = mk_injected (mk_comb(numSyntax.numeral_tm, nv))
in
  [INST [rv |-> injected] th, INST [rv |-> mk_negated injected] th]
end

fun posneg0split rv nv th = let
  val injected = mk_injected (mk_comb(numSyntax.numeral_tm, nv))
in
  [INST [rv |-> realSyntax.zero_tm] th,
   INST [rv |-> injected] th, INST [rv |-> mk_negated injected] th]
end

datatype splitting = posneg | posneg0 | nb12

fun splitfn posneg = posnegonly
  | splitfn posneg0 = posneg0split
  | splitfn nb12 = two_nats

fun transform vs th = let
  val T_imp = hd (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
  val rwt =
      REWRITE_CONV ([REAL_INJ, REAL_NEGNEG, REAL_NEG_EQ0,
                     num_eq_0, REAL_LT, REAL_LE, REAL_DIV_LZERO,
                     REAL_MUL_RZERO, REAL_MUL_LZERO,
                     REAL_ADD_LID, REAL_ADD_RID,
                     arithmeticTheory.ZERO_LESS_EQ] @
                    (map (fn n => List.nth(CONJUNCTS le_int, n)) [1,3]))
  fun simp t = let
    val impconv = if is_imp t then LAND_CONV rwt THENC REWR_CONV T_imp
                  else ALL_CONV
  in
    impconv THENC RAND_CONV rwt
  end t
  val nvs = map (fn (t,_) => mk_var(#1 (dest_var t), numSyntax.num)) vs

  fun recurse vs nvs th =
      if null vs then [th]
      else let
          val (v,split) = hd vs
          val nv = hd nvs
          val newths = map (CONV_RULE simp) (splitfn split v nv th)
        in
          List.concat (map (recurse (tl vs) (tl nvs)) newths)
        end
in
  recurse vs nvs th
end

val x = mk_var("x", real_ty)
val y = mk_var("y", real_ty)
val z = mk_var("z", real_ty)
val u = mk_var("u", real_ty)
val v = mk_var("v", real_ty)

val REAL_MUL_ASSOC' = GSYM REAL_MUL_ASSOC
val REAL_NEG_MINUS1' = GSYM REAL_NEG_MINUS1

val add_rats =
    transform [(x, posneg), (y, nb12), (u, posneg), (v, nb12)] add_rat
val add_ratls = transform [(x, posneg), (y,nb12), (z, posneg0)] add_ratl
val add_ratrs = transform [(x, posneg0), (y, posneg), (z, nb12)] add_ratr

val mult_rats =
    transform [(x,posneg), (y, nb12), (u, posneg), (v, nb12)] mult_rat
val mult_ratls = transform [(x, posneg), (y, nb12), (z, posneg0)] mult_ratl
val mult_ratrs = transform [(x, posneg0), (y, posneg), (z, nb12)] mult_ratr

val neg_ths = REAL_NEG_0 :: transform [(y, nb12)] neg_rat

val sub1 = SPECL [mk_div(x,y), mk_div(u,v)] real_sub
val sub1 = transform [(x, posneg), (y, nb12), (u, posneg), (v, nb12)] sub1
val sub2 = SPECL [x, mk_div(u,v)] real_sub
val sub2 = transform [(x, posneg0), (u, posneg), (v, nb12)] sub2
val sub3 = SPECL [mk_div(x,y), z] real_sub
val sub3 = transform [(x, posneg), (y, nb12), (z, posneg0)] sub3
val sub4 = transform [(x, posneg0), (y, posneg0)] (SPEC_ALL real_sub)

val div_rats = transform [(x, posneg), (y, nb12), (u, posneg), (v, nb12)] div_rat
val div_ratls = transform [(x, posneg), (y, nb12), (z, nb12)] div_ratl
val div_ratrs = transform [(x, posneg), (z, nb12), (y, posneg)] div_ratr
val div_eq_1 = transform [(x, nb12)] (SPEC_ALL REAL_DIV_REFL)

val max_ints = transform [(x, posneg0), (y, posneg0)] (SPEC_ALL max_def)
val min_ints = transform [(x, posneg0), (y, posneg0)] (SPEC_ALL min_def)
val max_rats =
    transform [(x, posneg), (y, nb12), (u, posneg), (v, nb12)]
              (SPECL [mk_div(x,y), mk_div(u,v)] max_def)
val max_ratls =
    transform [(x, posneg), (y, nb12), (u, posneg0)]
              (SPECL [mk_div(x,y), u] max_def)
val max_ratrs =
    transform [(x, posneg), (y, nb12), (u, posneg0)]
              (SPECL [u, mk_div(x,y)] max_def)
val min_rats =
    transform [(x, posneg), (y, nb12), (u, posneg), (v, nb12)]
              (SPECL [mk_div(x,y), mk_div(u,v)] min_def)
val min_ratls =
    transform [(x, posneg), (y, nb12), (u, posneg0)]
              (SPECL [mk_div(x,y), u] min_def)
val min_ratrs =
    transform [(x, posneg), (y, nb12), (u, posneg0)]
              (SPECL [u, mk_div(x,y)] min_def)

local
  val (a, b, c, d) =
    Lib.quadruple_of_list (Drule.CONJUNCTS realTheory.NUM_FLOOR_EQNS)
  val rule = REWRITE_RULE [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO, num_eq_0]
  val r1 = rule o Q.INST [`m` |-> `NUMERAL (BIT1 m)`]
  val r2 = rule o Q.INST [`m` |-> `NUMERAL (BIT2 m)`]
in
  val flr = Drule.LIST_CONJ [a, b, r1 c, r2 c, r1 d, r2 d]
end

val abs1 = SPEC (mk_div(x,y)) realTheory.abs
val abs1 = transform [(x,posneg), (y, nb12)] abs1
val abs2 = SPEC x realTheory.abs
val abs2 = transform [(x,posneg)] abs2

val n = mk_var("n", numSyntax.num)
val m = mk_var("m", numSyntax.num)
fun to_numeraln th = INST [n |-> mk_comb(numSyntax.numeral_tm, n),
                           m |-> mk_comb(numSyntax.numeral_tm, m)] th

val ltnb12 = TAC_PROOF(([], “0 < NUMERAL (BIT1 n) /\ 0 < NUMERAL (BIT2 n)”),
                       REWRITE_TAC[arithmeticTheory.NUMERAL_DEF,
                                   arithmeticTheory.BIT1,
                                   arithmeticTheory.BIT2,
                                   arithmeticTheory.ADD_CLAUSES,
                                   prim_recTheory.LESS_0])
val let_id = TAC_PROOF(([], “LET (\n. n) x = x”),
                       SIMP_TAC boolSimps.bool_ss [LET_THM])

val op_rwts =
  [to_numeraln mult_ints, to_numeraln add_ints, flr,
   REAL_DIV_LZERO, REAL_NEGNEG] @
  (transform [(x,posneg)] $ SPEC x NUM_CEILING_NUM_FLOOR) @
  (transform [(x,posneg), (y,nb12)] (
    SPEC (mk_div(x,y)) NUM_CEILING_NUM_FLOOR)
             |> map (SIMP_RULE arith_ss [REAL_LE_LDIV_EQ, REAL_LT, REAL_LE,
                                         REAL_MUL_LZERO, REAL_NEG_LE0,
                                         ltnb12, flr, let_id])) @

   transform [(x,posneg0)] (SPEC_ALL REAL_ADD_LID) @
   transform [(x,posneg)] (SPEC_ALL REAL_ADD_RID) @
   transform [(x,posneg0)] (SPEC_ALL REAL_MUL_LZERO) @
   transform [(x,posneg)] (SPEC_ALL REAL_MUL_RZERO) @
   neg_ths @
   add_rats @ add_ratls @ add_ratrs @
   mult_rats @ mult_ratls @ mult_ratrs @
   sub1 @ sub2 @ sub3 @ sub4 @
   div_rats @ div_ratls @ div_ratrs @ div_eq_1 @
   max_ratls @ max_ratrs @ max_rats @ max_ints @
   min_ratls @ min_ratrs @ min_rats @ min_ints @
   (realTheory.REAL_ABS_0 :: abs1) @ abs2

fun nat2nat th = let
  val simp = REWRITE_RULE [REAL_INJ, REAL_NEGNEG, REAL_NEG_EQ0, num_eq_0]
  val th0 =
      if free_in ``n:num`` (concl th) then
        map simp ([INST [``n:num`` |-> ``NUMERAL (BIT1 n)``] th,
                   INST [``n:num`` |-> ``NUMERAL (BIT2 n)``] th])
      else [th]
in
  if free_in ``m:num`` (concl th) then
    List.concat
      (map (fn th => map simp
                         [INST [``m:num`` |-> ``NUMERAL(BIT1 m)``] th,
                          INST [``m:num`` |-> ``NUMERAL(BIT2 m)``] th])
           th0)
  else th0
end

val lt_rats =
    List.concat (map (transform [(x,posneg), (u,posneg)]) (nat2nat lt_rat))
val lt_ratls =
    List.concat (map (transform [(x,posneg), (u,posneg0)]) (nat2nat lt_ratl))
val lt_ratrs =
    List.concat (map (transform [(x,posneg0), (u,posneg)]) (nat2nat lt_ratr))

val le_rats =
    List.concat (map (transform [(x,posneg), (u,posneg)]) (nat2nat le_rat))
val le_ratls =
    List.concat (map (transform [(x,posneg), (u,posneg0)]) (nat2nat le_ratl))
val le_ratrs =
    List.concat (map (transform [(x,posneg0), (u,posneg)]) (nat2nat le_ratr))

val eq_rats = transform [(x, posneg), (y, nb12), (u, posneg), (v, nb12)] eq_rat
val eq_ratls = transform [(x, posneg), (y, nb12), (z, posneg0)] eq_ratl
val eq_ratrs = transform [(x, posneg), (y, nb12), (z, posneg0)] eq_ratr

val real_gts = transform [(x, posneg0), (y, posneg0)] (SPEC_ALL real_gt)
val real_ges = transform [(x, posneg0), (y, posneg0)] (SPEC_ALL real_ge)

val real_gt_rats =
    transform [(x, posneg), (y, nb12), (u, posneg), (v, nb12)]
              (SPECL [mk_div(x,y), mk_div(u,v)] real_gt)
val real_gt_ratls =
    transform [(x, posneg), (y, nb12), (u, posneg0)]
              (SPECL [mk_div(x,y), u] real_gt)
val real_gt_ratrs =
    transform [(x, posneg), (y, nb12), (u, posneg0)]
              (SPECL [u, mk_div(x,y)] real_gt)

val real_ge_rats =
    transform [(x, posneg), (y, nb12), (u, posneg), (v, nb12)]
              (SPECL [mk_div(x,y), mk_div(u,v)] real_ge)
val real_ge_ratls =
    transform [(x, posneg), (y, nb12), (u, posneg0)]
              (SPECL [mk_div(x,y), u] real_ge)
val real_ge_ratrs =
    transform [(x, posneg), (y, nb12), (u, posneg0)]
              (SPECL [u, mk_div(x,y)] real_ge)

val rel_rwts = [eq_ints, le_int, lt_int] @
               eq_rats @ eq_ratls @ eq_ratrs @
               lt_rats @ lt_ratls @ lt_ratrs @
               le_rats @ le_ratrs @ le_ratls @
               real_gts @ real_gt_rats @ real_gt_ratls @ real_gt_ratrs @
               real_ges @ real_ge_rats @ real_ge_ratls @ real_ge_ratrs

val rwts = pow_rat :: (op_rwts @ rel_rwts)

val n_compset = reduceLib.num_compset()
val _ = computeLib.add_thms (mult_ints:: mult_rats) n_compset

fun elim_common_factor t = let
  open realSyntax Arbint
  val (n,d) = dest_div t
  val n_i = int_of_term n
in
  if n_i = zero then REWR_CONV REAL_DIV_LZERO t
  else let
      val d_i = int_of_term d
      val _ = d_i > zero orelse
              raise mk_HOL_ERR "realSimps" "elim_common_factor"
                               "denominator must be positive"
      val g = fromNat (Arbnum.gcd (toNat (abs n_i), toNat (abs d_i)))
      val _ = g <> one orelse
              raise mk_HOL_ERR "realSimps" "elim_common_factor"
                               "No common factor"
      val frac_1 = mk_div(term_of_int g, term_of_int g)
      val frac_new_t = mk_div(term_of_int (n_i div g), term_of_int (d_i div g))
      val mul_t = mk_mult(frac_new_t, frac_1)
      val eqn1 = computeLib.CBV_CONV n_compset mul_t
      val frac_1_eq_1 = FIRST_CONV (map REWR_CONV div_eq_1) frac_1
      val eqn2 =
          TRANS (SYM eqn1) (AP_TERM(mk_comb(mult_tm, frac_new_t)) frac_1_eq_1)
    in
      CONV_RULE (RAND_CONV (REWR_CONV REAL_MUL_RID THENC
                            TRY_CONV (REWR_CONV REAL_OVER1)))
                eqn2
    end
end


val ecf_patterns = [Term`&(NUMERAL n) / &(NUMERAL (BIT1 m))`,
                    Term`&(NUMERAL n) / &(NUMERAL (BIT2 m))`,
                    Term`~&(NUMERAL n) / &(NUMERAL (BIT1 m))`,
                    Term`~&(NUMERAL n) / &(NUMERAL (BIT2 m))`]

val simpset_convs = map (fn p => {conv = K (K elim_common_factor),
                                  key = SOME ([], p),
                                  name = "realSimps.elim_common_factor",
                                  trace = 2}) ecf_patterns

val REAL_REDUCE_ss = SSFRAG
  {name = SOME "REAL_REDUCE",
   ac = [], congs =[],
   convs = simpset_convs,
   dprocs = [], filter = NONE,
   rewrs = map (fn th => (NONE, th)) rwts}

val real_ss = arith_ss ++ real_SS ++ REAL_REDUCE_ss

val real_ac_ss = real_ss ++ real_ac_SS

fun real_compset () = let
  open computeLib
  val compset = reduceLib.num_compset()
  val _ = add_thms rwts compset
  val _ = add_conv (div_tm, 2, elim_common_factor) compset
in
  compset
end

(* add real calculation facilities to global functionality *)
val _ = let open computeLib in
          add_funs rwts ;
          add_convs [(div_tm, 2, elim_common_factor)]
        end

val addfrags = BasicProvers.logged_addfrags {thyname = "real"}
val _ = addfrags [REAL_REDUCE_ss]

(* ----------------------------------------------------------------------
    REAL_ARITH_ss

    embedding RealArith into a simpset fragment.
    Derived from code to do the same for the natural numbers, which is in
      src/num/arith/src/numSimps.sml
    and
      src/num/arith/src/Gen_arith.sml
   ---------------------------------------------------------------------- *)

fun contains_var tm =
    if is_var tm then true
    else if is_real_literal tm then false
    else let
        val (l, r) = dest_plus tm
                     handle HOL_ERR _ =>
                            dest_mult tm
                            handle HOL_ERR _ => dest_minus tm
      in
          contains_var l orelse contains_var r
      end handle HOL_ERR _ => contains_var (dest_absval tm)
                              handle HOL_ERR _ => true
 (* final default value is true because the term in question must be a
    complicated non-presburger thing that will get treated as a variable
    anyway. *)

fun is_linear_mult tm = let
  val (l,r) = dest_mult tm
in
  not (contains_var l andalso contains_var r)
end

fun arg1 tm = rand (rator tm)
val arg2 = rand

fun non_presburger_subterms tm =
   (non_presburger_subterms (#2 (dest_forall tm))) handle _ =>
   (non_presburger_subterms (dest_neg tm)) handle _ =>
   (if (is_conj tm) orelse (is_disj tm) orelse (is_imp tm) orelse
       (is_eq tm) orelse
       (is_less tm) orelse (is_leq tm) orelse
       (is_greater tm) orelse (is_geq tm) orelse
       (is_plus tm) orelse (is_minus tm) orelse
       (is_linear_mult tm handle _ => false)
    then tunion (non_presburger_subterms (arg1 tm))
                (non_presburger_subterms (arg2 tm))
    else if (is_real_literal tm) then []
    else [tm]);

fun is_num_var tm = is_var tm andalso type_of tm = real_ty
val is_presburger = (all is_num_var) o non_presburger_subterms;



fun cond_has_arith_components tm =
  if boolSyntax.is_cond tm then let
    val {cond,rarm,larm} = Rsyntax.dest_cond tm
  in
    List.all is_arith [cond, rarm, larm]
  end
  else true
and is_arith tm =
    is_presburger tm orelse
    List.all (fn t => type_of t = real_ty andalso cond_has_arith_components t)
             (non_presburger_subterms tm)

fun contains_forall sense tm =
  if is_conj tm orelse is_disj tm then
    List.exists (contains_forall sense) (#2 (strip_comb tm))
  else if is_neg tm then
    contains_forall (not sense) (rand tm)
  else if is_imp tm then
    contains_forall (not sense) (rand (rator tm)) orelse
    contains_forall sense (rand tm)
  else if is_forall tm then
    sense orelse contains_forall sense (#2 (dest_forall tm))
  else if is_exists tm then
    not sense orelse contains_forall sense (#2 (dest_exists tm))
  else false

(* This function determines whether or not to add something as context
   to the arithmetic decision procedure.  Because the d.p. can't
   handle implications with nested foralls on the left hand side, we
   eliminate those here.  More generally, we can't allow the formula
   to be added to have any positive universals, because these will
   translate into negative ones in the context of the wider goal, and
   thus cause the goal to be rejected.  *)

fun is_arith_thm thm =
  not (null (hyp thm)) andalso is_arith (concl thm) andalso
   (not (contains_forall true (concl thm)));

val is_arith_asm = is_arith_thm o ASSUME

(* The old d.p. is faster *)
val ARITH = RealArith.OLD_REAL_ARITH

open Trace Cache Traverse
fun CTXT_ARITH thms tm = let
  val context = map concl thms
  fun try gl = let
    val gl' = list_mk_imp(context,gl)
    val _ = trace (5, LZ_TEXT (fn () => "Trying cached arithmetic d.p. on "^
                                        term_to_string gl'))
  in
    rev_itlist (C MP) thms (ARITH gl')
  end
  val thm = EQT_INTRO (try tm)
      handle (e as HOL_ERR _) =>
             if not (Feq tm) then EQF_INTRO (try(mk_neg tm)) else raise e
in
  trace(1,PRODUCE(tm,"REAL_ARITH",thm)); thm
end

fun crossprod (ll : 'a list list) : 'a list list =
    case ll of
      [] => [[]]
    | h::t => let
        val c = crossprod t
      in
        List.concat (map (fn hel => map (cons hel) c) h)
      end
fun prim_dest_const t = let
  val {Thy,Name,...} = dest_thy_const t
in
  (Thy,Name)
end

fun dpvars t = let
  fun recurse bnds acc t = let
    val (f, args) = strip_comb t
    fun go2() = let
      val (t1, t2) = (hd args, hd (tl args))
    in
      recurse bnds (recurse bnds acc t1) t2
    end
    fun go1 () = recurse bnds acc (hd args)
  in
    case Lib.total prim_dest_const f of
      SOME ("bool", "~") => go1()
    | SOME ("bool", "/\\") => go2()
    | SOME ("bool", "\\/") => go2()
    | SOME ("min", "==>") => go2()
    | SOME ("min", "=") => go2()
    | SOME ("bool", "COND") => let
        val (t1,t2,t3) = (hd args, hd (tl args), hd (tl (tl args)))
      in
        recurse bnds (recurse bnds (recurse bnds acc t1) t2) t3
      end
    | SOME ("realax", "real_add") => go2()
    | SOME ("realax", "real_sub") => go2()
    | SOME ("realax", "real_gt") => go2()
    | SOME ("realax", "real_lt") => go2()
    | SOME ("realax", "real_lte") => go2()
    | SOME ("realax", "real_ge") => go2()
    | SOME ("realax", "real_neg") => go1()
    | SOME ("realax", "abs") => go1()
    | SOME ("realax", "real_mul") => let
        val args = realSyntax.strip_mult t
        val arg_vs = map (HOLset.listItems o recurse bnds empty_tmset) args
        val cs = crossprod (filter (not o null) arg_vs)
        val var_ts = map (realSyntax.list_mk_mult o Listsort.sort Term.compare)
                         cs
      in
        List.foldl (fn (t,acc)=>HOLset.add(acc,t)) acc var_ts
      end
    | SOME ("bool", "!") => let
        val (v, bod) = dest_abs (hd args)
      in
        recurse (HOLset.add(bnds, v)) acc bod
      end
    | SOME ("bool", "?") => let
        val (v, bod) = dest_abs (hd args)
      in
        recurse (HOLset.add(bnds, v)) acc bod
      end
    | SOME _ => if realSyntax.is_real_literal t then acc
                else HOLset.add(acc, t)
    | NONE => if is_var t then if HOLset.member(bnds, t) then acc
                               else HOLset.add(acc, t)
              else HOLset.add(acc, t)
  end
in
  HOLset.listItems (recurse empty_tmset empty_tmset t)
end


val (CACHED_ARITH,arith_cache) = let
  fun check tm =
    let val ty = type_of tm
    in
       (ty=Type.bool andalso (is_arith tm orelse Feq tm))
    end;
in
  RCACHE (dpvars, check,CTXT_ARITH)
  (* the check function determines whether or not a term might be handled
     by the decision procedure -- we want to handle F, because it's possible
     that we have accumulated a contradictory context. *)
end;

val ARITH_REDUCER = let
  exception CTXT of thm list;
  fun get_ctxt e = (raise e) handle CTXT c => c
  fun add_ctxt(ctxt, newthms) = let
    val addthese = filter is_arith_thm (flatten (map CONJUNCTS newthms))
  in
    CTXT (addthese @ get_ctxt ctxt)
  end
in
  REDUCER {name = SOME"REAL_ARITH_DP",
           addcontext = add_ctxt,
           apply = fn args => CACHED_ARITH (get_ctxt (#context args)),
           initial = CTXT []}
end;

val REAL_ARITH_ss =
    SSFRAG
    {name=SOME"REAL_ARITH",
     convs = [], rewrs = [], congs = [],
      filter = NONE, ac = [], dprocs = [ARITH_REDUCER]};

open AC_Sort realTheory realSyntax

val literalbase = mk_var(" ", real_ty) (* compares less than 'normal' vars *)

fun oksort cmp [] = true
  | oksort cmp [_] = true
  | oksort cmp (t1::(rest as (t2::ts))) =
      cmp(t1,t2) = LESS andalso oksort cmp rest

val x_real = mk_var("x", real_ty)
val a_num = mk_var("a", numSyntax.num)
val b_num = mk_var("b", numSyntax.num)
val NUMERALa = mk_comb(numSyntax.numeral_tm, a_num)
val NUMERALb = mk_comb(numSyntax.numeral_tm, b_num)
val REAL_MUL_RID' = GSYM REAL_MUL_RID
val REAL_POW_ADD' = GSYM REAL_POW_ADD
val REAL_POW_INV' = GSYM REAL_POW_INV
val REAL_POW_INV_NUMERAL' =
    REAL_POW_INV' |> SPECL [x_real, NUMERALa] |> GENL [x_real, a_num]
val REAL_POW_POW_NUMERAL =
    REAL_POW_POW |> SPECL [x_real, NUMERALa, NUMERALb]
                 |> GENL [x_real, a_num, b_num]
val POW_1' = GSYM POW_1
val (NEG_FRAC, NEG_DENOM) = CONJ_PAIR neg_rat
val NEG_INV = REAL_NEG_INV'
val INV_1OVER = REAL_INV_1OVER
val NEG_MINUS1' = GSYM REAL_NEG_MINUS1
val neg1_t = mk_negated one_tm
val NEG1_MUL = SPEC neg1_t REAL_MUL_ASSOC
val Flor = OR_CLAUSES |> SPEC_ALL |> CONJUNCTS |> el 3

val realreduce_cs = real_compset()
fun REPORT_ALL_CONV t =
    ((*print ("\nGiving up on " ^ term_to_string t ^ "\n"); *) NO_CONV t)
val REAL_REDUCE =
    PURE_REWRITE_CONV [REAL_INV_1OVER] THENC computeLib.CBV_CONV realreduce_cs
val NUM_REDUCE = reduceLib.REDUCE_CONV

fun is_literalish t =
    is_real_literal t orelse
    case total dest_inv t of
        NONE => (case total dest_div t of
                     NONE => (case total dest_negated t of
                                  NONE => false
                                | SOME t0 => is_literalish t0)
                   | SOME (n,d) => is_literalish n andalso is_literalish d)
      | SOME t0 => is_literalish t0

val NORMLIT_phase1 =
    PURE_REWRITE_CONV [NEG_FRAC, NEG_DENOM, NEG_INV, REAL_NEGNEG, INV_1OVER]
val GCDELIM = REAL_REDUCE

fun is_real_posliteral t =
    is_real_literal t andalso not (is_negated t)
fun is_real_fraction t =
    is_real_literal t orelse
    case Exn.capture dest_div t of
        Exn.Res(n,d) =>
        is_real_literal n andalso is_real_literal d andalso
        not (is_negated d)
      | _ => false
fun REAL_LITCANON t = if is_literalish t then
                        if is_real_fraction t then raise UNCHANGED
                        else
                          (NORMLIT_phase1 THENC REAL_REDUCE) t
                      else NO_CONV t

val NZ_t = prim_mk_const{Thy = "real", Name = "nonzerop"}
fun is_NZ t = is_comb t andalso rator t ~~ NZ_t
fun mul_termbase t =
    if is_real_fraction t then (t, Arbint.one)
    else if is_negated t then
      let val (t0,c) = mul_termbase (dest_negated t)
      in (t0, c)
      end
    else if is_NZ t then (t, Arbint.one)
    else
      case total dest_pow t of
          NONE => (case total dest_inv t of
                       NONE => (t, Arbint.one)
                     | SOME t' => (t', Arbint.~ Arbint.one))
        | SOME (b0,e) =>
          (case total dest_inv b0 of
               NONE => if numSyntax.is_numeral e then
                         (b0, Arbint.fromNat (numSyntax.dest_numeral e))
                       else (t, Arbint.one)
             | SOME b =>
               if numSyntax.is_numeral e then
                 (b, Arbint.~ (Arbint.fromNat (numSyntax.dest_numeral e)))
               else (mk_pow(b,e), Arbint.~ Arbint.one))

fun litcompare(t1,t2) =
    if is_real_fraction t1 then
      if is_real_fraction t2 then EQUAL
      else LESS
    else if is_real_fraction t2 then GREATER
    else Term.compare(t1,t2)
local
  fun termbase t = #1 (mul_termbase t)
  (* puts the inverted term on the right *)
  fun powinv_fix t =
      let val (l,r) = dest_mult t
          val (lb,_) = dest_pow l
      in
        if is_inv lb then REWR_CONV REAL_MUL_COMM
        else ALL_CONV
      end t
  val normNZs = REWR_CONV nonzerop_mulXX

  val mulcompare = inv_img_cmp termbase litcompare

  val addPOW1 = REWR_CONV POW_1'
  val mulPOWs = TRY_CONV (REWR_CONV REAL_POW_POW THENC
                          RAND_CONV (REWR_CONV arithmeticTheory.MULT_RIGHT_1))
  val POW_E0 = CONJUNCT1 pow
  val (inv_th1, inv_th2) = CONJ_PAIR realTheory.REAL_INV_nonzerop
  fun compare_exponents t =
      let val (l,r) = dest_mult t
          val (e1,e2) = ((snd o dest_pow) ## (snd o dest_pow)) (l,r)
          val (m,n) = (numSyntax.dest_numeral ## numSyntax.dest_numeral) (e1,e2)
          val finish = RAND_CONV NUM_REDUCE
          val cth =
              if Arbnum.<(m,n) then
                MATCH_MP pow_inv_mul_powlt
                         (numSyntax.mk_less(e1,e2) |> NUM_REDUCE |> EQT_ELIM)
              else
                MATCH_MP pow_inv_mul_invlt
                         (numSyntax.mk_less(e2,e1) |> NUM_REDUCE |> EQT_ELIM)
      in
        REWR_CONV cth THENC finish
      end t
  val combine_exponents =
      (REWR_CONV (GSYM REAL_POW_ADD) THENC
       RAND_CONV (CHANGED_CONV (computeLib.CBV_CONV realreduce_cs))) ORELSEC
      (powinv_fix THENC (
          REWR_CONV pow_inv_eq ORELSEC
          compare_exponents ORELSEC
          REWR_CONV (GSYM POW_2) ORELSEC
          REPORT_ALL_CONV
      ))

  fun give_pow t =
      case total dest_pow t of
          NONE => addPOW1 t
        | SOME (b,e) => if numSyntax.is_numeral e then ALL_CONV t else addPOW1 t
  val mulcombine0 =
      BINOP_CONV give_pow THENC
      combine_exponents THENC
      TRY_CONV (FIRST_CONV (map REWR_CONV [POW_1, POW_E0]))
  fun mulcombine t =
      if is_real_fraction (rand t) then REAL_REDUCE t
      else (normNZs ORELSEC mulcombine0) t

  fun neg_nonnum_conv t =
      case total dest_negated t of
          NONE => ALL_CONV t
        | SOME t0 => if is_real_literal t0 then ALL_CONV t
                     else REWR_CONV REAL_NEG_MINUS1 t
  fun diag s c t = (print (s t ^ "\n"); c t)

  fun pow_inv_nonnumeral_out t =
      case total dest_pow t of
          SOME (b,e) => if numSyntax.is_numeral e then ALL_CONV t
                        else TRY_CONV (LAND_CONV pow_inv_nonnumeral_out THENC
                                       REWR_CONV REAL_POW_INV) t
        | NONE => ALL_CONV t
  val mulpre =
      REAL_LITCANON ORELSEC
      (REWRITE_CONV [REAL_POW_INV_NUMERAL', REAL_INV_INV,
                     REAL_POW_POW_NUMERAL] THENC
       pow_inv_nonnumeral_out THENC
       neg_nonnum_conv)

  val mulsort = {
    assoc = REAL_MUL_ASSOC,
    comm = REAL_MUL_COMM,
    dest = realSyntax.dest_mult,
    mk = realSyntax.mk_mult,
    cmp = mulcompare,
    combine = (* diag (fn t => "mulcombine on "^term_to_string t) *) mulcombine,
    preprocess = (* diag (fn t => "mulpre on "^term_to_string t)  *) mulpre
  }
  fun leading_coeff_norm leaveneg1 t =
      case total dest_mult t of
          SOME (l,r) => if is_real_fraction l then
                          (RAND_CONV (PURE_REWRITE_CONV [REAL_MUL_ASSOC]) THENC
                           (if leaveneg1 then ALL_CONV
                            else PURE_REWRITE_CONV [NEG1_MUL] THENC
                                 PURE_REWRITE_CONV [NEG_MINUS1'])) t
                        else PURE_REWRITE_CONV [REAL_MUL_ASSOC] t
        | _ => ALL_CONV t
  fun elim1div t =
      case total dest_div t of
          NONE => ALL_CONV t
        | SOME (l,r) => if is_real_literal l then
                          if is_real_literal r then
                            if is_negated r then REWR_CONV (cj 2 neg_rat) t
                            else ALL_CONV t
                          else REWR_CONV real_div t
                        else REWR_CONV real_div t
  fun elimdivs t =
      case total dest_mult t of
          SOME _ => BINOP_CONV elimdivs t
        | NONE => if is_div t then (BINOP_CONV elimdivs THENC elim1div) t
                  else ALL_CONV t
in
  fun REALMULCANON00 leaveneg1 t =
      let
        fun strip A t =
            case total dest_mult t of
                SOME(t1,t2) => strip (t2::A) t1
              | NONE => t::A
        val ((l,r),divp) = (dest_mult t, false) handle HOL_ERR _ =>
                           (dest_div t, true) handle HOL_ERR _ =>
                                                     raise UNCHANGED
        fun is_baddiv t =
            case Lib.total dest_div t of
                NONE => false
              | SOME (l,r) => not (is_real_literal l) orelse
                              not (is_real_literal r) orelse is_negated r
        val ts = strip [] (if is_real_fraction l andalso not divp then r
                           else t)
      in
        if List.exists (fn t => is_literalish t orelse is_mult t orelse
                                is_baddiv t) ts orelse
           not (oksort mulcompare ts) orelse
           is_real_fraction l andalso List.exists is_negated ts orelse
           is_negated (hd ts) andalso not (is_real_fraction l) andalso
           leaveneg1 orelse
           length ts > 1 andalso List.exists is_negated (tl ts)
        then
          elimdivs THENC REWRITE_CONV [REAL_INV_MUL'] THENC
          AC_Sort.sort mulsort THENC
          TRY_CONV (REWR_CONV REAL_MUL_LID) THENC
          AC_Sort.sort mulsort THENC
          REWRITE_CONV[POW_1, nonzerop_NUMERAL, POW_ONE, REAL_MUL_LID,
                       REAL_MUL_RID, nonzerop_pow] THENC
          leading_coeff_norm leaveneg1
        else if not leaveneg1 then
          TRY_CONV (REWR_CONV REAL_NEG_MINUS1' THENC
                    TRY_CONV (RAND_CONV
                                (PURE_REWRITE_CONV [REAL_MUL_ASSOC']) THENC
                                REWR_CONV REAL_NEG_LMUL THENC
                                PURE_REWRITE_CONV [REAL_MUL_ASSOC]))
        else ALL_CONV
      end t
  fun interesting_negation t =
      case Lib.total dest_negated t of
          NONE => raise UNCHANGED
        | SOME t0 => if is_mult t0 orelse is_div t0 orelse is_inv t0 orelse
                        (is_literalish t0 andalso not (is_real_literal t0))
                     then
                       REWR_CONV REAL_NEG_MINUS1 t
                     else raise UNCHANGED

  fun REALMULCANON0 leaveneg1 =
      PURE_REWRITE_CONV [REAL_NEGNEG, pow0, POW_1] THENC
      interesting_negation THENC
      REALMULCANON00 leaveneg1 THENC
      PURE_REWRITE_CONV [REAL_MUL_LID]
  val REALMULCANON = REALMULCANON0 false
end (* local *)

val RMULCANON_ss = SSFRAG {
      ac = [], congs = [], dprocs = [], filter = NONE,
      name = SOME "RMULCANON",
      rewrs = [],
      convs = [
        {conv = K (K REALMULCANON), trace = 2,
         key = SOME ([], mk_mult(mk_var("x",real_ty), mk_var("y",real_ty))),
         name = "REALMULCANON"}
      ]
}

val _ = addfrags [RMULCANON_ss]

local
  val x = mk_var("x", real_ty)
  fun termbase t =
      if is_real_literal t then mk_abs(x,x) (* sorts last *)
      else
        case total dest_mult t of
            SOME(l,r) => if is_real_literal l then r else t
          | NONE => dest_negated t handle HOL_ERR _ => t

  val addcompare = inv_img_cmp termbase Term.compare

  val ADD_MUL1 = GSYM REAL_MUL_LID
  val ADD_RDISTRIB' = GSYM REAL_ADD_RDISTRIB
  fun give_coeff t =
      case total dest_mult t of
          SOME (l,r) => if is_real_literal l then ALL_CONV t
                        else REWR_CONV ADD_MUL1 t
        | NONE => (REWR_CONV REAL_NEG_MINUS1 ORELSEC REWR_CONV ADD_MUL1) t

  val NEG_MINUS1' = GSYM REAL_NEG_MINUS1
  val addcombine0 =
      BINOP_CONV give_coeff THENC REWR_CONV ADD_RDISTRIB' THENC
      LAND_CONV (computeLib.CBV_CONV realreduce_cs) THENC
      TRY_CONV (FIRST_CONV (map REWR_CONV [REAL_MUL_LID, REAL_MUL_LZERO]))
  fun addcombine t =
      if is_real_literal (rand t) then
        computeLib.CBV_CONV realreduce_cs t
      else addcombine0 t

  val addsort = {
    assoc = REAL_ADD_ASSOC,
    comm = REAL_ADD_COMM,
    dest = realSyntax.dest_plus,
    mk = realSyntax.mk_plus,
    cmp = addcompare,
    combine = addcombine,
    preprocess = REALMULCANON
  }
in
  fun REALADDCANON t =
      let
        fun strip A t =
            case total dest_plus t of
                SOME(t1,t2) => strip (t2::A) t1
              | NONE => t::A
        val ts = strip [] t
      in
        if List.exists is_plus ts orelse not (oksort addcompare ts)
        then
          AC_Sort.sort addsort THENC
          PURE_REWRITE_CONV [REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_RID]
        else ALL_CONV
      end t
end (* local *)

val RADDCANON_ss = SSFRAG {
      ac = [], congs = [], dprocs = [], filter = NONE,
      name = SOME "RADDCANON",
      rewrs = [],
      convs = [
        {conv = K (K REALADDCANON), trace = 2,
         key = SOME ([], mk_plus(mk_var("x",real_ty), mk_var("y",real_ty))),
         name = "REALADDCANON"}
      ]
}

(* val _ = augment_srw_ss [RMULCANON_ss] *)
fun ifMULT c1 c2 t = if is_mult t then c1 t else c2 t
fun mul_extract P t =
    case total dest_mult t of
        NONE => if P t then ALL_CONV t else NO_CONV t
      | SOME (l,r) =>
        let
        in
          if P l then ALL_CONV
          else
            (LAND_CONV (mul_extract P) THENC TRY_CONV (REWR_CONV REAL_MUL_ASSOC'))
              ORELSEC
            (RAND_CONV (mul_extract P) THENC REWR_CONV REAL_MUL_COMM THENC
             TRY_CONV (REWR_CONV REAL_MUL_ASSOC'))
        end t

fun mkexp (b0,e) =
    let
      val (b,i) = if Arbint.<(e,Arbint.zero) then (mk_inv b0, Arbint.abs e)
                  else (b0,e)
    in
      mk_pow(b, numSyntax.mk_numeral (Arbint.toNat i))
    end

val sign_rwts = [REAL_POW_POS, REAL_POW_NEG,
                 REAL_POW_GE0, REAL_POW_LE0,
                 ZERO_LT_POW,
                 REAL_LT_INV_EQ, REAL_INV_LT0]
(*
fun base_solver asms stk t =
    let
      val _ = print ("Solving "^term_to_string t)
    in
      case Exn.capture (EQT_ELIM o QCONV (SIMP_CONV (srw_ss() ++ numSimps.ARITH_ss) asms)) t of
          Exn.Res th => (print " - OK\n"; th)
        | Exn.Exn e => (print " - FAILED\n"; raise e)
    end
fun solver0 stk t = base_solver [ASSUME ``0r < U``] stk t
val stk = []

val R = “$<= : real -> real -> bool”
val Rthms = [(REAL_LE_LMUL, rhs), (REAL_LE_LMUL_NEG, rhs)]
val R = “$= : real -> real -> bool”
val Rthms = [(REAL_EQ_LMUL, (rand o rhs))]
val R = “$< : real -> real -> bool”
val Rthms = [(REAL_LT_LMUL, rhs), (REAL_LT_LMUL_NEG, rhs)]

*)
val giveexp = REWR_CONV POW_1'
fun mulrelnorm0 R Rthms solver0 stk t =
    let
      val mkERR = mk_HOL_ERR "realSimps" "mulrelnorm"
      val (l,r) = dest_binop R (mkERR ("Not a " ^ term_to_string R)) t
      val sorted_cbases = Listsort.sort (inv_img_cmp #1 litcompare) o
                          map mul_termbase o strip_mult
      val ls = sorted_cbases l
      val rs = sorted_cbases r
      fun solver stk t =
          let val eqn = QCONV (PURE_REWRITE_CONV sign_rwts) t
          in
            EQ_MP (SYM eqn) (solver0 stk (rhs (concl eqn)))
          end
      fun apply_thm (th0,_) t =
          let
            val th = PART_MATCH (lhs o #2 o strip_imp) th0 t
          in
            case total dest_imp (concl th) of
                NONE => th
              | SOME (h,c) => MP th (solver (t::stk) h)
          end
      val apply_thms = FIRST_CONV (map apply_thm Rthms)
      fun mkmove_th x (th0, f) t =
          let
            val th = PART_MATCH (f o #2 o strip_imp) (SPEC x th0) t
          in
            case total dest_imp (concl th) of
                NONE => SYM th
              | SOME (h,c) => MP th (solver(t::stk) h) |> SYM
          end
      fun mkmove_thms xyz = FIRST_CONV (map (mkmove_th xyz) Rthms)


      fun positivep i = Arbint.<=(Arbint.zero, i)
      fun process (l_t,el) (r_t,er) t =
          if is_real_literal l_t andalso is_real_literal r_t andalso
             positivep el andalso positivep er
          then
            let val li = int_of_term l_t and ri = int_of_term r_t
                val toN = Arbint.toNat o Arbint.abs
                val ln = toN li and rn = toN ri
                val dn = Arbnum.gcd (ln,rn)
                val _ = dn <> Arbnum.one orelse
                        (Arbint.<(li,Arbint.zero) andalso
                         (Arbint.<(ri,Arbint.zero) orelse same_const equality R)) orelse
                        raise mkERR "Literals are coprime"
                val di = if dn = Arbnum.one then Arbint.~ Arbint.one
                         else Arbint.fromNat dn
                val dt = term_of_int di
                val lc = Arbint.div(li,di) and rc = Arbint.div(ri,di)
                val lct = term_of_int lc and rct = term_of_int rc
                fun mkeq c = mk_mult(dt, c) |> REAL_REDUCE |> SYM
                val leqn = mkeq lct and reqn = mkeq rct
                fun extract_n_factor lit eqn =
                    mul_extract (aconv lit) THENC
                    ifMULT (LAND_CONV (K eqn) THENC REWR_CONV REAL_MUL_ASSOC')
                           (K eqn)
            in
              FORK_CONV(extract_n_factor l_t leqn, extract_n_factor r_t reqn)
                THENC
              apply_thms
            end t
          else if is_real_fraction l_t orelse is_real_fraction r_t then
            let
              fun denom (t,e) =
                  case total dest_div t of
                      NONE => if positivep e then Arbint.one
                              else int_of_term t
                    | SOME (_, d) => int_of_term d
              val ld = denom (l_t, el)
              val rd = denom (r_t, er)
              val mt = Arbint.*(ld,rd) |> term_of_int
              val sidecond1 = mk_less(zero_tm, mt) |> REAL_REDUCE
              val sidecond2 = mk_eq(mt,zero_tm) |> REAL_REDUCE
              val th = hd Rthms |> #1 |> SPEC mt
                                |> REWRITE_RULE [sidecond1,sidecond2]
                                |> GSYM
            in
              REWR_CONV th
            end t
          else if el = er then
            let fun chk t = pair_eq aconv equal (mul_termbase t) (l_t, el)
                val prc = PURE_REWRITE_CONV [REAL_POW_INV'] THENC giveexp
            in
              BINOP_CONV (mul_extract chk THENC
                          ifMULT (LAND_CONV prc)
                                 (prc THENC REWR_CONV REAL_MUL_RID')) THENC
              apply_thms
            end t
          else
            let val (c,ld,rd) = if Arbint.<(el,er) then
                                  (el,Arbint.zero,Arbint.-(er,el))
                              else (er,Arbint.-(el,er), Arbint.zero)
                fun chk p t = pair_eq aconv equal p (mul_termbase t)
                fun common split i t =
                    if i = Arbint.zero then
                      if split then REWR_CONV REAL_MUL_RID' t else ALL_CONV t
                    else
                      let
                        val mul_t = mk_mult(mkexp(l_t,c), mkexp(l_t,i))
                        val th = if Arbint.<(c,Arbint.zero) then
                                   if Arbint.<(Arbint.+(c,i), Arbint.zero) then
                                     pow_inv_mul_powlt
                                   else pow_inv_mul_invlt
                                 else REAL_POW_ADD'
                        fun stage2 t =
                            let val th0 = PART_MATCH (lhs o #2 o strip_imp) th t
                            in
                              case total dest_imp (concl th0) of
                                  NONE => th0
                                | SOME (l,r) =>
                                    MATCH_MP th0 (EQT_ELIM (REAL_REDUCE l))
                            end
                      in
                        (REWR_CONV REAL_MUL_COMM THENC stage2 THENC
                         RAND_CONV NUM_REDUCE ) mul_t |> SYM
                      end
                val lge = if Arbint.abs el = Arbint.one then giveexp
                          else ALL_CONV
                val rge = if Arbint.abs er = Arbint.one then giveexp
                          else ALL_CONV
            in
              FORK_CONV (mul_extract (chk (l_t,el)) THENC
                         ifMULT (LAND_CONV (lge THENC common false ld))
                                (lge THENC common true ld) THENC
                         TRY_CONV (REWR_CONV REAL_MUL_ASSOC'),
                         mul_extract (chk (r_t,er)) THENC
                         ifMULT (LAND_CONV (rge THENC common false rd))
                                (rge THENC common true rd) THENC
                         TRY_CONV (REWR_CONV REAL_MUL_ASSOC')) THENC
              apply_thms
            end t
      fun eqcleanup t =
          if is_disj t then
            let val subth = solver (t::stk) (mk_neg (lhand t))
            in
              LAND_CONV (REWR_CONV (EQF_INTRO subth)) THENC
              REWR_CONV Flor
            end t
          else ALL_CONV t

      (* direction = true <=> move from left to right *)
      fun maybemove (b,e) t =
          if not (is_literalish b) andalso positivep e then NO_CONV t
          else
            let val f =
                    if is_literalish b then #2 (dest_div b)
                    else mk_pow(b,
                                numSyntax.mk_numeral(Arbint.toNat(Arbint.~ e)))
                val (rel, args) = strip_comb t
                val l = hd args and r = hd (tl args)
                val th = mkmove_thms f t |> CONV_RULE (LAND_CONV eqcleanup)
            in
              CONV_RULE (RAND_CONV (BINOP_CONV REALMULCANON)) th
            end
      fun findelim lefts rights t =
          case (lefts, rights) of
              ([], []) => raise mkERR "No common eliminable terms"
            | (l1::ls, []) => (maybemove l1 ORELSEC findelim ls []) t
            | ([], r1::rs) => (maybemove r1 ORELSEC findelim [] rs) t
            | ((l1 as (bl,_))::ls, (r1 as (br,_))::rs) =>
              case litcompare(bl,br) of
                  LESS => (maybemove l1 ORELSEC findelim ls rights) t
                | GREATER => (maybemove r1 ORELSEC findelim lefts rs) t
                | EQUAL => (process l1 r1 ORELSEC findelim ls rs) t
    in
      findelim ls rs t
    end

fun elim_bare_negations t =
    case Lib.total dest_negated t of
        NONE => raise UNCHANGED
      | SOME a => if is_literalish a then raise UNCHANGED
                  else REWR_CONV REAL_NEG_MINUS1 t

(* if t is of form -c * x = y, then ensure that the r.h.s. has a constant
   coefficient at the front, adding a multiplication by one if necessary *)
fun negatedL_eq t =
    let
      val (l,r) = dest_eq t handle HOL_ERR _ => raise UNCHANGED
      val (c, _) = dest_mult l handle HOL_ERR _ => raise UNCHANGED
      val fix = RAND_CONV (REWR_CONV (GSYM REAL_MUL_LID))
    in
      if is_literalish c andalso is_negated c then
        case Lib.total dest_mult r of
            NONE => if is_literalish r then raise UNCHANGED else fix t
          | SOME (d,_) => if is_literalish d then raise UNCHANGED
                          else fix t
      else raise UNCHANGED
    end

fun mulrelnorm R Rthms solver0 stk =
    BINOP_CONV (REALMULCANON0 true THENC elim_bare_negations) THENC
    negatedL_eq THENC
    mulrelnorm0 R Rthms solver0 stk THENC
    BINOP_CONV (TRY_CONV REALMULCANON)
(*

val lenorm = mulrelnorm “$<= : real -> real -> bool”
                  [REAL_LE_LMUL, REAL_LE_LMUL_NEG] solver []

val eqnorm = mulrelnorm “$=” [REAL_EQ_LMUL] solver  []
val ex1 = eqnorm “2r * z pow 2 * inv yy = 5 * z pow 2 * inv y * a”
val ex1a = eqnorm “z * 4 = inv x * 6”
val ex1b = eqnorm “z pow 4 = inv z pow 3”

val ex2 = lenorm “2r * inv y pow 2 <= 9 * inv y * z”
val ex3 = lenorm “2r * inv y <= z * 2”;
val ex4 = lenorm “x pow 3 * 10 <= x pow 5 * y”
val ex5 = lenorm “z pow 3 * 10 <= z pow 5 * y”
*)
fun V s = mk_var(s, real_ty)
val x = V "x" and y = V "y" and z = V "z" and n = mk_var("n", numSyntax.num)
val RMULRELNORM_ss = SSFRAG {
  ac = [], congs = [], dprocs = [], filter = NONE, name = SOME "RMULRELNORM",
  rewrs = [],
  convs = [
    {key = SOME ([], mk_leq(x,y)),
     conv = mulrelnorm leq_tm [(REAL_LE_LMUL, rhs), (REAL_LE_LMUL_NEG, rhs)] ,
     name = "RMUL_LEQNORM", trace = 2
    },
    {key = SOME ([], mk_eq(x,mk_mult(y,z))),
     conv = mulrelnorm equality [(REAL_EQ_LMUL, rand o rhs)],
     name = "RMUL_EQNORM1", trace = 2
    },
    {key = SOME ([], mk_eq(mk_mult(x,y),z)),
     conv = mulrelnorm equality [(REAL_EQ_LMUL, rand o rhs)],
     name = "RMUL_EQNORM2", trace = 2
    },
    {key = SOME ([], mk_eq(mk_div(x,y), z)),
     conv = mulrelnorm equality [(REAL_EQ_LMUL, rand o rhs)],
     name = "RMUL_EQNORM3", trace = 2
    },
    {key = SOME ([], mk_eq(z, mk_div(x,y))),
     conv = mulrelnorm equality [(REAL_EQ_LMUL, rand o rhs)],
     name = "RMUL_EQNORM4", trace = 2
    },
    {key = SOME ([], mk_eq(mk_pow(x,n), z)),
     conv = mulrelnorm equality [(REAL_EQ_LMUL, rand o rhs)],
     name = "RMUL_EQNORM5", trace = 2
    },
    {key = SOME ([], mk_eq(z, mk_pow(x,n))),
     conv = mulrelnorm equality [(REAL_EQ_LMUL, rand o rhs)],
     name = "RMUL_EQNORM6", trace = 2
    },
    {key = SOME ([], mk_less(x,y)),
     conv = mulrelnorm less_tm [(REAL_LT_LMUL, rhs), (REAL_LT_LMUL_NEG, rhs)],
     name = "RMUL_LTNORM", trace = 2
    }
  ]
}

val _ = addfrags [RMULRELNORM_ss]

end
