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

val real_SS = simpLib.SSFRAG
  {name = SOME"real",
   ac = [],
   congs = [],
   convs = [],
   dprocs = [],
   filter = NONE,
   rewrs = [(* addition *)
            REAL_ADD_LID, REAL_ADD_RID,
            (* subtraction *)
            REAL_SUB_REFL, REAL_SUB_RZERO,
            (* multiplication *)
            REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_LZERO, REAL_MUL_RZERO,
            (* division *)
            REAL_OVER1, REAL_DIV_ADD,
            (* less than or equal *)
            REAL_LE_REFL, REAL_LE_01, REAL_LE_RADD,
            (* less than *)
            REAL_LT_01, REAL_LT_INV_EQ,
            (* pushing out negations *)
            REAL_NEGNEG, REAL_LE_NEG2, REAL_SUB_RNEG, REAL_NEG_SUB,
            REAL_MUL_RNEG, REAL_MUL_LNEG,
            (* cancellations *)
            REAL_SUB_ADD2, REAL_MUL_SUB1_CANCEL, REAL_MUL_SUB2_CANCEL,
            REAL_LE_SUB_CANCEL2, REAL_ADD_SUB, REAL_SUB_ADD, REAL_ADD_SUB_ALT,
            REAL_SUB_SUB2,
            (* halves *)
            REAL_LT_HALF1, REAL_HALF_BETWEEN, REAL_NEG_HALF,
            REAL_DIV_DENOM_CANCEL2, REAL_DIV_INNER_CANCEL2,
            REAL_DIV_OUTER_CANCEL2, REAL_DIV_REFL2,
            (* thirds *)
            REAL_NEG_THIRD, REAL_DIV_DENOM_CANCEL3, REAL_THIRDS_BETWEEN,
            REAL_DIV_INNER_CANCEL3, REAL_DIV_OUTER_CANCEL3, REAL_DIV_REFL3,
            (* injections to the naturals *)
            REAL_INJ, REAL_ADD, REAL_LE, REAL_LT, REAL_MUL,
            (* pos *)
            REAL_POS_EQ_ZERO, REAL_POS_POS, REAL_POS_INFLATE,
            REAL_POS_LE_ZERO,
            (* min *)
            REAL_MIN_REFL, REAL_MIN_LE1, REAL_MIN_LE2, REAL_MIN_ADD,
            REAL_MIN_SUB,
            (* max *)
            REAL_MAX_REFL, REAL_LE_MAX1, REAL_LE_MAX2, REAL_MAX_ADD,
            REAL_MAX_SUB]};

val real_ac_SS = simpLib.SSFRAG {
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
                     num_eq_0, REAL_LT, REAL_LE,
                     REAL_MUL_RZERO, REAL_MUL_LZERO,
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

val add_rats =
    transform [(x, posneg), (y, nb12), (u, posneg), (v, nb12)] add_rat
val add_ratls = transform [(x, posneg), (y,nb12), (z, posneg)] add_ratl
val add_ratrs = transform [(x, posneg), (y, posneg), (z, nb12)] add_ratr

val mult_rats =
    transform [(x,posneg), (y, nb12), (u, posneg), (v, nb12)] mult_rat
val mult_ratls = transform [(x, posneg), (y, nb12), (z, posneg)] mult_ratl
val mult_ratrs = transform [(x, posneg), (y, posneg), (z, nb12)] mult_ratr

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

val abs1 = SPEC (mk_div(x,y)) realTheory.abs
val abs1 = transform [(x,posneg), (y, nb12)] abs1
val abs2 = SPEC x realTheory.abs
val abs2 = transform [(x,posneg)] abs2

val n = mk_var("n", numSyntax.num)
val m = mk_var("m", numSyntax.num)
fun to_numeraln th = INST [n |-> mk_comb(numSyntax.numeral_tm, n),
                           m |-> mk_comb(numSyntax.numeral_tm, m)] th


val op_rwts = [to_numeraln mult_ints, to_numeraln add_ints, REAL_DIV_LZERO,
               REAL_NEGNEG] @
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

val rel_rwts = [eq_ints, le_int, lt_int] @
               eq_rats @ eq_ratls @ eq_ratrs @
               lt_rats @ lt_ratls @ lt_ratrs @
               le_rats @ le_ratrs @ le_ratls @
               real_gts @ real_ges


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
   rewrs = rwts}

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

val _ = BasicProvers.augment_srw_ss [REAL_REDUCE_ss]

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
       (is_great tm) orelse (is_geq tm) orelse
       (is_plus tm) orelse (is_minus tm) orelse
       (is_linear_mult tm handle _ => false)
    then Lib.union (non_presburger_subterms (arg1 tm))
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

val ARITH = RealArith.REAL_ARITH

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
             if tm <> F then EQF_INTRO (try(mk_neg tm)) else raise e
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
    | SOME ("real", "real_sub") => go2()
    | SOME ("real", "real_gt") => go2()
    | SOME ("realax", "real_lt") => go2()
    | SOME ("real", "real_lte") => go2()
    | SOME ("real", "real_ge") => go2()
    | SOME ("realax", "real_neg") => go1()
    | SOME ("real", "abs") => go1()
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
       (ty=Type.bool andalso (is_arith tm orelse tm = F))
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
  REDUCER {name = SOME"ARITH_REDUCER",
           addcontext = add_ctxt,
           apply = fn args => CACHED_ARITH (get_ctxt (#context args)),
           initial = CTXT []}
end;

val REAL_ARITH_ss =
    SSFRAG
    {name=SOME"REAL_ARITH",
     convs = [], rewrs = [], congs = [],
      filter = NONE, ac = [], dprocs = [ARITH_REDUCER]};

end
