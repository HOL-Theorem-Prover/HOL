structure OmegaSimple :> OmegaSimple =
struct
(* ----------------------------------------------------------------------
    Takes a closed existentially quantified formula where the body of
    the formula is a conjunction of <=-constraints.

    A <=-constraint is always of the form
        0 <= c_1*v_1 + c_2 * v_2 + c_3 * v_3 + ... + n

    With each c_i and the n an integer literal.  The n may be zero, but
    must be present.

    Attempts to reduce the formula to true or false using the MLshadow
    code in OmegaMLShadow.
   ---------------------------------------------------------------------- *)

open HolKernel boolLib intSyntax
open integerTheory

val lhand = rand o rator

val ERR = mk_HOL_ERR "OmegaSimple";

(* Fix the grammar used by this file *)
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars integer_grammars
end


(* ----------------------------------------------------------------------
    var_sorted ct

    Checks that the variables in constraint ct (a term) appear in order
    from left to right, and aren't duplicated.
   ---------------------------------------------------------------------- *)

fun vars_sorted ct = let
  fun recurse [] = true
    | recurse [_] = true
    | recurse (t::(ts as (u::us))) = let
        val vname = #1 o dest_var o #2 o dest_mult
      in
        String.<(vname t, vname u)
      end
in
  recurse (#1 (front_last (strip_plus (rand ct))))
end

(* ----------------------------------------------------------------------
    add_term_to_db db t next kont

    Adds a term to an OmegaMLShadow database, and continues with next if
    this doesn't do anything untoward, or kont if this generates a
    "result" immediately (which can come about if there is already a term
    in the database that contradicts what we have).
   ---------------------------------------------------------------------- *)

fun add_term_to_db db vars t next kont = let
  open OmegaMLShadow
  val df as (f,d) = term_to_dfactoid vars t
in
  if false_factoid f then kont (CONTR d)
  else if true_factoid f then next db kont
  else add_check_factoid db (gcd_check_dfactoid df) next kont
end

(* ----------------------------------------------------------------------
    determine_width cstlist

    determines the number of free variables in cstlist, and then adds
    one to give the necessary width of the MLShadow database.
   ---------------------------------------------------------------------- *)

fun determine_width cstlist =
  HOLset.numItems (FVL cstlist empty_tmset) + 1

(* ----------------------------------------------------------------------
    isolate_var v t

    t  is a term of the form 0 <= c1 * v1 + ... + vn * cn + n
    where v is one of the vi's.   This function moves things around so
    that v is on its own with a positive coefficient on one side or the
    other of the <=.
   ---------------------------------------------------------------------- *)

val SYMLE_ADDL = GSYM integerTheory.INT_LE_ADDL
val LE_NEG = REWRITE_RULE [INT_NEG_LMUL, INT_NEGNEG]
                          (SPECL [``c * v:int``, ``~y:int``] INT_LE_NEG)
fun isolate_var v t = let
  val r = rand t
  fun findv_c t = let
    val (l,r) = dest_plus t
    val (c,v') = dest_mult r
  in
    if v = v' then c else findv_c l
  end handle HOL_ERR _ => #1 (dest_mult t)
  val c = findv_c (lhand r)
  val (flip, addthis) = if is_negated c then (false, mk_mult(rand c, v))
                        else (true, mk_mult(mk_negated c, v))
  val add_th = SPECL [r,addthis] SYMLE_ADDL
  open OmegaMath
in
  K add_th THENC
  RAND_CONV SORT_AND_GATHER1_CONV THENC
  (if flip then REWR_CONV LE_NEG THENC LAND_CONV NEG_SUM_CONV else ALL_CONV)
end t

(* ----------------------------------------------------------------------
    verify_combination v th1 th2

    Does variable elimination on v, given a "lower-bound" theorem th1,
    and an "upper-bound" theorem th2.  Both th1 and th2 are of the form
      0 <= c1 * v1 + ... + vn * cn + n
    In th1, the coefficient of v will be positive, and in th2, negative.
   ---------------------------------------------------------------------- *)

fun verify_combination v th1 th2 = let
  open CooperMath OmegaMath
  val lowth = CONV_RULE (isolate_var v) th1
  val upth = CONV_RULE (isolate_var v) th2
  val lo_c = lhand (rand (concl lowth))
  val hi_c = lhand (lhand (concl upth))
  val lo = int_of_term lo_c
  val hi = int_of_term hi_c
  val lh = lcm(lo,hi)
  val lo_f = term_of_int (Arbint.div(lh,lo))
  val hi_f = term_of_int (Arbint.div(lh,hi))
  fun multhru_by c th =
      if c = one_tm then th
      else let
          val zero_lt_c = EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, c)))
          val res =
              EQ_MP (SYM (MP (SPECL [c, lhand (concl th), rand (concl th)]
                                    INT_LE_MONO)
                             zero_lt_c))
                    th
        in
          CONV_RULE (BINOP_CONV LINEAR_MULT) res
        end
  val newlo = multhru_by lo_f lowth
  val newhi = multhru_by hi_f upth
  val elim = MATCH_MP INT_LE_TRANS (CONJ newlo newhi)
in
  CONV_RULE (REWR_CONV int_arithTheory.le_move_all_right THENC
             RAND_CONV (RAND_CONV NEG_SUM_CONV THENC
                        SORT_AND_GATHER_CONV)) elim
end

(* ----------------------------------------------------------------------
    verify_gcd_check th

    Eliminates a common divisor from the coefficients of the variables in
    theorem th, which is of the standard form.
   ---------------------------------------------------------------------- *)

fun verify_gcd_check th = let
  open CooperMath
  val t = concl th
  val cs = List.mapPartial (total (#1 o dest_mult)) (strip_plus (rand t))
  val ics = map (Arbint.abs o int_of_term) cs
  val d = gcdl ics
  val d_t = term_of_int d
  val rwt = MATCH_MP (SPEC d_t int_arithTheory.elim_le_coeffs)
                     (EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, d_t))))
in
  CONV_RULE (RAND_CONV (factor_out d d_t THENC
                        REWRITE_CONV [GSYM INT_LDISTRIB]) THENC
             REWR_CONV rwt THENC
             RAND_CONV (RAND_CONV REDUCE_CONV)) th
end

(* ----------------------------------------------------------------------
    verify_contr (th1, th2)

    return [..] |- F
    given the theorems th1 and th2, which between them say contradictory
    things.  They will be of the form 0 <= X + c and 0 <= ~X + d
    and ~c is not <= d.   X may be the sum of multiple ci * vi pairs.
   ---------------------------------------------------------------------- *)

fun verify_contr (th1, th2) = let
  val isolate_X = REWR_CONV int_arithTheory.le_move_right_left THENC
                  REWRITE_CONV [INT_NEGNEG, INT_ADD_LID, INT_NEG_ADD,
                                INT_NEG_LMUL]
  val th1' = CONV_RULE isolate_X th1
  val th2' = CONV_RULE (RAND_CONV (REWR_CONV INT_ADD_COMM) THENC
                        isolate_X) th2
  open CooperMath
in
  CONV_RULE REDUCE_CONV (MATCH_MP INT_LE_TRANS (CONJ th1' th2'))
end


(* ----------------------------------------------------------------------
    verify_derivation tm vars d

    takes a purported derivation of false, and uses it to equate tm to
    false.
   ---------------------------------------------------------------------- *)

fun verify_derivation tm vars d = let
  open OmegaMLShadow
  fun verifyd d =
      case d of
        ASM t => ASSUME t
      | REAL_COMBIN(i, d1, d2) => let
          val th1 = verifyd d1
          val th2 = verifyd d2
        in
          verify_combination (List.nth(vars, i)) th1 th2
        end
    | GCD_CHECK d0 => verify_gcd_check (verifyd d0)
    | DIRECT_CONTR (d1,d2) =>
      verify_contr(verifyd d1, verifyd d2)
  val falsity = verifyd d
  val (bvars, body) = strip_exists tm
  val bodyths = CONJUNCTS (ASSUME body)
  fun elimhyps th [] = th
    | elimhyps th (cth::cths) = if HOLset.isEmpty (hypset th) then th
                                else elimhyps (PROVE_HYP cth th) cths
  val hyps_elimmed = elimhyps falsity bodyths
  fun foldthis (v, th) = let
    val newhyp = mk_exists(v, hd (hyp th))
  in
    CHOOSE(v, ASSUME(newhyp)) th
  end
  val exists_f = List.foldr foldthis hyps_elimmed bvars
in
  EQF_INTRO (NOT_INTRO (DISCH_ALL exists_f))
end


(* ----------------------------------------------------------------------
    verify_satisfaction tm vars vm

    vm maps integers to integers, where the domain is an index into the
    list vars.  Use this to provide witnesses that prove tm = T
   ---------------------------------------------------------------------- *)

fun verify_satisfaction tm vars vm = let
  fun prove_exists t =
      if is_exists t then let
          val (v, bod) = dest_exists t
          val i = index (fn u => u = v) vars
          val n = PIntMap.find i vm
          val n_t = term_of_int n
          val newbod = Term.subst [v |-> n_t] bod
          val subth = prove_exists newbod
        in
          EXISTS(t, n_t) subth
        end
      else EQT_ELIM (CooperMath.REDUCE_CONV t)
in
  EQT_INTRO (prove_exists tm)
end

(* ----------------------------------------------------------------------
    verify_result tm vars r

    takes a term and a result from the MLShadow and attempts to turn it
    into a theorem, where vars is the list of variables occuring in tm,
    in order.
   ---------------------------------------------------------------------- *)

fun verify_result tm vars r = let
  open OmegaMLShadow
in
  case r of
    CONTR d => verify_derivation tm vars d
  | SATISFIABLE vm => verify_satisfaction tm vars vm
  | NO_CONCL => raise ERR "verify_result" "ML shadow chasing inconclusive"
end

(* ----------------------------------------------------------------------
    simple_CONV t

    attempts to use ML shadow chasing to prove t either true or false.
   ---------------------------------------------------------------------- *)

fun simple_CONV t = let
  val (vars, body) = strip_exists t
  val svars = Listsort.sort Term.compare vars
  val bcs = strip_conj body
  fun add_ts db tl next kont =
      case tl of
        [] => next db kont
      | (t::ts) =>
        add_term_to_db db svars t (fn db => fn k => add_ts db ts next k) kont
  open OmegaMLShadow
  val ordered_vars = Listsort.sort Term.compare vars
in
  add_ts (dbempty (length vars + 1)) bcs work (verify_result t ordered_vars)
end

(* testing code:

   fun toTerm l = let
     open intSyntax
     val clist = map Arbint.fromInt l
     val lim = length clist - 1

     fun clist2term (x, (acc, n)) = let
       val c = intSyntax.term_of_int x
       val cx = if n = lim then c
                else mk_mult(c, mk_var("x"^Int.toString n, int_ty))
     in
       case acc of
         NONE => (SOME cx, n + 1)
       | SOME a => (SOME(mk_plus(a, cx)), n + 1)
     end
   in
     mk_leq(zero_tm, valOf (#1 (List.foldl clist2term (NONE, 0) clist)))
   end

   fun test l = let
     val body = list_mk_conj (map toTerm l)
     val g = list_mk_exists(free_vars body, body)
   in
     time simple_CONV g;
     time Cooper.COOPER_CONV g
   end;

   test [[2,3,6],[~1,~4,7]];  (* exact elimination *)
   test [[2,3,4],[~3,~4,7]];  (* dark shadow test *)
   test [[2,3,4],[~3,~4,7],[4,5,~10]];  (* another dark shadow *)
   test [[2,3,4],[~3,~4,7],[4,~5,~10]];  (* also satisfiable *)
   test [[~3,~1,6],[2,1,~5],[3,~1,~3]];  (* a contradiction *)
   test [[11,13,~27], [~11,~13,45],[7,~9,10],[~7,9,4]];  (* no conclusion *)

*)

end (* struct *)
