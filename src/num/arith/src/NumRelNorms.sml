structure NumRelNorms :> NumRelNorms =
struct

open HolKernel boolLib

(* ----------------------------------------------------------------------
    basic canonisers
   ---------------------------------------------------------------------- *)

(* first define the records containing the necessary information for the
   generic canoniser *)

(* for addition - right-associated for backwards compatibility *)
local
  open numSyntax arithmeticTheory GenPolyCanon
  fun is_good t = let
    val (l,r) = dest_mult t
  in
    is_numeral l
  end handle HOL_ERR _ => false
  fun non_coeff t = if is_good t then rand t
                    else if is_numeral t then mk_var("   ", num)
                    else t
  fun add_coeff (t:term) : thm = if is_good t then ALL_CONV t
                    else REWR_CONV (GSYM MULT_LEFT_1) t
  val distrib = GSYM RIGHT_ADD_DISTRIB
  fun merge t = let
    val (l,r) = dest_plus t
  in
    if is_numeral l andalso is_numeral r then
      reduceLib.REDUCE_CONV
    else
      Conv.BINOP_CONV add_coeff THENC
      REWR_CONV distrib THENC LAND_CONV reduceLib.REDUCE_CONV
  end t
in
  val rnatadd_gci =
      GCI { dest = dest_plus,
            assoc_mode = R,
            assoc = ADD_ASSOC,
            symassoc = GSYM ADD_ASSOC,
            comm = ADD_COMM,
            r_asscomm = derive_r_asscomm ADD_ASSOC ADD_COMM,
            l_asscomm = derive_l_asscomm ADD_ASSOC ADD_COMM,
            is_literal = is_numeral,
            non_coeff = non_coeff, merge = merge,
            postnorm = REWR_CONV (CONJUNCT1 (SPEC_ALL MULT)) ORELSEC
            TRY_CONV (REWR_CONV MULT_LEFT_1),
            left_id = CONJUNCT1 ADD,
            right_id = ADD_0,
            reducer = reduceLib.REDUCE_CONV}
  val lnatadd_gci =
      GCI { dest = dest_plus,
            assoc_mode = L,
            assoc = ADD_ASSOC,
            symassoc = GSYM ADD_ASSOC,
            comm = ADD_COMM,
            r_asscomm = derive_r_asscomm ADD_ASSOC ADD_COMM,
            l_asscomm = derive_l_asscomm ADD_ASSOC ADD_COMM,
            is_literal = is_numeral,
            non_coeff = non_coeff, merge = merge,
            postnorm = REWR_CONV (CONJUNCT1 (SPEC_ALL MULT)) ORELSEC
            TRY_CONV (REWR_CONV MULT_LEFT_1),
            left_id = CONJUNCT1 ADD,
            right_id = ADD_0,
            reducer = reduceLib.REDUCE_CONV}
end

val ADDL_CANON_CONV = GenPolyCanon.gencanon lnatadd_gci
val ADDR_CANON_CONV = GenPolyCanon.gencanon rnatadd_gci





(* multiplication *)
val lcnatmult_gci = let
  open GenPolyCanon numSyntax arithmeticTheory
  fun is_good t = let
    val (l,r) = dest_exp t
  in
    is_numeral r
  end handle HOL_ERR _ => false
  fun non_coeff t = if is_good t then rand (rator t)
                    else if is_numeral t then mk_numeral Arbnum.one
                    else t
  fun add_coeff t = if is_good t then ALL_CONV t
                    else REWR_CONV (GSYM (CONJUNCT2 (SPEC_ALL EXP_1))) t
  val distrib = GSYM EXP_ADD
  fun merge t = let
    val (l,r) = dest_mult t
  in
    if is_numeral l andalso is_numeral r then reduceLib.REDUCE_CONV
    else Conv.BINOP_CONV add_coeff THENC REWR_CONV distrib THENC
         reduceLib.REDUCE_CONV
  end t
in
  GCI { dest = dest_mult,
        is_literal = is_numeral,
        assoc_mode = L_Cflipped,
        assoc = MULT_ASSOC,
        symassoc = GSYM MULT_ASSOC,
        comm = MULT_COMM,
        r_asscomm = derive_r_asscomm MULT_ASSOC MULT_COMM,
        l_asscomm = derive_l_asscomm MULT_ASSOC MULT_COMM,
        non_coeff = non_coeff,
        merge = merge,
        postnorm = REWR_CONV (CONJUNCT1 (SPEC_ALL EXP)) ORELSEC
                   TRY_CONV (REWR_CONV (CONJUNCT2 (SPEC_ALL EXP_1))),
        right_id = MULT_RIGHT_1,
        left_id = MULT_LEFT_1,
        reducer = reduceLib.REDUCE_CONV}
end

val MUL_CANON_CONV = GenPolyCanon.gencanon lcnatmult_gci



(* normalisation of sums over relational operators *)
structure NumRel_Base =
struct
  open numSyntax Abbrev
  type t = Arbint.int
  val dest = dest_plus
  val zero = Arbint.zero
  val one = Arbint.one
  val one_t = mk_numeral (Arbint.toNat one)
  val mk = mk_plus
  val listmk = list_mk_plus
  fun toNat t = Arbint.fromNat (dest_numeral t)
  fun destf t = let
    val (l,r) = dest_mult t
  in
    (toNat l, r)
  end handle HOL_ERR _ => if is_numeral t then (toNat t, one_t)
                          else (Arbint.one, t)
  fun mkf (i,t) = let
    val i_t = mk_numeral(Arbint.toNat i)
  in
    if aconv t one_t then i_t else mk_mult(i_t, t)
  end
  val canon = ADDR_CANON_CONV
  val addid = REWR_CONV (GSYM arithmeticTheory.ADD_0)
  val op+ = Arbint.+
  val op- = Arbint.-
  val op~ = Arbint.~
  val op < = Arbint.<
end

structure LEQ_NREL : RelNorm_Input = struct
  open NumRel_Base
  val destrel = dest_leq
  val opr = leq_tm
  val rwt = arithmeticTheory.LE_ADD_LCANCEL
end

structure LT_NREL : RelNorm_Input = struct
  open NumRel_Base
  val destrel = dest_less
  val opr = less_tm
  val rwt = arithmeticTheory.LT_ADD_LCANCEL
end

structure EQ_NREL : RelNorm_Input = struct
  open NumRel_Base
  val destrel = dest_eq
  val opr = mk_thy_const{Name = "=", Thy = "min", Ty = num --> num --> bool}
  val rwt = arithmeticTheory.EQ_ADD_LCANCEL
end

structure NumLEQNorm = GenRelNorm (LEQ_NREL);
structure NumLTNorm = GenRelNorm (LT_NREL);
structure NumEQNorm = GenRelNorm (EQ_NREL);

val sum_leq_norm = NumLEQNorm.gen_relnorm
val sum_lt_norm = NumLTNorm.gen_relnorm
val sum_eq_norm = NumEQNorm.gen_relnorm


end;
