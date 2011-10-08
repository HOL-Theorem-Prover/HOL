(* Copyright (c) 2010-2011 Tjark Weber. All rights reserved. *)

(* SMT-LIB 2 theories *)

structure SmtLib_Theories =
struct

local

  local open HolSmtTheory in end

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Theories"

in

  fun zero_args x xs =
    if List.null xs then
      x
    else
      raise ERR "zero_args" "no arguments expected"

  fun one_arg f xs =
    f (Lib.singleton_of_list xs handle Feedback.HOL_ERR _ =>
      raise ERR "one_arg" "one argument expected")

  fun two_args f xs =
    f (Lib.pair_of_list xs handle Feedback.HOL_ERR _ =>
      raise ERR "two_args" "two arguments expected")

  fun three_args f xs =
    f (Lib.triple_of_list xs handle Feedback.HOL_ERR _ =>
      raise ERR "three_args" "three arguments expected")

  fun list_args f xs =
    if List.null xs then
      raise ERR "list_args" "non-empty argument list expected"
    else
      f xs

  fun zero_zero f x = zero_args (zero_args (f x))
  fun zero_one f x = zero_args (one_arg (f x))
  fun zero_two f x = zero_args (two_args (f x))

  fun one_zero f x = zero_args o (one_arg (f x))
  fun one_one f x = one_arg o (one_arg (f x))

  fun K_zero_zero x = Lib.K (zero_args (zero_args x))
  fun K_zero_one f = Lib.K (zero_args (one_arg f))
  fun K_zero_two f = Lib.K (zero_args (two_args f))
  fun K_zero_three f = Lib.K (zero_args (three_args f))
  fun K_zero_list f = Lib.K (zero_args (list_args f))

  fun K_one_zero f = Lib.K (zero_args o one_arg f)
  fun K_one_one f = Lib.K (one_arg o one_arg f)

  fun K_two_one f = Lib.K (one_arg o two_args f)

  fun chainable f =
  let
    fun aux t [] = raise Match  (* should never happen *)
      | aux t [_] = t
      | aux t (x::y::zs) = aux (boolSyntax.mk_conj (t, f (x, y))) (y::zs)
  in
    Lib.K (zero_args (list_args
      (fn x::y::zs => aux (f (x, y)) (y::zs)
        | _ => raise ERR "chainable" "at least two arguments expected")))
  end

  fun leftassoc f =
  let
    fun aux t [] = t
      | aux t (y::zs) = aux (f (t, y)) zs
  in
    Lib.K (zero_args (list_args
      (fn x::y::zs => aux x (y::zs)
        | _ => raise ERR "leftassoc" "at least two arguments expected")))
  end

  fun rightassoc f =
  let
    fun aux _ [] = raise Match  (* should never happen *)
      | aux cont [y] = cont y
      | aux cont (x::y::zs) = aux (fn t => cont (f (x, t))) (y::zs)
  in
    Lib.K (zero_args (list_args
      (fn x::y::zs => aux Lib.I (x::y::zs)
        | _ => raise ERR "rightassoc" "at least two arguments expected")))
  end

  (* A <numeral> is the digit 0 or a non-empty sequence of digits not
     starting with 0. *)
  fun is_numeral token =
  let
    val cs = String.explode token
  in
    cs = [#"0"] orelse
      (not (List.null cs) andalso List.all Char.isDigit cs andalso
        List.hd cs <> #"0")
  end

  (* A <decimal> is a token of the form <numeral>.0*<numeral>. *)
  fun real_of_decimal token =
  let
    val (left, right) = Lib.pair_of_list (String.fields (Lib.equal #".") token)
    val _ = is_numeral left orelse
      raise ERR "real_of_decimal" "not a decimal"
    val right = String.explode right
    fun is_zerostar_numeral (#"0" :: c :: cs) = is_zerostar_numeral (c :: cs)
      | is_zerostar_numeral cs                = is_numeral (String.implode cs)
    val _ = is_zerostar_numeral right orelse
      raise ERR "real_of_decimal" "not a decimal"
    (* drop trailing 0's *)
    fun drop_zeros (#"0" :: cs) = drop_zeros cs
      | drop_zeros cs           = cs
    val right = String.implode (List.rev (drop_zeros (List.rev right)))
    val numerator = Arbint.fromString (left ^ right)
    val ten = Arbint.fromInt 10
    val denominator = Lib.funpow (String.size right)
      (fn i => Arbint.* (ten, i)) Arbint.one
  in
    if denominator = Arbint.one then
      realSyntax.term_of_int numerator
    else
      realSyntax.mk_div (realSyntax.term_of_int numerator,
        realSyntax.term_of_int denominator)
  end
  handle Feedback.HOL_ERR _ =>
    raise ERR "real_of_decimal" "not a decimal"

  (* ArraysEx *)

  structure ArraysEx =
  struct

    val tydict = Library.dict_from_list [
      (* arrays are translated as functions *)
      ("Array", K_zero_two Type.-->)
    ]

    val tmdict = Library.dict_from_list [
      (* array lookup is translated as function application *)
      ("select", K_zero_two Term.mk_comb),
      (* array update is translated as function update *)
      ("store", K_zero_three (fn (array, index, value) =>
        Term.mk_comb (combinSyntax.mk_update (index, value), array)))
    ]

  end

  (* Fixed_Size_BitVectors *)

  structure Fixed_Size_BitVectors =
  struct

    val tydict = Library.dict_from_list [
      ("BitVec", K_one_zero (wordsSyntax.mk_word_type o fcpLib.index_type))
    ]

    val tmdict = Library.dict_from_list [
      (* bit-vector constants *)
      ("_", zero_zero (fn token =>
        if String.isPrefix "#b" token then
          let
            val binary = String.extract (token, 2, NONE)
            val value = Arbnum.fromBinString binary
            val size = Arbnum.fromInt (String.size binary)
          in
            wordsSyntax.mk_word (value, size)
          end
        else if String.isPrefix "#x" token then
          let
            val hex = String.extract (token, 2, NONE)
            val value = Arbnum.fromHexString hex
            val size = Arbnum.times2 (Arbnum.times2 (Arbnum.fromInt
              (String.size hex)))
          in
            wordsSyntax.mk_word (value, size)
          end
        else
          raise ERR "<Fixed_Size_BitVectors.tmdict._>"
            "not a bit-vector constant")),
      ("concat", K_zero_two wordsSyntax.mk_word_concat),
      ("extract", K_two_one (fn (m, n) =>
        let
          val index_type = fcpLib.index_type (Arbnum.plus1 (Arbnum.- (m, n)))
          val m = numSyntax.mk_numeral m
          val n = numSyntax.mk_numeral n
        in
          fn t => wordsSyntax.mk_word_extract (m, n, t, index_type)
        end)),
      ("bvnot", K_zero_one wordsSyntax.mk_word_1comp),
      ("bvneg", K_zero_one wordsSyntax.mk_word_2comp),
      ("bvand", K_zero_two wordsSyntax.mk_word_and),
      ("bvor", K_zero_two wordsSyntax.mk_word_or),
      ("bvadd", K_zero_two wordsSyntax.mk_word_add),
      ("bvmul", K_zero_two wordsSyntax.mk_word_mul),
      (* SMT-LIB states that division by 0w is unspecified. Thus, any
         proof (of unsatisfiability) should also be valid in HOL,
         regardless of how division by 0w is defined in HOL. *)
      ("bvudiv", K_zero_two wordsSyntax.mk_word_div),
      ("bvurem", K_zero_two wordsSyntax.mk_word_mod),
      ("bvshl", K_zero_two wordsSyntax.mk_word_lsl_bv),
      ("bvlshr", K_zero_two wordsSyntax.mk_word_lsr_bv),
      ("bvult", K_zero_two wordsSyntax.mk_word_lo)
    ]

  end

  (* Core *)

  structure Core =
  struct

    val tydict = Library.dict_from_list [
      ("Bool", K_zero_zero Type.bool)
    ]

    val tmdict = Library.dict_from_list [
      ("true", K_zero_zero boolSyntax.T),
      ("false", K_zero_zero boolSyntax.F),
      ("not", K_zero_one boolSyntax.mk_neg),
      ("=>", rightassoc boolSyntax.mk_imp),
      (* FIXME: SMT-LIB declares "and" and "or" as left-assoc. This
         interacts badly with HOL4, where they are right-assoc.  In
         particular, it breaks our proof reconstruction implementation
         (Z3_ProofReplay.sml) in a few places that are not prepared to
         handle the additional parentheses. For now, we parse "and"
         and "or" as rightassoc. Since conjunction and disjunction are
         associative, this does not change the meaning of formulas. *)
      ("and", rightassoc boolSyntax.mk_conj),
      ("or", rightassoc boolSyntax.mk_disj),
      ("xor", leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
          (Term.prim_mk_const {Thy="HolSmt", Name="xor"}, t1), t2))),
      ("=", chainable boolSyntax.mk_eq),
      (* "distinct" is declared as :pairwise in SMT-LIB, but rather
         than unfolding the definition of :pairwise, we use
         'mk_all_distinct' *)
      ("distinct", K_zero_list (fn ts => listSyntax.mk_all_distinct
        (listSyntax.mk_list (ts, Term.type_of (List.hd ts))))),
      ("ite", K_zero_three boolSyntax.mk_cond)
    ]

  end

  (* Ints *)

  structure Ints =
  struct

    val tydict = Library.dict_from_list [
      ("Int", K_zero_zero intSyntax.int_ty)
    ]

    val tmdict = Library.dict_from_list [
      (* numerals *)
      ("_", zero_zero (fn token =>
        if is_numeral token then
          intSyntax.term_of_int (Arbint.fromString token)
        else
          raise ERR "<Ints.tmdict._>" "not a numeral")),
      ("-", K_zero_one intSyntax.mk_negated),
      ("-", leftassoc intSyntax.mk_minus),
      ("+", leftassoc intSyntax.mk_plus),
      ("*", leftassoc intSyntax.mk_mult),
      (* FIXME: add parsing of div and mod *)
      ("abs", K_zero_one intSyntax.mk_absval),
      ("<=", chainable intSyntax.mk_leq),
      ("<", chainable intSyntax.mk_less),
      (">=", chainable intSyntax.mk_geq),
      (">", chainable intSyntax.mk_great)
    ]

  end

  (* Reals *)

  structure Reals =
  struct

    val tydict = Library.dict_from_list [
      ("Real", K_zero_zero realSyntax.real_ty)
    ]

    val tmdict = Library.dict_from_list [
      (* numerals *)
      ("_", zero_zero (fn token =>
        if is_numeral token then
          realSyntax.term_of_int (Arbint.fromString token)
        else
          raise ERR "<Reals.tmdict._>" "not a numeral")),
      (* decimals *)
      ("_", zero_zero real_of_decimal),
      ("-", K_zero_one realSyntax.mk_negated),
      ("-", leftassoc realSyntax.mk_minus),
      ("+", leftassoc realSyntax.mk_plus),
      ("*", leftassoc realSyntax.mk_mult),
      ("/", leftassoc realSyntax.mk_div),
      ("<=", chainable realSyntax.mk_leq),
      ("<", chainable realSyntax.mk_less),
      (">=", chainable realSyntax.mk_geq),
      (">", chainable realSyntax.mk_great)
    ]

  end

  (* Reals_Ints *)

  structure Reals_Ints =
  struct

    val tydict = Library.dict_from_list [
      ("Int", K_zero_zero intSyntax.int_ty),
      ("Real", K_zero_zero realSyntax.real_ty)
    ]

    val tmdict = Library.dict_from_list [
      (* numerals *)
      ("_", zero_zero (fn token =>
        if is_numeral token then
          intSyntax.term_of_int (Arbint.fromString token)
        else
          raise ERR "<Reals_Ints.tmdict._>" "not a numeral")),
      ("-", K_zero_one intSyntax.mk_negated),
      ("-", leftassoc intSyntax.mk_minus),
      ("+", leftassoc intSyntax.mk_plus),
      ("*", leftassoc intSyntax.mk_mult),
      (* FIXME: add parsing of div and mod *)
      ("abs", K_zero_one intSyntax.mk_absval),
      ("<=", chainable intSyntax.mk_leq),
      ("<", chainable intSyntax.mk_less),
      (">=", chainable intSyntax.mk_geq),
      (">", chainable intSyntax.mk_great),
      (* decimals *)
      ("_", zero_zero real_of_decimal),
      ("-", K_zero_one realSyntax.mk_negated),
      ("-", leftassoc realSyntax.mk_minus),
      ("+", leftassoc realSyntax.mk_plus),
      ("*", leftassoc realSyntax.mk_mult),
      ("/", leftassoc realSyntax.mk_div),
      ("<=", chainable realSyntax.mk_leq),
      ("<", chainable realSyntax.mk_less),
      (">=", chainable realSyntax.mk_geq),
      (">", chainable realSyntax.mk_great),
      ("to_real", K_zero_one intrealSyntax.mk_real_of_int),
      ("to_int", K_zero_one intrealSyntax.mk_INT_FLOOR),
      ("is_int", K_zero_one intrealSyntax.mk_is_int)
    ]

  end

end  (* local *)

end
