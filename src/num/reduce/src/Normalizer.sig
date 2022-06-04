(* ========================================================================= *)
(* Relatively efficient HOL conversions for canonical polynomial form.       *)
(*   (HOL-Light's normalizer.ml)                                             *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

signature Normalizer =
sig
   include Abbrev

   (* Usage: SEMIRING_NORMALIZERS_CONV sth rth
              (is_semiring_constant,
               SEMIRING_ADD_CONV,SEMIRING_MUL_CONV,SEMIRING_POW_CONV)
              variable_order

    - "sth" is a theorem as axioms of a semiring system of the following form:

  |- (!x:'a y z. add x (add y z) = add (add x y) z) /\
     (!x y. add x y = add y x) /\
     (!x. add r0 x = x) /\
     (!x y z. mul x (mul y z) = mul (mul x y) z) /\
     (!x y. mul x y = mul y x) /\
     (!x. mul r1 x = x) /\
     (!x. mul r0 x = r0) /\
     (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
     (!x. pwr x 0 = r1) /\
     (!x n. pwr x (SUC n) = mul x (pwr x n))

    - "rth" is a theorem as additional axioms of negation and subtraction of
      the following form:

  |- (!x:'a. neg x = (neg r1) * x) /\
     (!x y. sub x y = add x ((neg r1) mul y))

    - is_semiring_constant tests if a term is a literal numeral. For :num, it can
      be numSyntax.is_numeral

     (NOTE: is_semiring_constant (neg r1) is expected to return true when "rth"
            is provided.)

    - variable_order can be (Term.compare (x,y) = LESS) in HOL4.

    - SEMIRING_ADD_CONV, SEMIRING_MUL_CONV and SEMIRING_POW_CONV are conversions
      that simplifies ‘add’, ‘mul’ and ‘pow’ of literal numerals (one-step). For
      :num, they can be ADD_CONV, MULT_CONV and EXP_CONV of reduceLib (or Arithconv).

      SEMIRING_NORMALIZERS_CONV returns 6 conversions correspoding to the following
      simplification tasks: (the last one subsumes the other five.)

      POLYNOMIAL_NEG_CONV,
      POLYNOMIAL_ADD_CONV,
      POLYNOMIAL_SUB_CONV,
      POLYNOMIAL_MUL_CONV,
      POLYNOMIAL_POW_CONV,
      POLYNOMIAL_CONV
    *)
   val SEMIRING_NORMALIZERS_CONV :
       thm -> thm -> (term -> bool) * conv * conv * conv -> (term -> term -> bool) ->
       conv * conv * conv * conv * conv * conv;

   (* Sample application of SEMIRING_NORMALIZERS_CONV for :num *)
   val NUM_NORMALIZE_CONV : conv;
end
