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

(* ----------------------------------------------------------------------
    var_sorted ct

    Checks that the variables in constraint ct (a term) appear in order
    from left to right.
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

