signature permLib =
sig
  include Abbrev

  (* Syntax *)
  val PERM_tm   : term
  val dest_PERM : term -> term * term
  val is_PERM   : term -> bool



  (* Given a term of the form "PERM l1 l2" this
     conversion tries to eliminate common parts of
     l1 and l2. It knows about APPEND and CONS.

     Example:

     PERM_ELIM_DUPLICATES_CONV ``PERM (x::l1++y::l2++l3) (y::l3++z::l2++l4)``

     |- PERM (x::l1 ++ y::l2 ++ l3) (y::l3 ++ z::l2 ++ l4) <=>
        PERM (x::l1) ([z] ++ l4)
  *)
  val PERM_ELIM_DUPLICATES_CONV : term -> thm

  (* Given a term of the form "PERM l1 l2" this
     conversion tries to combine TAKE and DROP parts of
     l1 and l2. It uses that resorting is allowed inside permutations.

     Example:

     PERM_TAKE_DROP_CONV
        “PERM (DROP n l1++l2++TAKE n l1) (l1++TAKE n l2++DROP n l2)”

     |- PERM (DROP n l1 ++ l2 ++ TAKE n l1) (l1 ++ TAKE n l2 ++ DROP n l2) <=>
        PERM (l1 ++ l2) (l2 ++ l1)
  *)
  val PERM_TAKE_DROP_CONV : term -> thm

  (* Given a term ``PERM l1 l2`` this conversions sorts the lists l1 and l2.

     Example:

     PERM_NO_ELIM_NORMALISE_CONV ``PERM (x::l1++y::l2++l3) (y::l3++z::l2++l4)``

     |- PERM (x::l1++y::l2++l3) (y::l3++z::l2++l4) <=>
        PERM (x::y::(l1 ++ l2 ++ l3)) (y::z::(l2 ++ l3 ++ l4))
  *)
  val PERM_NO_ELIM_NORMALISE_CONV : term -> thm


  (* Turns ``PERM l1 l2`` into ``PERM l2 l1`` iff l1 is in some sence
     smaller than l2. This is useful in combination with PERM_REWR_CONV.

     Exmaple:

     PERM_TURN_CONV ``PERM (x::l1) (y::z::l1 ++ l2 ++ l3)``

     |- PERM (x::l1) (y::z::l1 ++ l2 ++ l3) <=>
        PERM (y::z::l1 ++ l2 ++ l3) (x::l1)
  *)
  val PERM_TURN_CONV : term -> thm


  (* Combines PERM_ELIM_DUPLICATES_CONV, PERM_NO_ELIM_NORMALISE_CONV and
     PERM_TURN_CONV


     Example:

     PERM_NORMALISE_CONV ``PERM (x::l1++y::l2++l3) (y::l3++z::l2++l4)``

     |- PERM (x::l1++y::l2++l3) (y::l3++z::l2++l4) <=>
        PERM (z::l4) (x::l1)
  *)
  val PERM_NORMALISE_CONV : term -> thm

  (* Given two terms l1 and l2. PERM_SPLIT l1 l2 tries to find
     a l2' such that PERM l2 (l1 ++ l2') holds.

     Example:

     PERM_SPLIT ``(y::l4)`` ``(y::l3++z::l2++l4)``

     |- PERM (y::l3++z::l2++l4) (y::l4 ++ (l3 ++ z::l2)
  *)
  val PERM_SPLIT : term -> term -> thm


  (* Given a theorem |- PERM l r and a term
     PERM l1 l2 then
     PERM_REWR_CONV tries to replace l in l1 or l2 with r.
     Afterwards PERM_NORMALISE_CONV is used.

     Example:
     PERM_REWR_CONV
       (ASSUME “PERM l1 [x;y;z]”)
       “PERM (z::y::x'::l2) (l3++x'::l1)”

     [PERM l1 [x; y; z]]
       |- PERM (z::y::x'::l2) (l3 ++ x'::l1) <=> PERM (x::l3) l2 : thm
  *)
  val PERM_REWR_CONV : thm -> term -> thm


  (* A SSFRAG to use these PERM tools with the simplifier *)
  val PERM_ss        : simpLib.ssfrag
  val PERM_SIMPLE_ss : simpLib.ssfrag

  (* brings the permutation assumptions in normal form *)
  val NORMALISE_ASM_PERM_TAC : tactic

  (* Prove `ALL_DISTINCT xs = T` by permuting to a sorted list
     (using theorems ALL_DISTINCT_PERM and SORTED_ALL_DISTINCT).

     Requires a relation R, a theorem `irreflexive R /\ transitive R`
     a sorting function f which sorts the terms of xs in ML, and a
     conversion that shows `R x y = T` whenever f `x` `y`.
  *)
  val ALL_DISTINCT_CONV : thm -> (term -> term -> bool) -> conv -> conv

end
