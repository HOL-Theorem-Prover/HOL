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



  (* Given a term ``PERM l1 l2`` this conversions sorts the lists l1 and l2.

     Example:

     PERM_NO_ELIM_NORMALISE_CONV ``PERM (x::l1++y::l2++l3) (y::l3++z::l2++l4)``

     |- PERM (x::l1++y::l2++l3) (y::l3++z::l2++l4) <=>
        PERM (x::y::(l1 ++ l2 ++ l3)) (y::z::(l2 ++ l3 ++ l4))
  )*
  val PERM_NO_ELIM_NORMALISE_CONV = fn : term -> thm


  (* Turns ``PERM l1 l2`` into ``PERM l2 l1`` iff l1 is in some sence
     smaller than l2. This is useful in combination with PERM_REWR_CONV.

     Exmaple:

     PERM_TURN_CONV ``PERM (x::l1) (y::z::l1 ++ l2 ++ l3)``

     |- PERM (x::l1) (y::z::l1 ++ l2 ++ l3) <=>
        PERM (y::z::l1 ++ l2 ++ l3) (x::l1)
  *)
  val PERM_TURN_CONV : term -> thm


  (* Combines PERM_ELIM_DUPLICATES_CONV, PERM_NO_ELIM_NORMALISE_CONV and
     PERM_TURN_CONV *)


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
     PERM_REWR_CONV (ASSUME ``PERM l1 [x;y;z]``) ``PERM (z::y::x'::l2) (l3++x'::l1)``

     [PERM l1 [x; y; z]]
       |- PERM (z::y::x'::l2) (l3 ++ x'::l1) <=> PERM (x::l3) l2 : thm
  *)
  val PERM_REWR_CONV : thm -> term -> thm


  (* A SSFRAG to use these PERM tools with the simplifier *)
  val PERM_ss : simpLib.ssfrag

end
