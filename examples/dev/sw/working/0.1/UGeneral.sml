(*
 *  util/general.sml  --  some generally useful utilities
 *
 *  COPYRIGHT (c) 1997 by Martin Erwig.  See COPYRIGHT file for details.
 *)

structure UGeneral =
struct
  fun id x = x
  fun eq x y = x=y
  fun neq x y = not (x=y)
  infix 5 to
  fun n to m = if n > m then [] else n::(n+1 to m)
end
