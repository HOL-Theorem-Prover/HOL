(* -------------------------------------------------------------------------
   Pure Maps
   ------------------------------------------------------------------------- *)

structure PureMap :> PureMap =
struct

val arrayBits = 0w16
val arraySize = IntInf.<< (1, arrayBits)
val arrayMask = arraySize - 1

fun inRange v = fn NONE => true | SOME s => v < s

datatype 'a map =
     Vector of 'a Vector.vector
   | VTree of int option * 'a * 'a Vector.vector Ptree.ptree

fun mkMap (x as (s, d)) =
   case s of
      SOME sz => if sz < arraySize
                    then Vector (Vector.tabulate (sz, fn _ => d))
                 else VTree (s, d, Ptree.Empty)
    | NONE => VTree (s, d, Ptree.Empty)

fun lookup (Vector a, v) = Vector.sub (a, v)
  | lookup (VTree (s, d, t), v) =
      let
         val top = IntInf.~>> (v, arrayBits)
      in
         case Ptree.peek (t, top) of
            SOME a => Vector.sub (a, IntInf.andb (v, arrayMask))
          | NONE => if inRange v s then d else raise Subscript
      end

fun update (Vector a, v, d) = Vector (Vector.update (a, v, d))
  | update (VTree (s, d, t), v, e) =
      let
         val top = IntInf.~>> (v, arrayBits)
         val bottom = IntInf.andb (v, arrayMask)
      in
         case Ptree.peek (t, top) of
            SOME a =>
               VTree (s, d, Ptree.add (t, (top, Vector.update (a, bottom, e))))
          | NONE => if inRange v s
                       then let
                               val a =
                                  Vector.tabulate
                                     (arraySize,
                                      fn i => if i = bottom then e else d)
                            in
                               VTree (s, d, Ptree.add (t, (top, a)))
                            end
                    else raise Subscript
      end

fun copy x = x

end (* structure PureMap *)

(*

open PureMap

val m = mkMap (NONE, 0);
val m = update (m, 1, 1);
val p = m;
val m = update (m, 1, 2);
val v = lookup (p, 1);

*)
