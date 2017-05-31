(* -------------------------------------------------------------------------
   Mutable Maps
   ------------------------------------------------------------------------- *)

functor MutableMap (val arrayBits : Word.word) :> Map =
struct

val arraySize = IntInf.<< (1, arrayBits)
val arrayMask = arraySize - 1

fun inRange v = fn NONE => true | SOME s => IntInf.< (v, s)

datatype 'a map =
     Array of 'a Array.array
   | Tree of IntInf.int option * 'a * 'a Array.array Ptree.ptree

fun mkMap (x as (s, d)) =
   case s of
      SOME sz => if sz < arraySize
                    then Array (Array.array (IntInf.toInt sz, d))
                 else Tree (s, d, Ptree.Empty)
    | NONE => Tree (s, d, Ptree.Empty)

fun lookup (Array a, v) = Array.sub (a, IntInf.toInt v)
  | lookup (Tree (s, d, t), v) =
      let
         val top = IntInf.~>> (v, arrayBits)
      in
         case Ptree.peek (t, top) of
            SOME a => Array.sub (a, IntInf.toInt (IntInf.andb (v, arrayMask)))
          | NONE => if inRange v s then d else raise Subscript
      end

fun update (Array a, v, d) = (Array.update (a, IntInf.toInt v, d); Array a)
  | update (Tree (s, d, t), v, e) =
      let
         val top = IntInf.~>> (v, arrayBits)
         val bottom = IntInf.toInt (IntInf.andb (v, arrayMask))
      in
         case Ptree.peek (t, top) of
            SOME a => (Array.update (a, bottom, e); Tree (s, d, t))
          | NONE => if inRange v s
                       then let
                               val a = Array.array (IntInf.toInt arraySize, d)
                               val () = Array.update (a, bottom, e)
                            in
                               Tree (s, d, Ptree.add (t, (top, a)))
                            end
                    else raise Subscript
      end

fun copyArray a = Array.tabulate (Array.length a, fn i => Array.sub (a, i))

fun copy (Array a) = Array (copyArray a)
  | copy (Tree (s, d, t)) = Tree (s, d, Ptree.transform copyArray t)

end (* functor MutableMap *)

(*

open MutableMap

val m = mkMap (NONE, 0);
val m = update (m, 1, 1);
val p = m;
val m = update (m, 1, 2);
val v = lookup (p, 1);

val m = mkMap (NONE, 0);
val m = update (m, 1, 1);
val p = copy m;
val m = update (m, 1, 2);
val v = lookup (p, 1);

*)
