(* Modified for Moscow ML from SML/NJ Library 0.2 file dynamic-array.sml
 *
 * COPYRIGHT (c) 1993 by AT&T Bell Laboratories.
 * See file mosml/copyrght/copyrght.att for details.
 *
 * Arrays of unbounded length
 *
 *)

structure Dynarray :> Dynarray =
struct

datatype 'elem array = BLOCK of 'elem Array.array ref * 'elem

fun array (sz, dflt) = BLOCK (ref (Array.array (sz, dflt)), dflt)

fun subArray (BLOCK (arr, dflt), lo, hi) =
   let
      val arrval = !arr
      fun copy i = Array.sub (arrval, i + lo) handle _ => dflt
   in
      BLOCK (ref (Array.tabulate (hi - lo, copy)), dflt)
   end

fun fromList (initlist, dflt) = BLOCK (ref (Array.fromList initlist), dflt)

fun tabulate (sz, fillfn, dflt) =
   BLOCK (ref (Array.tabulate (sz, fillfn)), dflt)

fun default (BLOCK (_, dflt)) = dflt

fun sub (BLOCK (arr, dflt), idx) =
   Array.sub (!arr, idx)
   handle Subscript => if idx < 0 then raise Subscript else dflt

fun bound (BLOCK (arr, _)) = Array.length (!arr)

fun expand (arr, oldlen, newlen, dflt) =
   let
      fun fillfn i = if i < oldlen then Array.sub (arr, i) else dflt
   in
      Array.tabulate (newlen, fillfn)
   end

fun update (b as BLOCK (arr, dflt), idx, v) =
   let
      fun max (x, y: int) = if x > y then x else y
      val len = bound b
   in
      if idx >= len
         then arr := expand (!arr, len, max (len + len, idx + 1), dflt)
      else ()
      ; Array.update (!arr, idx, v)
   end

end
