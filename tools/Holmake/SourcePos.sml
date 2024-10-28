(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-1999 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * Please see the file MLton-LICENSE for license information.

 * Slightly adjusted by Michael Norrish (2006)

 *)

structure SourcePos :> SourcePos =
struct

datatype t = T of {column: int, file: string, line: int}

local
   fun f g (T r) = g r
in
   val column = f #column
   val line = f #line
end

fun compare (T {column = c, file = f, line = l},
             T {column = c', file = f', line = l'}) =
   case String.compare (f, f') of
      EQUAL =>
         (case Int.compare (l, l') of
             EQUAL => Int.compare (c, c')
           | r => r)
    | r => r

fun equals (T r, T r') = r = r'

fun make {column, file, line} =
   T {column = column,
      file = file,
      line = line}

fun file (p as T {file, ...}) = file

val bogus = T {column = ~1,
               file = "<bogus>",
               line = ~1}

fun toString (p as T {column, line, ...}) =
   String.concat [file p, " ", Int.toString line, ".", Int.toString column]

fun posToString (T {column,line,...}) =
   String.concat [Int.toString line, ".", Int.toString column]

end
