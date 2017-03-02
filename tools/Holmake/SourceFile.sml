(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-1999 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * Please see the file MLton-LICENSE for license information.
 *)

structure SourceFile :> SourceFile =
struct

datatype t = T of {file: string ref,
                   lineNum: int ref,
                   lineStart: int ref}

fun getPos (T {file, lineNum, lineStart, ...}, n) =
   SourcePos.make {column = n - !lineStart,
                   file = !file,
                   line = !lineNum}

fun lineStart (s as T {lineStart, ...}) = getPos (s, !lineStart)

val observe_line_directives = ref true

fun new file = T {file = ref file,
                  lineNum = ref 1,
                  lineStart = ref 0}

fun newline (T {lineStart, lineNum, ...}, n) =
   (lineNum := !lineNum + 1
    ; lineStart := n)

fun lineDirective (src as T {file, lineNum, lineStart},
                   f,
                   {lineNum = n, lineStart = s}) =
    if !observe_line_directives then
      (Option.app (fn f => file := f) f
       ; lineNum := n
       ; lineStart := s)
    else newline(src,s)



end;
