(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-1999 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * Please see the file MLton-LICENSE for license information.
 *)
signature SourceFile =
   sig
      type t

      (* The pos in the following specs is a file position (e.g. yypos of mllex).
       *)
      val getPos: t * int -> SourcePos.t
      val observe_line_directives : bool ref
      val lineDirective:
           t * string option * {lineNum: int, lineStart: int} -> unit
      val lineStart: t -> SourcePos.t

      val new: string -> t
      val newline: t * int -> unit
   end;
