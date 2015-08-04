(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-1999 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * Please see the file MLton-LICENSE for license information.

 * Slightly adjusted by Michael Norrish (2006)

 *)

signature SourcePos =
sig

  type t

  val bogus: t
  val column: t -> int
  val compare: t * t -> order
  val equals: t * t -> bool
  val file: t -> string
  val line: t -> int
  val make: {column: int, file: string, line: int} -> t
  val toString: t -> string
  val posToString : t -> string
end
