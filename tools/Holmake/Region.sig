(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-1999 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * Please see the file MLton-LICENSE for license information.
 *)
signature Region =
   sig

      type t

      val <= : t * t -> bool
      val append: t * t -> t
      val bogus: t
      val compare: t * t -> order
      val equals: t * t -> bool
      val extendRight: t * SourcePos.t -> t
      val left: t -> SourcePos.t option
      val list: 'a list * ('a -> t) -> t
      val make: {left: SourcePos.t, right: SourcePos.t} -> t
      val right: t -> SourcePos.t option
      val toString: t -> string

      structure Wrap:
	 sig
	    type region
	    type 'a t
	    val region: 'a t -> region
	    val node: 'a t -> 'a
	    val makeRegion: 'a * region -> 'a t
	    val makeRegion':  'a * SourcePos.t * SourcePos.t -> 'a t
	    val dest: 'a t -> 'a * region
	 end
      sharing type Wrap.region = t
   end
