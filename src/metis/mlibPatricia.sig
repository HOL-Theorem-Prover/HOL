(* ========================================================================= *)
(* mlibPatricia: Maps over integers implemented as mlibPatricia trees.               *)
(* Copyright (c) 2000 Jean-Christophe Filliatre, 2001 Michael Norrish        *)
(*                                                                           *)
(* This software is free software; you can redistribute it and/or            *)
(* modify it under the terms of the GNU Library General Public               *)
(* License version 2, as published by the Free Software Foundation.          *)
(*                                                                           *)
(* This software is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of            *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                      *)
(* ========================================================================= *)

signature mlibPatricia =
sig

type 'a t

type key = int
exception NotFound

val empty   : 'a t
val add     : key -> 'a -> 'a t -> 'a t
val addf    : ('a -> 'a) -> key -> 'a -> 'a t -> 'a t
val find    : key -> 'a t -> 'a
val remove  : key -> 'a t -> 'a t
val mem     : key -> 'a t -> bool
val app     : (key * 'a -> unit) -> 'a t -> unit
val map     : ('a -> 'b) -> 'a t -> 'b t
val mapi    : (key -> 'a -> 'b) -> 'a t -> 'b t
val fold    : (key * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b
val getItem : 'a t -> ((key * 'a) * 'a t) option
val size    : 'a t -> int

end
