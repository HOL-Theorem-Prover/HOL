(*
 * PIntMap: Maps over integers implemented as Patricia trees.
 * Copyright (C) 2000 Jean-Christophe FILLIATRE
 *
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 *
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file LGPL).

 * Translated to SML by Michael Norrish, 2001.
 *)

signature PIntMap =
sig

type 'a t

type key = int
exception NotFound

val empty : 'a t

val add : int -> 'a -> 'a t -> 'a t

val addf : ('a -> 'a) -> int -> 'a -> 'a t -> ('a t * 'a)

val find : int -> 'a t -> 'a

val remove : int -> 'a t -> 'a t

val mem :  int -> 'a t -> bool

val app : (int * 'a -> unit) -> 'a t -> unit

val map : ('a -> 'b) -> 'a t -> 'b t

val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t

val fold : (int * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b

val choose : 'a t -> 'a t * (int * 'a)

val size : 'a t -> int

end
