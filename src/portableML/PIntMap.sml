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
 *
 * Translated to SML by Michael Norrish, 2001
 *)

(*s Maps of integers implemented as Patricia trees, following Chris
    Okasaki and Andrew Gill's paper {\em Fast Mergeable Integer Maps}
    ({\tt\small http://www.cs.columbia.edu/\~{}cdo/papers.html\#ml98maps}).
    See the documentation of module [Ptset] which is also based on the
    same data-structure. *)

structure PIntMap :> PIntMap =
struct

type key = int

datatype 'a t =
         Empty
       | Leaf of int * 'a
       | Branch of int * int * 'a t * 'a t * int
exception NotFound

val empty = Empty

fun land (p, q) = Word.toIntX(Word.andb(Word.fromInt p, Word.fromInt q))
infix land

fun zero_bit k m = (k land m) = 0

fun mem k t =
    case t of
      Empty => false
    | Leaf (j,_) => k = j
    | Branch (_, m, l, r, _) => mem k (if zero_bit k m then l else r)

fun find k t =
    case t of
      Empty => raise NotFound
    | Leaf (j,x) => if k = j then x else raise NotFound
    | Branch (_, m, l, r, _) => find k (if zero_bit k m then l else r)

fun lowest_bit x = x land ~x

fun branching_bit p0 p1 =
    lowest_bit (Word.toIntX(Word.xorb(Word.fromInt p0, Word.fromInt p1)))

fun mask p m = p land (m-1)

fun size Empty = 0
  | size (Leaf _) = 1
  | size (Branch(_, _, _, _, sz)) = sz

fun join (p0,t0,p1,t1) = let
  val m = branching_bit p0 p1
  val sz = size t0 + size t1
in
  if zero_bit p0 m then
    Branch (mask p0 m, m, t0, t1, sz)
  else
    Branch (mask p0 m, m, t1, t0, sz)
end

fun match_prefix k p m = (mask k m) = p

fun addf f k x t = let
  fun ins t =
      case t of
        Empty => (Leaf (k,x), x)
      | Leaf (j,old) => if j = k then let val new = f old
                                      in (Leaf (k,new), new) end
                        else (join (k, Leaf (k,x), j, t), x)
      | Branch (p,m,t0,t1,sz) => if match_prefix k p m then
	                           if zero_bit k m then let
                                       val (t0', new) = ins t0
                                     in
	                               (Branch (p, m, t0', t1, sz+1), new)
                                     end
	                        else let
                                    val (t1', new) = ins t1
                                  in
	                            (Branch (p, m, t0, t1',sz+1), new)
                                  end
	                      else
	                        (join (k, Leaf (k,x), p, t), x)
in
  ins t
end

fun add k x t = #1 (addf (fn _ => x) k x t)

val branch = fn (_,_,Empty,t) => t
              | (_,_,t,Empty) => t
              | (p,m,t0,t1)   => Branch (p,m,t0,t1,size t0 + size t1)

fun remove k t = let
  fun rmv t =
      case t of
        Empty => Empty
      | Leaf (j,_) => if k = j then Empty else t
      | Branch (p,m,t0,t1,_) => if match_prefix k p m then
	                        if zero_bit k m then
	                          branch (p, m, rmv t0, t1)
	                        else
	                          branch (p, m, t0, rmv t1)
	                      else
	                        t
in
  rmv t
end

fun choose t =
    case t of
      Empty => raise NotFound
    | Leaf(k, x) => (Empty, (k, x))
    | Branch(p, m, t0, t1, _) => let
        val (t0', x) = choose t0
      in
        (branch(p,m,t0',t1), x)
      end

fun app f = fn Empty => ()
              | Leaf (k,x) => f (k, x)
              | Branch (_,_,t0,t1,_) => (app f t0; app f t1)

fun map f = fn Empty => Empty
             | Leaf (k,x) => Leaf (k, f x)
             | Branch (p,m,t0,t1,s) => Branch (p, m, map f t0, map f t1, s)

fun mapi f = fn Empty => Empty
              | Leaf (k,x) => Leaf (k, f k x)
              | Branch (p,m,t0,t1,s) => Branch (p, m, mapi f t0, mapi f t1, s)

fun fold f accu s = case s of
                      Empty => accu
                    | Leaf (k,x) => f (k, x, accu)
                    | Branch (_,_,t0,t1,_) => fold f (fold f accu t1) t0

end
