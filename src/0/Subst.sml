(* ======================================================================== *)
(* FILE          : Subst.sml                                                *)
(* DESCRIPTION   : Explicit substitutions                                   *)
(*                                                                          *)
(* AUTHOR        : (c) Bruno Barras, Cambridge University and               *)
(*                                   INRIA Rocquencourt                     *)
(* DATE          : 1999                                                     *)
(*                                                                          *)
(*                                                                          *)
(* Type of explicit substitutions on an abstract type of term 'a.           *)
(*                                                                          *)
(* - Id is the identity substitution                                        *)
(*     { 0/0 .... i/i ... }                                                 *)
(*                                                                          *)
(* - Cons(S,T) is the parallel substitution                                 *)
(*     { T/0 S(0)/1 .... S(i-1)/i ... }                                     *)
(*                                                                          *)
(* - Shift(k,S) is substitution S followed by a relocation of k:            *)
(*     { k/0 .... i+k/i ... } o S   or  { ^k(S(0))/0 ... ^k(S(i))/i ... }   *)
(*                                                                          *)
(* - Lift(k,S) applies S without affecting the k last variables:            *)
(*     { 0/0 ... k-1/k-1  ^k(S(0))/k ...  ^k(S(i))/k+i ... }                *)
(* ======================================================================== *)


structure Subst :> Subst =
struct

datatype 'a subs =
    Id
  | Cons  of 'a subs * 'a
  | Shift of int * 'a subs
  | Lift  of int * 'a subs
;

(*---------------------------------------------------------------------------
 * These constructors allow the following invariants to be asserted:
 *
 *  - shifts and lifts always collapsed (and non-zero)
 *  - no Lift(_,Id), which is equivalent to Id
 *
 *---------------------------------------------------------------------------*)

val id = Id;

val cons = Cons;

fun shift (0, s)           = s
  | shift (k, Shift(k',s)) = shift(k+k', s)
  | shift (k, s)           = Shift(k,s)
;

fun lift (0, s)          = s
  | lift (k, Id)         = Id
  | lift (k, Lift(k',s)) = lift(k+k', s)
  | lift (k, s)          = Lift(k,s)
;

fun is_id Id = true
  | is_id _ = false;


(*---------------------------------------------------------------------------
 * Destructor: applies substitution subs to de Bruijn index db. In other
 * words, sigma-reduces [subs]db.
 * Returns:
 *  - (n,SOME t) when db is bound by a Cons(_,t). n is the number of variables
 *    to relocate t. i.e.    [subs]db reduces to ^n(t)
 *  - (n,NONE) when variable db was bound by a Lift or Id. This means that
 *    [subs]db reduces to n.
 *---------------------------------------------------------------------------*)

fun exp_rel (subs,db) =
  let fun exp (lams, Id,         n) = (lams+n, NONE)
        | exp (lams, Cons(s,x),  0) = (lams, SOME x)
	| exp (lams, Cons(s,x),  n) = exp(lams, s, n-1)
	| exp (lams, Shift(k,s), n) = exp(lams+k, s, n)
	| exp (lams, Lift(k,s),  n) = if n < k then (lams+n, NONE)
	                              else exp(lams+k, s, n-k)
  in exp(0,subs,db)
  end
;

(*---------------------------------------------------------------------------
 * Composition of 2 substitution. We need to provide a function [mk_cl] that
 * given a subst S and a term t, builds the term [S]t.
 *
 * There is a critical pair: (Shift(k,s)) o (Cons(s',x)) could be reduced in
 * 2 ways:
 *     Cons(shift k (s o s'), mk_cl (Shift(k,s)) x)
 *  or shift k (Cons (s o s', mk_cl s x)) <-- was prefered
 *---------------------------------------------------------------------------*)

fun comp mk_cl =
  let fun Id           o s'             = s'
	| s            o Id             = s
        | (Shift(k,s)) o s'             = shift(k, s o s')
	| s            o (Cons(s',x))   = Cons(s o s', mk_cl(s,x))
	| (Cons(s,x))  o (Shift(k,s'))  = s o shift(k-1, s')
	| (Cons(s,x))  o (Lift(k,s'))   = Cons(s o lift(k-1, s'), x)
	| (Lift(k,s))  o (Shift(k',s')) = if k<k'
                                          then shift(k, s o shift(k'-k, s'))
                                          else shift(k', lift(k-k', s) o s')
	| (Lift(k,s))  o (Lift(k',s'))  = if k<k'
	                                  then lift(k, s o lift(k'-k, s'))
                                          else lift(k', lift(k-k', s) o s')
  in (op o)
  end
;


end;
