(*  Title: 	sequence
    ID:         sequence.ML,v 1.3 1994/11/21 10:33:23 lcp Exp
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1988  University of Cambridge

Unbounded sequences implemented by closures.

RECOMPUTES if sequence is re-inspected.

Memoing, using polymorphic refs, was found to be slower!  (More GCs)

Modified by Donald Syme, November 1995, for inclusion in HOL.

*)


signature Sequence = sig
  type 'a seq
  val seq_append	: 'a seq * 'a seq -> 'a seq
  val seq_chop	: int * 'a seq -> 'a list * 'a seq
  val seq_cons	: 'a * 'a seq -> 'a seq
  val seq_filter	: ('a -> bool) -> 'a seq -> 'a seq
  val seq_flat	: 'a seq seq -> 'a seq
  val seq_hd	: 'a seq -> 'a
  val seq_interleave: 'a seq * 'a seq -> 'a seq
  val seq_iterate : ('a * 'b seq -> 'b seq) -> 'a seq * 'b seq -> 'b seq
  val list_of_seq : 'a seq -> 'a list
  val seq_mapp	: ('a -> 'b) -> 'a seq -> 'b seq -> 'b seq
  val seq_map	: ('a -> 'b) -> 'a seq -> 'b seq
  val seq_mapfilter :  ('a -> 'b) -> 'a seq -> 'b seq
  val seq_nil	: 'a seq
  val seq_print	: (int -> 'a -> unit) -> int -> 'a seq -> unit
  val seq_pull	: 'a seq -> ('a * 'a seq) option
  val seq_of_list	: 'a list -> 'a seq
  val mk_seq	: (unit -> ('a * 'a seq) option) -> 'a seq
  val seq_single	: 'a -> 'a seq
  val seq_tl	: 'a seq -> 'a seq
  val seq_diagonalize : 'a seq -> 'b seq -> ('a * 'b) seq
  val seq_permutations : 'a list -> 'a list seq
end (* sig *)


