(* ===================================================================== *)
(* FILE          : Net.sig                                               *)
(* DESCRIPTION   : Signature for term nets.                              *)
(*                                                                       *)
(* AUTHOR        : ICL HOL group.                                        *)
(* DATE          : August 26, 1991                                       *)
(* Modified      : September 23, 1997, Ken Larsen                        *)
(* Rewritten and                                                         *)
(* Expanded      : July 17, 1999, Konrad Slind                           *)
(* ===================================================================== *)

signature Net =
sig
  type 'a net
  type term = Term.term

  val empty     : 'a net
  val insert    : term * 'a -> 'a net -> 'a net
  val match     : term -> 'a net -> 'a list
  val index     : term -> 'a net -> 'a list
  val delete    : term * ('a -> bool) -> 'a net -> 'a net
  val filter    : ('a -> bool) -> 'a net -> 'a net
  val union     : 'a net -> 'a net -> 'a net
  val map       : ('a -> 'b) -> 'a net -> 'b net
  val itnet     : ('a -> 'b -> 'b) -> 'a net -> 'b -> 'b
  val size      : 'a net -> int
  val listItems : 'a net -> 'a list

  val enter     : term * 'a -> 'a net -> 'a net  (* for compatibility *)
  val lookup    : term -> 'a net -> 'a list      (* for compatibility *)


(*---------------------------------------------------------------------------

    A term net is a collection of items, each of which can be thought
    of as being indexed by a path which is computed from a term which
    is supplied when the item is inserted into the net. Type information,
    and the names of variables, is not represented in paths, so more than
    one term may be indexed by the same path, i.e., the extraction
    operations are not exact. In this sense, term nets are akin to
    hash tables.

  [empty] is the empty term net.

  [insert (tm, x) net]

    The term tm is used as a key to compute a path at which to
    store x in net. If the path does not already exist in net,
    it is created. Note that insert merely adds x to the net;
    if x has already been stored under tm, then it is not overwritten.

  [match tm net]

    Term nets can be used to cut down on the number of match attempts
    that a matching function would have to make, say when rewriting
    with a collection of theorems. "match tm net" will return every
    element that has been inserted into the net using a term M as the
    key, such that M possibly matches tm. The matches are returned in
    "most specific match first" order.

   [index tm net]

    An alternative use of term nets ignores any paths in the net
    arising from clearly non-alpha-convertible terms. "index" is a more
    discriminating entrypoint than "match", in the sense that the set
    of results is always a subset of those returned for matches.

   [delete (tm,P) net] uses tm as an index into the net. There can be
     more than one element indexable by tm. The net resulting from
     removing all such elements that also meet the predicate P is
     returned.

   [filter P net] The net resulting from removing all elements meeting
      P is returned.

   [union net1 net2] joins net1 and net2. Looking up or fetching
     an element from the result should return the union of the
     results of separately fetching or looking up in net1 and net2.

   [map f net] returns a new net, each element of which has had f
     applied to it.

   [itnet f net b] folds function f through net, with base value b.

   [size net] returns the number of elements in the net.

   [listItems net] lists the elements in the net, in no particular order.

   [enter (tm,x) net] An outdated version of insert, kept for compatibility.

   [lookup tm net] An outdated version of match, kept for compatibility.

 ---------------------------------------------------------------------------*)
end;
