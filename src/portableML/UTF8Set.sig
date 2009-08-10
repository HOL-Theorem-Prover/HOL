signature UTF8Set =
sig

  type t
  val add : t * string -> t
  val empty : t
  val addList : t * string list -> t
  val isEmpty : t -> bool
  val listItems : t -> string list
  val member : t * string -> bool

  val longest_pfx_member : t * string -> {pfx:string,rest:string} option

(*
   [t] is the type of sets of (UTF8-encoded) strings.  The implementation is
   a trie like structure.  If a malformed (in the sense of the UTF8
   encoding) string is passed to any of these functions then the UTF8.BadUTF8
   exception will be raised.

   [add(t,s)] adds the string s to the set t.

   [empty] is the empty set.

   [addList(t,slist)] adds the list of strings slist to t.

   [isEmpty t] returns true iff t does not contain any elements.

   [listItems t] returns the list of elements in t.

   [member(t,s)] returns true iff s is a member of t.

   [longest_pfx_member(t,s)] returns SOME{pfx,rest} when pfx is the longest
   prefix of s that is also a member of t, and rest is the rest of the string
   s.  If there is no prefix of s in t, then the function returns NONE.
*)

end
