signature DB =
sig

 type term = Term.term
 type thm = Thm.thm
 type 'a quotation = 'a Portable.frag list

 datatype class = Thm | Axm | Def
 
 type data = (string * string) * (thm * class)

  val thy           : string -> data list
  val theorems      : string -> (string * thm) list
  val find          : string -> data list
  val matchp        : (thm -> bool) -> string list -> data list
  val matcher       : (term -> term -> 'a) -> string list -> term -> data list
  val match         : string list -> term -> data list 
  val apropos       : term -> data list 
  val theorem       : string -> string -> thm
  val theorem_class : string -> string -> thm * class
  val all_thms      : unit -> data list

  val bindl : string -> (string * thm * class) list -> unit

(*
 [thy] returns data for the specified theory segment. Case distinctions
    are ignored when determining the segment. The current segment may
    be specified, either by the distinguished literal "-", or by the
    full name.
       
 [theorems] returns a (name,thm) pair for each entry in the specified 
     theory segment. Case distinctions are ignored when determining the
     segment. The current segment may be specified, either by "-", or by 
     the full name.

 [find] searches through all known entries, returning those data elements 
    that have binding names in which the given string occurs. Case
    distinctions between the binding names and the specified string are
    ignored.

 [matchp] Given a list of segments to search in, returns those data 
    elements such that the conclusion of the theorem projection satisfies
    the predicate.  If the input list is empty, all segments are searched,
    including the current one.

 [matcher] Given a list of segments to search in, returns those data 
    elements such that the supplied matching function matches some
    subterm of the theorem projection.  If the input list is empty, all
    segments are searched, including the current one.

 [match] Instantiation of matcher with standard higher-order matcher.

 [apropos] Calls match with first argument = [].

 [theorem] Return the specified theorem in the specified theory segment. 
    The literal "-" may be used as an abbreviation for the current segment.
    Case distinctions between both the segment name and the theorem name, 
    and those of the stored entries are ignored,

 [theorem_class] behaves the same as "theorem", except that the class
    of the theorem is also included.

 [all_thms] Everything in the database.

*)

end;
