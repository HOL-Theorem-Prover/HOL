signature DB =
sig

 type term = Term.term
 type thm = Thm.thm

 type data = AncestorDB.data

 (* returns data for every theory which has a name in which the given string
    occurs, ignoring case *)
 val thy    : string -> data list

 (* returns those data elements that have names in which the given string
    occurs, again ignoring case *)
 val find   : string -> data list

 (* Given a list of theories to use (again, any theory that has a string
    from the list occurring as a substring), returns those data elements
    whose conclusions satisfy the predicate.  If the list is empty, all
    theories are examined (including the current one). *)
 val rawfind : string list -> (Term.term -> bool) -> data list

 (* First argument as above, second is a term that must match a sub-term
    in the returned element's conclusion *)
 val match  : string list -> Term.term -> data list (* first order matches *)

 (* functions to access all of the stored theorems, where the first string
    parameter to all four is the string of the theory name, allowing
    "-" as an abbreviation for the current theory. *)
 val theorem : string -> string -> thm
 val theorems : string -> (string * thm) list
 val gen_theorem : string -> string -> thm * Thm.thmclass
 val gen_theorems : string -> (string * thm * Thm.thmclass) list

 val all_thms : unit -> data list

end;
