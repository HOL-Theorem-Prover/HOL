signature datatypeSimpLib =
sig
  include Abbrev

  (* The `datatype_simp` theorem set.  A theorem tagged with the
     attribute is used to normalise the induction principle of every
     type declared after it, in the theories that can see it.

       Theorem IN_optSET[datatype_simp]:
         e IN optSET opt <=> (opt = SOME e)
       Proof ... QED

     Nothing is tagged to begin with.  What a blank slate does is
     described at normalise_induction below. *)
  val datatype_simps : unit -> thm list
  val add_datatype_simp : string -> unit  (* a theorem's name; this session only *)

  (* Normalise an induction principle's hypotheses.  Without any
     tagged theorem this pulls the existentials out of the clause
     antecedents and unwinds the equalities that leaves, which is a
     rephrasing rather than a change of content; a tagged theorem can
     take it further.  The conclusion is never rewritten.

     Returns the principle unchanged, with a message, if the
     normalisation raises: a declaration must not fail because of a
     theorem somebody tagged. *)
  val normalise_induction : thm -> thm
end
