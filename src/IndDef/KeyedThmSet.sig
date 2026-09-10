signature KeyedThmSet =
sig

  type thm = Thm.thm

  (* A keyed theorem set is a ThmSetData-backed store of theorems indexed
     by the constants they talk about.  Each theorem is expected to look
     like

        |- !vs. premises ==> clause_1 /\ ... /\ clause_n

     with every clause of the form  !us. hyp ==> concl.  One of hyp and
     concl is designated the key part; its head must be a constant, and
     the theorem is filed under that constant's kernel name.

     Rule induction theorems key on the hypothesis (in
        !x. R x ==> P x
     the relation is R), coinduction theorems on the conclusion (in
        !x. P x ==> R x
     it is again R).  *)

  datatype clause_part = Hypothesis | Conclusion

  type keyed_thm_map = thm list KNametab.table
  type keyed_thm_set

  val new : {settype : string, key_part : clause_part} -> keyed_thm_set

  val add           : keyed_thm_set -> thm -> unit
  val export_thm    : keyed_thm_set -> string -> unit
  val thy_thms      : keyed_thm_set -> string -> thm list
  val get_map       : keyed_thm_set -> unit -> keyed_thm_map
  val map_by_theory : keyed_thm_set -> {thyname : string} ->
                      keyed_thm_map option

end

(*
   [new {settype, key_part}] creates a new keyed theorem set, exported
   under the ThmSetData set-type settype.  As a side effect this
   registers settype as a theorem attribute, so that theorems can be
   added with  Theorem foo[settype]: ...

   [add sset th] adds th to sset for the current session only.

   [export_thm sset name] adds the theorem saved under name to sset and
   records the addition in the current theory, so that descendant
   theories pick it up.  If name's theorem is not of the expected shape
   nothing is recorded.

   [thy_thms sset thyname] returns the theorems added to sset by theory
   thyname.

   [get_map sset ()] returns the whole set as a map from constants to
   the theorems filed under them.

   [map_by_theory sset {thyname}] returns the map as it stands after
   loading thyname and its ancestors.
*)
