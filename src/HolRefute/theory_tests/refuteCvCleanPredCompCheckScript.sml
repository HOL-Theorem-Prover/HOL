Theory refuteCvCleanPredCompCheck
Ancestors
  refuteCvCleanPredComp

(* Unlike [refuteCvCleanCheckScript]'s substring filter -- load-bearing
   there because that script declares its own [clean_tree]/[clean_enum]
   -- [refuteCvCleanPredCompScript] deliberately declares exactly two
   things of its own: the [predcomp_tree] datatype and the
   [predcomp_sg_listall] relation used by its user-datatype fixture.
   Every name either of those two declarations introduces is listed here
   explicitly; anything else surviving in this theory is Refute-created
   residue that should have been reverted. *)
val allowed_type_names = ["predcomp_tree"]

val allowed_constant_names =
  ["PredCompLeaf", "PredCompNode", "predcomp_tree_CASE",
   "predcomp_tree_size", "predcomp_sg_listall"]

val allowed_binding_names =
  ["predcomp_tree_TY_DEF", "predcomp_tree_size_def",
   "predcomp_tree_nchotomy", "predcomp_tree_induction",
   "predcomp_tree_distinct", "predcomp_tree_case_eq",
   "predcomp_tree_case_def", "predcomp_tree_case_cong",
   "predcomp_tree_Axiom", "predcomp_tree_11", "datatype_predcomp_tree",
   "predcomp_sg_listall_rules", "predcomp_sg_listall_ind",
   "predcomp_sg_listall_cases", "predcomp_sg_listall_strongind"]

val type_names = List.map #1 (Theory.types "refuteCvCleanPredComp")

val constant_names = List.map
  (fn tm => #Name (Term.dest_thy_const tm))
  (Theory.constants "refuteCvCleanPredComp")

val binding_names = List.map
  (fn ((_, name), _) => name)
  (DB.thy "refuteCvCleanPredComp")

val bad_types =
  List.filter (fn n => not (Lib.mem n allowed_type_names)) type_names
val bad_constants =
  List.filter (fn n => not (Lib.mem n allowed_constant_names))
    constant_names
val bad_bindings =
  List.filter (fn n => not (Lib.mem n allowed_binding_names))
    binding_names
val residue = bad_types @ bad_constants @ bad_bindings

val _ =
  if null residue then ()
  else
    raise Fail
      ("Refute predicate-compiler cv export residue: " ^
       String.concatWith ", " residue)
