(* File: tv.sml, supplied by Brian Graham  *)

app load ["nested_recLib","listTheory"];

val _ = new_theory "test2";

local open DefTypeInfo
in
val spec =  (* test2 ::= terminal2 | nonterminal2 of ('a * test2) list  *)
 [{type_name = "test2",
   constructors =
     [{name = "terminal2", arg_info = []},
      {name = "nonterminal2",
       arg_info = [type_op{Tyop="list",
                    Args = [type_op{Tyop = "prod",
                              Args = [existing (Type`:'a`),
                                      being_defined "test2"]}]}]}]}]
end;

val {Cases_Thm, 
     Constructors_Distinct_Thm,
     Constructors_One_One_Thm, 
     New_Ty_Existence_Thm,
     New_Ty_Induct_Thm, 
     New_Ty_Uniqueness_Thm} = nested_recLib.define_type
                                spec [pairTheory.pair_Axiom,
                                      listTheory.list_Axiom];


(*---------------------------------------------------------------------------
 * Lists.
 *---------------------------------------------------------------------------*)
local open DefTypeInfo
in
val spec =  (* fSeq ::= end | L of 'a # fSeq  *)
 [{type_name = "fSeq",
   constructors =
     [{name = "end", arg_info = []},
      {name = "L",
       arg_info = [type_op{Tyop="prod",
                    Args = [existing (Type`:'a`), being_defined "fSeq"]}]}]}]
end;

val {Cases_Thm, 
     Constructors_Distinct_Thm,
     Constructors_One_One_Thm, 
     New_Ty_Existence_Thm,
     New_Ty_Induct_Thm, 
     New_Ty_Uniqueness_Thm} = nested_recLib.define_type
                                spec [pairTheory.pair_Axiom];


(*---------------------------------------------------------------------------
 * Ken Larsen lists.
 *---------------------------------------------------------------------------*)
local open DefTypeInfo
in
val spec =  (* kll ::= end | KL of kll  *)
 [{type_name = "kll",
   constructors =
     [{name = "end", arg_info = []},
      {name = "KL",
       arg_info = [type_op{Tyop="prod",
                    Args = [existing (Type`:'a`), being_defined "fSeq"]}]}]}]
end;

val {Cases_Thm, 
     Constructors_Distinct_Thm,
     Constructors_One_One_Thm, 
     New_Ty_Existence_Thm,
     New_Ty_Induct_Thm, 
     New_Ty_Uniqueness_Thm} = nested_recLib.define_type
                                spec [pairTheory.pair_Axiom];



(*---------------------------------------------------------------------------
 * Here's a difficult one ... it doesn't work in the current package.
 *
 * local open DefTypeInfo
 * in
 * val spec =  (* hard ::= A of 'a | B of ('a * 'a) hard  *)
 *  [{type_name = "test2",
 *   constructors =
 *     [{name = "A", arg_info = [existing(Type`:'a`)]},
 *      {name = "B",
 *       arg_info = [type_op{Tyop="hard",
 *                    Args = [type_op{Tyop = "prod",
 *                              Args = [existing (Type`:'a`),
 *                                      existing (Type`:'a`)]}]}]}]}]
 * end;
 *
 * val {Cases_Thm, 
 *      Constructors_Distinct_Thm,
 *      Constructors_One_One_Thm, 
 *      New_Ty_Existence_Thm,
 *      New_Ty_Induct_Thm, 
 *      New_Ty_Uniqueness_Thm} = nested_recLib.define_type
 *                                 spec [pairTheory.pair_Axiom];
 *---------------------------------------------------------------------------*)