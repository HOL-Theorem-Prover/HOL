open HolKernel Parse boolLib bossLib;

val _ = new_theory "mdt";

val _ = new_type ("char", 0)

val _ = type_abbrev("string", ``:char list``)

val _ = Hol_datatype`
  term = Var of string => type
       | Const of string => type => const_tag
       | Comb of term => term
       | Abs of string => type => term
       ;
   type = Tyvar of string
       | Tyapp of type_op => type list
       ;
   type_op =
     Typrim of string => num
   | Tydefined of string => term
       ;
   const_tag =
     Prim
   | Defined of num => (string # term) list => term
   | Tyabs of string => term
   | Tyrep of string => term
`;

val _ = Datatype`testrcd = <| fld1 : bool ; fld2 : 'a -> num |>`;

val _ = export_theory();
