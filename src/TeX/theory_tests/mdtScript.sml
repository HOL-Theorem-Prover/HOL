Theory mdt

val _ = new_type ("char", 0)

val _ = type_abbrev_pp("string", ``:char list``)

Datatype:
  term = Var string type
       | Const string type const_tag
       | Comb term term
       | Abs string type term
       ;
   type = Tyvar string
       | Tyapp type_op (type list)
       ;
   type_op =
     Typrim string num
   | Tydefined string term
       ;
   const_tag =
     Prim
   | Defined num ((string # term) list) term
   | Tyabs string term
   | Tyrep string term
End

Datatype: testrcd = <| fld1 : bool ; fld2 : 'a -> num |>
End
