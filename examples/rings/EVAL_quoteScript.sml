Theory EVAL_quote
Ancestors
  ternaryComparisons
Libs
  TotalDefn Datatype BasicProvers

Datatype:
   index = Left_idx of index
         | Right_idx of index
         | End_idx
End

Definition index_compare_def:
   (index_compare End_idx End_idx = EQUAL)
/\ (index_compare End_idx i = LESS)
/\ (index_compare i End_idx = GREATER)
/\ (index_compare (Left_idx n') (Left_idx m') = (index_compare n' m'))
/\ (index_compare (Left_idx n') (Right_idx m') = LESS)
/\ (index_compare (Right_idx n') (Right_idx m') = (index_compare n' m'))
/\ (index_compare (Right_idx n') (Left_idx m') = GREATER)
End


fun type_rws ty = #rewrs (TypeBase.simpls_of ty)

val index_discr = tl (type_rws ``:index``);


val compare_index_equal = store_thm("compare_index_equal",
  “!i1 i2. (index_compare i1 i2 = EQUAL) = (i1 = i2)”,
Induct THEN Induct THEN
RW_TAC bool_ss (index_compare_def :: index_discr));


val compare_list_index = save_thm(
  "compare_list_index",
  MATCH_MP compare_equal compare_index_equal);


Definition index_lt_def:    index_lt i1 i2 = (index_compare i1 i2 = LESS)
End


Datatype:
   varmap =
     Empty_vm
   | Node_vm of 'a => varmap => varmap
End


Definition varmap_find_def:
   (varmap_find End_idx        (Node_vm x v1 v2) = x:'a)
/\ (varmap_find (Right_idx i1) (Node_vm x v1 v2) = varmap_find i1 v2)
/\ (varmap_find (Left_idx i1)  (Node_vm x v1 v2) = varmap_find i1 v1)
/\ (varmap_find i v = @x.T)
End


