Theory basicSize[bare]
Ancestors
  pair sum option numeral
Libs
  HolKernel Parse boolLib pairLib Prim_rec

Definition bool_size_def[nocompute]: bool_size (b:bool) = 0
End

Definition min_pair_size_def[nocompute]: min_pair_size f g (x, y) = f x + g y
End

Definition pair_size_def[nocompute]: pair_size f g (x, y) = 1 + (f x + g y)
End

Definition one_size_def[nocompute]: one_size (x:one) = 0
End

Definition itself_size_def[nocompute]: itself_size (x : 'a itself) = 0
End

val sum_size_def =
 new_recursive_definition
   {def = ``(sum_size (f:'a->num) g (INL x) = f x) /\
            (sum_size f (g:'b->num) (INR y) = g y)``,
    name="sum_size_def",
    rec_axiom = sumTheory.sum_Axiom};

Definition full_sum_size_def[nocompute]: full_sum_size f g sum = 1 + (sum_size f g sum)
End
Theorem full_sum_size_thm:
   (full_sum_size f g (INL x) = 1 + (f x)) /\
    (full_sum_size f g (INR y) = 1 + (g y))
Proof
  REWRITE_TAC [full_sum_size_def, sum_size_def]
QED

val option_size_def =
 new_recursive_definition
   {def = ``(option_size f NONE = 0) /\
            (option_size f (SOME x) = 1 + (f x))``,
    name="option_size_def",
    rec_axiom = optionTheory.option_Axiom};

