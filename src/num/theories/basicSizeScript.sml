open HolKernel Parse boolLib Prim_rec
     pairTheory sumTheory optionTheory numeralTheory;


val _ = new_theory "basicSize";

val bool_size_def = new_definition
  ("bool_size_def", ``bool_size (b:bool) = 0``);

val min_pair_size_def = new_definition
  ("min_pair_size_def", ``min_pair_size f g (x, y) = f x + g y``);

val pair_size_def = new_definition
  ("pair_size_def", ``pair_size f g (x, y) = 1 + (f x + g y)``);

val one_size_def = new_definition
  ("one_size_def", ``one_size (x:one) = 0``);

val itself_size_def = new_definition
  ("itself_size_def", ``itself_size (x : 'a itself) = 0``);

val sum_size_def =
 new_recursive_definition
   {def = ``(sum_size (f:'a->num) g (INL x) = f x) /\
            (sum_size f (g:'b->num) (INR y) = g y)``,
    name="sum_size_def",
    rec_axiom = sumTheory.sum_Axiom};

val full_sum_size_def = new_definition
  ("full_sum_size_def", ``full_sum_size f g sum = 1 + (sum_size f g sum)``);
val full_sum_size_thm = Q.store_thm ("full_sum_size_thm",
  `(full_sum_size f g (INL x) = 1 + (f x)) /\
    (full_sum_size f g (INR y) = 1 + (g y))`,
  REWRITE_TAC [full_sum_size_def, sum_size_def]);

val option_size_def =
 new_recursive_definition
   {def = ``(option_size f NONE = 0) /\
            (option_size f (SOME x) = 1 + (f x))``,
    name="option_size_def",
    rec_axiom = optionTheory.option_Axiom};

val _ = export_theory();
