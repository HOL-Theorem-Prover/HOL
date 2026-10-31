signature Refute_ModelFinder_Peephole =
sig
  type n_ary_index = Refute_Forl.n_ary_index
  type formula = Refute_Forl.formula
  type int_expr = Refute_Forl.int_expr
  type rel_expr = Refute_Forl.rel_expr
  type decl = Refute_Forl.decl
  type expr_assign = Refute_Forl.expr_assign

  type name_pool =
    {rels: n_ary_index list,
     vars: n_ary_index list,
     formula_reg: int,
     rel_reg: int}

  val initial_pool : name_pool
  val not3_rel : n_ary_index
  val suc_rel : n_ary_index
  val suc_rels_base : int
  val unsigned_bit_word_sel_rel : n_ary_index
  val signed_bit_word_sel_rel : n_ary_index
  val nat_add_rel : n_ary_index
  val int_add_rel : n_ary_index
  val nat_subtract_rel : n_ary_index
  val int_subtract_rel : n_ary_index
  val nat_multiply_rel : n_ary_index
  val int_multiply_rel : n_ary_index
  val nat_divide_rel : n_ary_index
  val int_divide_rel : n_ary_index
  val nat_less_rel : n_ary_index
  val int_less_rel : n_ary_index
  val gcd_rel : n_ary_index
  val lcm_rel : n_ary_index
  val norm_frac_rel : n_ary_index
  val formula_for_bool : bool -> formula
  val atom_for_nat : int * int -> int -> int
  val max_int_for_card : int -> int
  val int_for_atom : int * int -> int -> int
  val atom_for_int : int * int -> int -> int
  val is_twos_complement_representable : int -> int -> bool
  val bit_width_for : int -> int -> int
  val suc_rel_for_atom_seq : int * int -> n_ary_index
  val atom_seq_for_suc_rel : n_ary_index -> int * int
  val inline_rel_expr : rel_expr -> bool
  val empty_n_ary_rel : int -> rel_expr
  val s_and : formula -> formula -> formula

  type kodkod_constrs =
    {kk_all: decl list -> formula -> formula,
     kk_exist: decl list -> formula -> formula,
     kk_formula_let: expr_assign list -> formula -> formula,
     kk_formula_if: formula -> formula -> formula -> formula,
     kk_or: formula -> formula -> formula,
     kk_not: formula -> formula,
     kk_iff: formula -> formula -> formula,
     kk_implies: formula -> formula -> formula,
     kk_and: formula -> formula -> formula,
     kk_subset: rel_expr -> rel_expr -> formula,
     kk_rel_eq: rel_expr -> rel_expr -> formula,
     kk_no: rel_expr -> formula,
     kk_lone: rel_expr -> formula,
     kk_one: rel_expr -> formula,
     kk_some: rel_expr -> formula,
     kk_rel_let: expr_assign list -> rel_expr -> rel_expr,
     kk_rel_if: formula -> rel_expr -> rel_expr -> rel_expr,
     kk_union: rel_expr -> rel_expr -> rel_expr,
     kk_difference: rel_expr -> rel_expr -> rel_expr,
     kk_override: rel_expr -> rel_expr -> rel_expr,
     kk_intersect: rel_expr -> rel_expr -> rel_expr,
     kk_product: rel_expr -> rel_expr -> rel_expr,
     kk_join: rel_expr -> rel_expr -> rel_expr,
     kk_closure: rel_expr -> rel_expr,
     kk_reflexive_closure: rel_expr -> rel_expr,
     kk_comprehension: decl list -> formula -> rel_expr,
     kk_project: rel_expr -> int_expr list -> rel_expr,
     kk_project_seq: rel_expr -> int -> int -> rel_expr,
     kk_not3: rel_expr -> rel_expr,
     kk_nat_less: rel_expr -> rel_expr -> rel_expr,
     kk_int_less: rel_expr -> rel_expr -> rel_expr}

  val kodkod_constrs : bool -> int -> int -> int -> kodkod_constrs
end
