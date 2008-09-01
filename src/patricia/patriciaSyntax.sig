signature patriciaSyntax =
sig

  include Abbrev

  val mk_ptree_type   : hol_type -> hol_type
  val dest_ptree_type : hol_type -> hol_type
  val is_ptree_type   : hol_type -> bool

  val empty_tm           : term
  val leaf_tm            : term
  val branch_tm          : term
  val peek_tm            : term
  val find_tm            : term
  val add_tm             : term
  val add_list_tm        : term
  val remove_tm          : term
  val traverse_tm        : term
  val keys_tm            : term
  val transform_tm       : term
  val every_leaf_tm      : term
  val exists_leaf_tm     : term
  val size_tm            : term
  val depth_tm           : term
  val is_ptree_tm        : term
  val in_ptree_tm        : term
  val insert_ptree_tm    : term
  val branching_bit_tm   : term
  val ptree_of_numset_tm : term
  val numset_of_ptree_tm : term

  val mk_empty           : hol_type -> term
  val mk_leaf            : term * term -> term
  val mk_branch          : term * term * term * term -> term
  val mk_peek            : term * term -> term
  val mk_find            : term * term -> term
  val mk_add             : term * term -> term
  val mk_add_list        : term * term -> term
  val mk_remove          : term * term -> term
  val mk_traverse        : term -> term
  val mk_keys            : term -> term
  val mk_transform       : term * term -> term
  val mk_every_leaf      : term * term -> term
  val mk_exists_leaf     : term * term -> term
  val mk_size            : term -> term
  val mk_depth           : term -> term
  val mk_is_ptree        : term -> term
  val mk_in_ptree        : term * term -> term
  val mk_insert_ptree    : term * term -> term
  val mk_branching_bit   : term * term -> term
  val mk_ptree_of_numset : term * term -> term
  val mk_numset_of_ptree : term -> term

  val dest_leaf            : term -> term * term
  val dest_branch          : term -> term * term * term * term
  val dest_peek            : term -> term * term
  val dest_find            : term -> term * term
  val dest_add             : term -> term * term
  val dest_add_list        : term -> term * term
  val dest_remove          : term -> term * term
  val dest_traverse        : term -> term
  val dest_keys            : term -> term
  val dest_transform       : term -> term * term
  val dest_every_leaf      : term -> term * term
  val dest_exists_leaf     : term -> term * term
  val dest_size            : term -> term
  val dest_depth           : term -> term
  val dest_is_ptree        : term -> term
  val dest_in_ptree        : term -> term * term
  val dest_insert_ptree    : term -> term * term
  val dest_branching_bit   : term -> term * term
  val dest_ptree_of_numset : term -> term * term
  val dest_numset_of_ptree : term -> term

  val is_empty           : term -> bool
  val is_leaf            : term -> bool
  val is_branch          : term -> bool
  val is_peek            : term -> bool
  val is_find            : term -> bool
  val is_add             : term -> bool
  val is_add_list        : term -> bool
  val is_remove          : term -> bool
  val is_traverse        : term -> bool
  val is_keys            : term -> bool
  val is_transform       : term -> bool
  val is_every_leaf      : term -> bool
  val is_exists_leaf     : term -> bool
  val is_size            : term -> bool
  val is_depth           : term -> bool
  val is_is_ptree        : term -> bool
  val is_in_ptree        : term -> bool
  val is_insert_ptree    : term -> bool
  val is_branching_bit   : term -> bool
  val is_ptree_of_numset : term -> bool
  val is_numset_of_ptree : term -> bool

end
