signature patricia_castsSyntax =
sig

  include Abbrev

  val mk_word_ptree_type    : hol_type * hol_type -> hol_type
  val dest_word_ptree_type  : hol_type -> hol_type * hol_type
  val is_word_ptree_type    : hol_type -> bool

  val the_ptree_tm          : term
  val some_ptree_tm         : term
  val wordempty_tm          : term
  val peekw_tm              : term
  val findw_tm              : term
  val addw_tm               : term
  val add_listw_tm          : term
  val removew_tm            : term
  val traversew_tm          : term
  val keysw_tm              : term
  val transformw_tm         : term
  val every_leafw_tm        : term
  val exists_leafw_tm       : term
  val sizew_tm              : term
  val depthw_tm             : term
  val in_ptreew_tm          : term
  val insert_ptreew_tm      : term
  val ptree_of_wordset_tm   : term
  val wordset_of_ptree_tm   : term

  val peeks_tm              : term
  val finds_tm              : term
  val adds_tm               : term
  val add_lists_tm          : term
  val removes_tm            : term
  val traverses_tm          : term
  val keyss_tm              : term
  val in_ptrees_tm          : term
  val insert_ptrees_tm      : term
  val ptree_of_stringset_tm : term
  val stringset_of_ptree_tm : term

  val mk_wordempty          : hol_type * hol_type -> term
  val mk_the_ptree          : term -> term
  val mk_some_ptree         : hol_type * term -> term
  val mk_peekw              : term * term -> term
  val mk_findw              : term * term -> term
  val mk_addw               : term * term -> term
  val mk_add_listw          : term * term -> term
  val mk_removew            : term * term -> term
  val mk_traversew          : term -> term
  val mk_keysw              : term -> term
  val mk_transformw         : term * term -> term
  val mk_every_leafw        : term * term -> term
  val mk_exists_leafw       : term * term -> term
  val mk_sizew              : term -> term
  val mk_depthw             : term -> term
  val mk_in_ptreew          : term * term -> term
  val mk_insert_ptreew      : term * term -> term
  val mk_ptree_of_wordset   : term -> term
  val mk_wordset_of_ptree   : term -> term

  val mk_peeks              : term * term -> term
  val mk_finds              : term * term -> term
  val mk_adds               : term * term -> term
  val mk_add_lists          : term * term -> term
  val mk_removes            : term * term -> term
  val mk_traverses          : term -> term
  val mk_keyss              : term -> term
  val mk_in_ptrees          : term * term -> term
  val mk_insert_ptrees      : term * term -> term
  val mk_ptree_of_stringset : term -> term
  val mk_stringset_of_ptree : term -> term

  val dest_the_ptree        : term -> term
  val dest_some_ptree       : term -> term
  val dest_wordempty        : term -> term
  val dest_peekw            : term -> term * term
  val dest_findw            : term -> term * term
  val dest_addw             : term -> term * term
  val dest_add_listw        : term -> term * term
  val dest_removew          : term -> term * term
  val dest_traversew        : term -> term
  val dest_keysw            : term -> term
  val dest_transformw       : term -> term * term
  val dest_every_leafw      : term -> term * term
  val dest_exists_leafw     : term -> term * term
  val dest_sizew            : term -> term
  val dest_depthw           : term -> term
  val dest_in_ptreew        : term -> term * term
  val dest_insert_ptreew    : term -> term * term
  val dest_ptree_of_wordset : term -> term
  val dest_wordset_of_ptree : term -> term

  val dest_peeks              : term -> term * term
  val dest_finds              : term -> term * term
  val dest_adds               : term -> term * term
  val dest_add_lists          : term -> term * term
  val dest_removes            : term -> term * term
  val dest_traverses          : term -> term
  val dest_keyss              : term -> term
  val dest_in_ptrees          : term -> term * term
  val dest_insert_ptrees      : term -> term * term
  val dest_ptree_of_stringset : term -> term
  val dest_stringset_of_ptree : term -> term

  val is_the_ptree          : term -> bool
  val is_some_ptree         : term -> bool
  val is_wordempty          : term -> bool
  val is_peekw              : term -> bool
  val is_findw              : term -> bool
  val is_addw               : term -> bool
  val is_add_listw          : term -> bool
  val is_removew            : term -> bool
  val is_traversew          : term -> bool
  val is_keysw              : term -> bool
  val is_transformw         : term -> bool
  val is_every_leafw        : term -> bool
  val is_exists_leafw       : term -> bool
  val is_sizew              : term -> bool
  val is_depthw             : term -> bool
  val is_in_ptreew          : term -> bool
  val is_insert_ptreew      : term -> bool
  val is_ptree_of_wordset   : term -> bool
  val is_wordset_of_ptree   : term -> bool

  val is_peeks              : term -> bool
  val is_finds              : term -> bool
  val is_adds               : term -> bool
  val is_add_lists          : term -> bool
  val is_removes            : term -> bool
  val is_traverses          : term -> bool
  val is_keyss              : term -> bool
  val is_in_ptrees          : term -> bool
  val is_insert_ptrees      : term -> bool
  val is_ptree_of_stringset : term -> bool
  val is_stringset_of_ptree : term -> bool

end
