signature utilsLib =
sig
   include Abbrev

   type inventory = {C: string list, N: int list, T: string list, Thy: string}
   type cover = {redex: term frag list, residue: term} list list

   val ALL_HYP_CONV_RULE: conv -> rule
   val ALL_HYP_RULE: rule -> rule
   val BIT_FIELD_INSERT_CONV : string -> string -> conv
   val CHANGE_CBV_CONV: computeLib.compset -> conv
   val ELIM_UNDISCH: rule
   val EXTRACT_CONV: conv
   val FULL_CONV_RULE: conv -> thm -> thm
   val HYP_CANON_RULE: rule
   val HYP_CONV_RULE: conv -> term -> rule
   val HYP_RULE: (thm -> thm) -> term -> rule
   val INST_REWRITE_CONV: thm list -> conv
   val INST_REWRITE_CONV1: thm -> conv
   val INST_REWRITE_RULE: thm list -> rule
   val LIST_DISCH: term list -> rule
   val MATCH_HYP_CONV_RULE: conv -> term -> rule
   val MATCH_HYP_RULE: rule -> term -> rule
   val MERGE_CASES: term -> thm -> thm -> thm
   val NCONV: int -> conv -> conv
   val PRED_HYP_CONV_RULE: conv -> (term -> bool) -> rule
   val PRED_HYP_RULE: rule -> (term -> bool) -> rule
   val REC_REG_BIT_FIELD_INSERT_TAC:
      string -> string -> term quotation -> tactic
   val Run_CONV: string * term -> conv
   val SET_CONV: conv
   val SET_RULE: rule
   val SRW_CONV: thm list -> conv
   val SRW_RULE: thm list -> rule
   val STEP:
      (thm list -> thm list) * term -> thm list -> term list list -> cover ->
      term -> thm list
   val WALPHA_CONV: conv
   val WGROUND_CONV: conv
   val accessor_fns: hol_type -> term list
   val add_base_datatypes: computeLib.compset -> unit
   val add_datatypes: hol_type list -> computeLib.compset -> unit
   val add_theory: (thm list * inventory) -> computeLib.compset -> unit
   val add_to_rw_net:
      (thm -> term) -> thm * thm LVTermNet.lvtermnet -> thm LVTermNet.lvtermnet
   val add_to_the_compset: (thm list * inventory) -> unit
   val augment: term frag list * term list -> cover -> cover
   val avoid_name_clashes: term -> term -> term
   val cache: int -> ('a * 'a -> order) -> ('a -> 'b) -> 'a -> 'b
   val classes: ('a * 'a -> bool) -> 'a list -> 'a list list
   val datatype_rewrites: bool -> string -> string list -> thm list
   val dom: hol_type -> hol_type
   val eval: term -> term
   val filter_inventory: string list -> inventory -> inventory
   val find_rw: thm LVTermNet.lvtermnet -> term -> thm list
   val for_thm: int * int -> thm
   val get_function: thm -> term
   val lhsc: thm -> term
   val list_mk_wordii: int -> int list -> term list
   val long_term_to_string: term -> string
   val lowercase: string -> string
   val map_conv: conv -> term list -> thm
   val match_subst: {redex: term, residue: term} list -> term -> term
   val maximal: ('a * 'a -> order) -> ('b -> 'a) -> 'b list -> 'b * 'b list
   val minimal: ('a * 'a -> order) -> ('b -> 'a) -> 'b list -> 'b * 'b list
   val mk_cond_rand_thms: term list -> thm
   val mk_cond_update_thms: hol_type list -> thm list
   val mk_negation: term -> term
   val mk_reg_thm: string -> string -> thm
   val mk_run: string * term -> term -> term
   val mk_rw_net: (thm -> term) -> thm list -> thm LVTermNet.lvtermnet
   val mk_state_id_thm: thm -> string list list -> thm
   val o_RULE: rule
   val padLeft: 'a -> int -> 'a list -> 'a list
   val partitions: 'a list -> 'a list list list
   val pattern: string -> term
   val pick: bool list -> 'a list -> 'a list
   val process_opt:
      ''a list list -> string -> 'b -> ''a list -> (int -> 'b) -> 'b * ''a list
   val process_option:
      ('a -> bool) -> ('a -> ''b) -> string -> 'c -> 'a list -> (''b -> 'c) ->
      'c * 'a list
   val qm: thm list -> term -> thm
   val qm_tac: thm list -> tactic
   val removeSpaces: string -> string
   val resetStepConv: unit -> unit
   val rev_endian: 'a list -> 'a list
   val rhsc: thm -> term
   val rng: hol_type -> hol_type
   val save_as: string -> thm -> thm
   val setStepConv: conv -> unit
   val specialized: string -> conv * term list -> thm list -> thm list
   val splitAtChar: (char -> bool) -> string -> string * string
   val splitAtPos: int -> string -> string * string
   val split_conditions: thm -> thm list
   val strip_add_or_sub: term -> term * (bool * term) list
   val tab_fixedwidth: int -> int -> term list
   val theory_compset: (thm list * inventory) -> computeLib.compset
   val theory_rewrites: (thm list * inventory) -> thm list
   val theory_types: inventory -> hol_type list
   val update_fns: hol_type -> term list
   val uppercase: string -> string
   val usave_as: string -> thm -> thm
   val ustore_thm: string * Q.tmquote * tactic -> thm
   val vacuous: thm -> bool
   val zipLists: ('a list -> 'b) -> 'a list list -> 'b list
end
