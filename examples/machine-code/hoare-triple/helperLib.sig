signature helperLib =
sig

    include Abbrev

    type decompiler_tools =
      (* ( derive spec, generate branch, status thm, program counter term ) *)
      (string -> (Thm.thm * int * int option) * (Thm.thm * int * int option) option) *
      (term -> term -> int -> bool -> string * int) * Thm.thm * Abbrev.term

    datatype ftree_type =
      FUN_IF of term * ftree_type * ftree_type
    | FUN_LET of term * term * ftree_type
    | FUN_COND of term * ftree_type
    | FUN_VAL of term;

    val \\                     : tactic * tactic -> tactic
    val RW                     : thm list -> thm -> thm
    val RW1                    : thm list -> thm -> thm

    val echo                   : int -> string -> unit
    val set_echo               : int -> unit

    val cache                  : (string -> 'a) -> string -> 'a
    val to_lower               : string -> string

    val all_distinct           : ''a list -> ''a list
    val replace_terml          : (term -> term) -> term -> term
    val collect_term_of_type   : hol_type -> term -> term list
    val find_terml             : (term -> bool) -> term -> term list
    val find_terml_all         : (term -> bool) -> term -> term list
    val remove_primes          : thm -> thm

    val car                    : term -> term
    val cdr                    : term -> term
    val list_dest              : ('a -> 'a * 'a) -> 'a -> 'a list
    val list_mk                : (term * term -> term) -> term list -> term -> term
    val is_normal_char         : char -> bool
    val mk_cond_star           : term * term -> term
    val mk_sidecond_star       : term * term -> term
    val mk_star                : term * term -> term
    val mk_sep_hide            : term -> term
    val mk_sep_exists          : term * term -> term
    val dest_star              : term -> term * term
    val dest_sep_hide          : term -> term
    val dest_sep_exists        : term -> term * term
    val dest_spec              : term -> term * term * term * term
    val get_sep_domain         : term -> term
    val list_mk_star           : term list -> hol_type -> term
    val word_patterns          : term list

    val eval_term_ss           : string -> term -> simpLib.ssfrag
    val sep_cond_ss            : simpLib.ssfrag
    val star_ss                : simpLib.ssfrag
    val sw2sw_ss               : simpLib.ssfrag
    val w2w_ss                 : simpLib.ssfrag
    val pbeta_ss               : simpLib.ssfrag

    val MOVE_STAR_CONV         : term -> conv
    val MOVE_STAR_REWRITE_CONV : thm list -> term -> conv
    val MOVE_OUT_CONV          : term -> conv
    val STAR_REVERSE_CONV      : conv
    val FIX_WORD32_ARITH_CONV  : conv
    val POST_CONV              : conv -> conv
    val PRE_CONV               : conv -> conv
    val FORCE_PBETA_CONV       : conv
    val EVAL_ANY_MATCH_CONV    : term list -> conv

    val tm2ftree               : term -> ftree_type
    val ftree2tm               : ftree_type -> term

    val MATCH_INST             : thm -> term -> thm

    val SUBST_INST             : {redex: term, residue: term} list -> thm -> thm
    val UNHIDE_PRE_RULE        : term -> thm -> thm
    val HIDE_PRE_RULE          : term -> thm -> thm
    val HIDE_POST_RULE         : term -> thm -> thm
    val HIDE_STATUS_RULE       : bool -> thm -> thm -> thm
    val HIDE_PRE_STATUS_RULE   : thm -> thm -> thm
    val INST_SPEC              : thm -> thm -> thm
    val EXISTS_PRE             : term frag list -> thm -> thm
    val SEP_EXISTS_ELIM_RULE   : thm -> thm
    val SEP_EXISTS_POST_RULE   : term -> thm -> thm
    val SEP_EXISTS_PRE_RULE    : term -> thm -> thm
    val SEP_REWRITE_RULE       : thm list -> thm -> thm

    val SPEC_STRENGTHEN_RULE   : thm -> term -> thm * term
    val SPEC_WEAKEN_RULE       : thm -> term -> thm * term
    val SPEC_BOOL_FRAME_RULE   : thm -> term -> thm
    val SPEC_FRAME_RULE        : thm -> term -> thm
    val SPEC_COMPOSE_RULE      : thm list -> thm

    val SPEC_PROVE_TAC         : thm list -> tactic

    val ALIGNED_TAC            : tactic
    val SEP_READ_TAC           : tactic
    val SEP_WRITE_TAC          : tactic
    val SEP_NEQ_TAC            : tactic

    val CLEAN_TAC              : tactic
    val EXPAND_TAC             : tactic
    val SEP_F_TAC              : tactic
    val SEP_I_TAC              : string -> tactic
    val SEP_W_TAC              : tactic
    val SEP_R_TAC              : tactic
    val SEP_S_TAC              : string list -> thm -> tactic

    val auto_prove             : string -> term * tactic -> thm

end
