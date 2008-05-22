signature helperLib =
sig

    include Abbrev

    type decompiler_tools =
      (string -> (Thm.thm * int * int option) * (Thm.thm * int * int option) option) *
      Thm.thm * Abbrev.term

    val RW                     : thm list -> thm -> thm
    val RW1                    : thm list -> thm -> thm

    val cache                  : (string -> 'a) -> string -> 'a
    val to_lower               : string -> string

    val all_distinct           : ''a list -> ''a list
    val replace_terml          : (term -> term) -> term -> term
    val collect_term_of_type   : hol_type -> term -> term list
    val find_terml             : (term -> bool) -> term -> term list
    val find_terml_all         : (term -> bool) -> term -> term list

    val car                    : term -> term
    val cdr                    : term -> term
    val list_dest              : ('a -> 'a * 'a) -> 'a -> 'a list
    val list_mk                : (term * term -> term) -> term list -> term -> term
    val is_normal_char         : char -> bool
    val mk_cond_star           : term * term -> term
    val mk_sidecond_star       : term * term -> term
    val mk_star                : term * term -> term
    val mk_sep_hide            : term -> term
    val dest_star              : term -> term * term
    val dest_sep_hide          : term -> term       
    val dest_spec              : term -> term * term * term * term 
    val get_sep_domain         : term -> term       
    val list_mk_star           : term list -> hol_type -> term

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
    val INST_SPEC              : thm -> thm -> thm

end
