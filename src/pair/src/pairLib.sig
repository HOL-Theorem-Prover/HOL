signature pairLib =
sig
 include Abbrev

 val add_pair_compset : computeLib.compset -> unit

 (* from pairSyntax *)

 val mk_prod          : hol_type * hol_type -> hol_type
 val dest_prod        : hol_type -> hol_type * hol_type
 val list_mk_prod     : hol_type list -> hol_type
 val strip_prod       : hol_type -> hol_type list

 val comma_tm         : term
 val fst_tm           : term
 val snd_tm           : term
 val uncurry_tm       : term
 val curry_tm         : term
 val pair_map_tm      : term

 val mk_pair          : term * term -> term
 val mk_fst           : term -> term
 val mk_snd           : term -> term
 val mk_curry         : term * term * term -> term
 val mk_uncurry       : term * term -> term
 val mk_pair_map      : term * term -> term
 val mk_pabs          : term * term -> term
 val mk_pforall       : term * term -> term
 val mk_pexists       : term * term -> term
 val mk_pexists1      : term * term -> term
 val mk_pselect       : term * term -> term

 val dest_pair        : term -> term * term
 val dest_fst         : term -> term
 val dest_snd         : term -> term
 val dest_curry       : term -> term * term * term
 val dest_uncurry     : term -> term * term
 val dest_pair_map    : term -> term * term
 val dest_pabs        : term -> term * term
 val pbvar            : term -> term
 val pbody            : term -> term
 val dest_pforall     : term -> term * term
 val dest_pexists     : term -> term * term
 val dest_pexists1    : term -> term * term
 val dest_pselect     : term -> term * term
 val dest_pbinder     : term -> exn -> term -> term * term

 val list_mk_pair     : term list -> term
 val list_mk_pabs     : term list * term -> term
 val list_mk_pforall  : term list * term -> term
 val list_mk_pexists  : term list * term -> term
 val strip_pair       : term -> term list
 val spine_pair       : term -> term list
 val unstrip_pair     : hol_type -> term list -> term * term list
 val strip_pabs       : term -> term list * term
 val strip_pforall    : term -> term list * term
 val strip_pexists    : term -> term list * term

 val is_pair          : term -> bool
 val is_fst           : term -> bool
 val is_snd           : term -> bool
 val is_curry         : term -> bool
 val is_uncurry       : term -> bool
 val is_pair_map      : term -> bool
 val is_pabs          : term -> bool
 val is_pforall       : term -> bool
 val is_pexists       : term -> bool
 val is_pexists1      : term -> bool
 val is_pselect       : term -> bool
 val is_vstruct       : term -> bool

 val genvarstruct     : hol_type -> term

 (* From PairedLambda *)

 val PAIRED_BETA_CONV : conv
 val PAIRED_ETA_CONV  : conv
 val GEN_BETA_CONV    : conv
 val let_CONV         : conv
 val LET_SIMP_CONV    : bool -> conv
 val GEN_BETA_RULE    : thm -> thm
 val GEN_BETA_TAC     : tactic

 (* from Pair_basic *)

(*
 val MK_PAIR : thm * thm -> thm
 val PABS : term -> thm -> thm
 val PABS_CONV : conv -> conv
 val PSUB_CONV : conv -> conv
 val CURRY_CONV : conv
 val UNCURRY_CONV : conv
 val PBETA_CONV : conv
 val PBETA_RULE : thm -> thm
 val PBETA_TAC : tactic
 val RIGHT_PBETA : thm -> thm
 val LIST_PBETA_CONV : conv
 val RIGHT_LIST_PBETA : thm -> thm
 val LEFT_PBETA : thm -> thm
 val LEFT_LIST_PBETA : thm -> thm
 val UNPBETA_CONV : term -> conv
 val PETA_CONV : conv
 val PALPHA_CONV : term -> conv
 val GEN_PALPHA_CONV : term -> conv
 val PALPHA : term -> conv
 val paconv : term -> term -> bool
 val PAIR_CONV : conv -> conv
*)

 (* from pairTools *)

 val PairCases_on     : term quotation -> tactic
 val PGEN             : term -> term -> thm -> thm
 val PGEN_TAC         : term -> tactic
 val PFUN_EQ_RULE     : thm -> thm
 val LET_INTRO        : thm -> thm
 val LET_EQ_TAC       : thm list -> tactic
 val TUPLE            : term -> thm -> thm
 val TUPLE_TAC        : term -> tactic

 val LET_INTRO_TAC    : tactic
end
