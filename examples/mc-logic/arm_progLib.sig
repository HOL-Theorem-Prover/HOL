signature arm_progLib =
sig
    include Abbrev

    (* stable core functions *)

    val dest_ARM_PROG       : term -> term * term * term * term * term   

    val FST_PROG2           : thm -> thm
    val SND_PROG2           : thm -> thm

    val ARM_PROG_PRE_CONV   : conv -> conv   
    val ARM_PROG_POST1_CONV : conv -> conv
    val ARM_PROG_POST_CONV  : conv -> conv

    val PRE_CONV_RULE       : conv -> thm -> thm   
    val POST1_CONV_RULE     : conv -> thm -> thm
    val POST_CONV_RULE      : conv -> thm -> thm

    val PRE_MOVE_STAR       : term frag list -> term frag list -> thm -> thm   
    val POST1_MOVE_STAR     : term frag list -> term frag list -> thm -> thm
    val POST_MOVE_STAR      : term frag list -> term frag list -> thm -> thm

    val pcINC_ss            : simpLib.ssfrag
    val setINC_ss           : simpLib.ssfrag
    val compose_ss          : simpLib.ssfrag
    val armINST_ss          : simpLib.ssfrag

    val MATCH_COMPOSE       : thm -> thm -> thm
    val ARRANGE_COMPOSE     : thm -> thm -> thm
    val FRAME_COMPOSE       : thm -> thm -> thm
    val MOVE_COMPOSE        : thm -> thm -> 
                              term frag list -> term frag list -> 
                              term frag list -> term frag list -> thm

    val HIDE_PRE            : thm -> thm
    val HIDE_POST1          : thm -> thm
    val HIDE_POST           : thm -> thm
    val HIDE_STATUS         : thm -> thm
    val EXISTS_PRE          : term frag list -> thm -> thm

    val MOVE_PRE            : term frag list -> thm -> thm
    val MOVE_POST1          : term frag list -> thm -> thm
    val MOVE_POST           : term frag list -> thm -> thm

    val AUTO_HIDE_PRE       : (term frag list) list -> thm -> thm
    val AUTO_HIDE_POST1     : (term frag list) list -> thm -> thm
    val AUTO_HIDE_POST      : (term frag list) list -> thm -> thm

    val AUTO_PRE_HIDE_STATUS   : thm -> thm
    val AUTO_POST1_HIDE_STATUS : thm -> thm
    val AUTO_POST_HIDE_STATUS  : thm -> thm
    val AUTO_HIDE_STATUS       : thm -> thm

    val APP_BASIC_FRAME     : thm -> thm
    val APP_FRAME           : term frag list -> thm -> thm
    val APP_APPEND          : thm -> term -> thm
    val APP_MERGE           : thm -> thm -> thm

    val APP_STRENGTHEN_TERM      : thm -> term frag list -> term 
    val APP_STRENGTHEN           : thm -> term frag list -> tactic -> thm 
    val APP_PART_STRENGTHEN_TERM : thm -> term frag list -> term 
    val APP_PART_STRENGTHEN      : thm -> term frag list -> tactic -> thm 
    val APP_WEAKEN1_TERM         : thm -> term frag list -> term 
    val APP_WEAKEN1              : thm -> term frag list -> tactic -> thm 
    val APP_PART_WEAKEN1_TERM    : thm -> term frag list -> term 
    val APP_PART_WEAKEN1         : thm -> term frag list -> tactic -> thm 
    val APP_WEAKEN_TERM          : thm -> term frag list -> term 
    val APP_WEAKEN               : thm -> term frag list -> tactic -> thm 
    val APP_PART_WEAKEN_TERM     : thm -> term frag list -> term 
    val APP_PART_WEAKEN          : thm -> term frag list -> tactic -> thm 

    val SPEC_STRENGTHEN     : thm -> term frag list -> thm
    val SPEC_WEAKEN1        : thm -> term frag list -> thm
    val SPEC_WEAKEN         : thm -> term frag list -> thm
    val SEP_IMP_RULE        : (term -> thm) -> thm -> thm

    val ALIGN_VARS          : string list -> thm -> thm
 
    val MATCH_INST1         : term frag list list -> thm -> thm -> thm
    val MATCH_INST          : term frag list list -> thm -> thm -> thm
     
    val CLOSE_LOOP          : thm -> thm
    val EXTRACT_CODE        : thm -> thm
    val ABSORB_POST         : thm -> thm

    val PAT_DISCH           : term -> thm -> thm
    val PAIR_GEN            : string -> term frag list -> thm -> thm
    val QGENL               : term frag list list -> thm -> thm
    val INST_LDM_STM        : bool -> term frag list -> term frag list -> 
                              thm -> term frag list -> thm

    val show_enc            : bool ref
    val show_code           : bool ref
 
    val pp_enc              : unit -> unit

    (* experimental proof-producing functions *)
 
    val print_compositions  : (thm * string) list -> string -> string -> unit   

    val make_spec           : string list -> unit
    val make_spec'          : (string * bool) list -> unit

    val compose_progs       : string list -> string -> string -> unit
    val compose_progs'      : (string * bool) list -> string -> string -> unit
    val compose_progs''     : (string * bool) list -> string -> string -> int -> unit

end
