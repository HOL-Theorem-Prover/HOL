signature set_sepLib =
sig
    include Abbrev

    val mk_STAR             : term * term -> term
    val dest_STAR           : term -> term * term
    val list_mk_STAR        : term list -> term
    val list_dest_STAR      : term -> term list    

    val sep_ss              : simpLib.ssfrag 
    val sep2_ss             : simpLib.ssfrag 

    val star_ss             : simpLib.ssfrag 
    val SEP_cond_ss         : simpLib.ssfrag
    val SEP_EXISTS_ss       : simpLib.ssfrag

    val ONCE_REWRITE_ASSUMS : thm list -> tactic

    val MOVE_STAR_TAC       : term frag list -> term frag list -> tactic
    val ASM_MOVE_STAR_TAC   : term frag list -> term frag list -> tactic
    val FULL_MOVE_STAR_TAC  : term frag list -> term frag list -> tactic
    val MOVE_STAR_CONV      : term frag list -> term frag list -> conv
    val MOVE_STAR_RULE      : term frag list -> term frag list -> rule

end
