signature bossLib =
sig
  include Abbrev
  type ssfrag = simpLib.ssfrag
  type simpset = simpLib.simpset

  (* Make definitions *)

  (* new types *)
  val Hol_datatype : hol_type quotation -> unit
  val Datatype : hol_type quotation -> unit

  (* new functions *)
  val Define       : term quotation -> thm
  val zDefine      : term quotation -> thm
  val xDefine      : string -> term quotation -> thm
  val tDefine      : string -> term quotation -> tactic -> thm
  val WF_REL_TAC   : term quotation -> tactic
  val Hol_defn     : string -> term quotation -> DefnBase.defn

  (* new (inductive) relations *)
  val Hol_reln     : term quotation -> thm * thm * thm
  val Hol_coreln   : term quotation -> thm * thm * thm
  val xHol_reln    : string -> term quotation -> thm * thm * thm
  val xHol_coreln  : string -> term quotation -> thm * thm * thm
  val export_mono  : string -> unit

  (* Derived rule for specifying new constants.
     Should have the same effect as Theory.Definition.new_specification. *)
  val new_specification : string * string list * thm -> thm

  (* Case-splitting and induction operations *)

  val Cases             : tactic
  val Cases_on          : term quotation -> tactic
  val tmCases_on        : term -> string list -> tactic
  val PairCases         : tactic
  val PairCases_on      : term quotation -> tactic
  val Induct            : tactic
  val Induct_on         : term quotation -> tactic
  val update_induction  : thm -> unit
  val recInduct         : thm -> tactic
  val namedCases        : string list -> tactic
  val namedCases_on     : term quotation -> string list -> tactic

  val measureInduct_on  : term quotation -> tactic
  val completeInduct_on : term quotation -> tactic
  val using             : tactic * thm -> tactic (* infix *)
  val usingA            : tactic -> thm -> tactic (* curry of above *)

  val pairarg_tac       : tactic
  val split_pair_case_tac : tactic

  val CASE_TAC          : tactic
  val CaseEq            : string -> thm
  val CaseEqs           : string list -> thm
  val AllCaseEqs        : unit -> thm
  val CasePred          : string -> thm
  val CasePreds         : string list -> thm
  val AllCasePreds      : unit -> thm

  (* Proof automation *)

  val PROVE          : thm list -> term -> thm   (* First order *)
  val METIS_PROVE    : thm list -> term -> thm   (* First order *)
  val DECIDE         : term -> thm               (* Cooperating dec. procs *)
  val PROVE_TAC      : thm list -> tactic
  val prove_tac      : thm list -> tactic
  val METIS_TAC      : thm list -> tactic
  val metis_tac      : thm list -> tactic
  val DECIDE_TAC     : tactic
  val decide_tac     : tactic

  (* Simplification *)

  val ++              : simpset * ssfrag -> simpset    (* infix *)
  val &&              : simpset * thm list -> simpset  (* infix *)
  val -*              : simpset * string list -> simpset (* infix *)
  val pure_ss         : simpset
  val bool_ss         : simpset
  val std_ss          : simpset           (* bool + option + pair + sum *)
  val arith_ss        : simpset
  val old_arith_ss    : simpset
  val list_ss         : simpset
  val srw_ss          : unit -> simpset
  val boss_ss         : unit -> simpset (* srw_ss() + LET_ss + ARITH_ss *)

  val ARITH_ss        : ssfrag            (* arithmetic d.p. + some rewrites *)
  val old_ARITH_ss    : ssfrag
  val CONJ_ss         : ssfrag
  val DISJ_ss         : ssfrag
  val DNF_ss          : ssfrag
  val ETA_ss          : ssfrag
  val QI_ss           : ssfrag
  val SFY_ss          : ssfrag
  val SQI_ss          : ssfrag
  val type_rws        : hol_type -> thm list
  val rewrites        : thm list -> ssfrag
  val augment_srw_ss  : ssfrag list -> unit
  val diminish_srw_ss : string list -> unit
  val export_rewrites : string list -> unit
  val temp_delsimps   : string list -> unit
  val delsimps        : string list -> unit
  val limit           : int -> simpset -> simpset

  (* use these in simplifier's argument list *)
  val SimpLHS        : thm
  val SimpRHS        : thm
  val SimpL          : term -> thm
  val SimpR          : term -> thm

  val Cong           : thm -> thm
  val AC             : thm -> thm -> thm
  val Excl           : string -> thm
  val ExclSF         : string -> thm
  val SF             : ssfrag -> thm
  val Req0           : thm -> thm
  val ReqD           : thm -> thm
  val NoAsms         : thm
  val IgnAsm         : 'a quotation -> thm

  (* useful rules to use with simplification *)
  val oneline        : thm -> thm
  val lambdify       : thm -> thm

  val SIMP_CONV         : simpset -> thm list -> conv
  val SIMP_RULE         : simpset -> thm list -> thm -> thm
  val SRULE             : thm list -> thm -> thm (* uses srw_ss() *)
  val SCONV             : thm list -> conv (* uses srw_ss() *)
  val SIMP_TAC          : simpset -> thm list -> tactic
  val simp_tac          : simpset -> thm list -> tactic
  val ASM_SIMP_TAC      : simpset -> thm list -> tactic
  val asm_simp_tac      : simpset -> thm list -> tactic
  val FULL_SIMP_TAC     : simpset -> thm list -> tactic
  val full_simp_tac     : simpset -> thm list -> tactic
  val REV_FULL_SIMP_TAC : simpset -> thm list -> tactic
  val rev_full_simp_tac : simpset -> thm list -> tactic
  val RW_TAC            : simpset -> thm list -> tactic
  val rw_tac            : simpset -> thm list -> tactic
  val SRW_TAC           : ssfrag list -> thm list -> tactic
  val srw_tac           : ssfrag list -> thm list -> tactic

  val NO_STRIP_FULL_SIMP_TAC     : simpset -> thm list -> tactic
  val NO_STRIP_REV_FULL_SIMP_TAC : simpset -> thm list -> tactic

  val QI_TAC     : tactic
  val ASM_QI_TAC : tactic
  val GEN_EXISTS_TAC : string -> Parse.term Lib.frag list -> tactic

  (* Call-by-value evaluation *)
  val EVAL           : conv
  val EVALn          : int -> conv
  val EVAL_RULE      : thm -> thm
  val EVAL_TAC       : tactic

  (* Automate some routine set theory by reduction to FOL *)
  val SET_TAC        : thm list -> tactic
  val ASM_SET_TAC    : thm list -> tactic
  val SET_RULE       : term -> thm

  (* Miscellaneous *)

  val ZAP_TAC        : simpset -> thm list -> tactic
  val SPOSE_NOT_THEN : (thm -> tactic) -> tactic
  val spose_not_then : (thm -> tactic) -> tactic
  val by             : term quotation * tactic -> tactic   (* infix *)
  val suffices_by    : term quotation * tactic -> tactic   (* infix *)
  val sg             : term quotation -> tactic
  val subgoal        : term quotation -> tactic
  val >~             : ('a,'b)gentactic * term quotation list ->
                       ('a,'b)gentactic
  val >>~            : ('a,'b)gentactic * term quotation list ->
                       ('a,'b)gentactic
  val >>~-           : ('a,'b)gentactic * (term quotation list * tactic) ->
                       ('a,'b)gentactic
  val cheat          : tactic
  val kall_tac       : 'a -> tactic

  (* Abbreviations  (see also Q structure) *)

  val Abbr             : term quotation -> thm
  val UNABBREV_ALL_TAC : tactic
  val REABBREV_TAC     : tactic
  val WITHOUT_ABBREVS  : tactic -> tactic

  (* name cases of an induction theorem *)
  val name_ind_cases : term list -> thm -> thm

  (* convert aux size operators to combinators and use append rules *)
  val size_comb_tac : tactic

  (* more simplification variants *)
  val fsrw_tac : simpLib.ssfrag list -> thm list -> tactic
  val simp : thm list -> tactic
  val csimp : thm list -> tactic
  val dsimp : thm list -> tactic
  val lrw : thm list -> tactic
  val lfs : thm list -> tactic
  val lrfs : thm list -> tactic
  val rw : thm list -> tactic
  val fs : thm list -> tactic
  val rfs : thm list -> tactic
  val gs : thm list -> tactic
  val gvs : thm list -> tactic
  val gns : thm list -> tactic
  val gnvs : thm list -> tactic
  val rgs : thm list -> tactic

  (* without loss of generality (from wlogLib) *)
  val wlog_then : term quotation ->
                  term quotation list -> thm_tactic -> tactic
  val wlog_tac : term quotation -> term quotation list -> tactic

  (* useful quotation-based tactics (from Q) *)
  val qx_gen_tac : term quotation -> tactic
  val qx_genl_tac : term quotation list -> tactic
  val qx_choose_then : term quotation -> thm_tactic -> thm_tactic
  val qx_choosel_then : term quotation list -> thm_tactic -> thm_tactic
  val qexists_tac : term quotation -> tactic
  val qexistsl_tac : term quotation list -> tactic
  val qexists : term quotation -> tactic
  val qexistsl : term quotation list -> tactic
  val qrefine : term quotation -> tactic
  val qrefinel : term quotation list -> tactic
  val qsuff_tac : term quotation -> tactic
  val qid_spec_tac : term quotation -> tactic
  val qspec_tac : term quotation * term quotation -> tactic
  val qspec_then : term quotation -> thm_tactic -> thm -> tactic
  val qspecl_then : term quotation list -> thm_tactic -> thm -> tactic
  val qhdtm_assum : term quotation -> thm_tactic -> tactic
  val qhdtm_x_assum : term quotation -> thm_tactic -> tactic
  val qpat_assum : term quotation -> thm_tactic -> tactic
  val qpat_x_assum : term quotation -> thm_tactic -> tactic
  val qpat_abbrev_tac : term quotation -> tactic
  val qmatch_abbrev_tac : term quotation -> tactic
  val qho_match_abbrev_tac : term quotation -> tactic
  val qmatch_rename_tac : term quotation -> tactic
  val qmatch_assum_abbrev_tac : term quotation -> tactic
  val qmatch_assum_rename_tac : term quotation -> tactic
  val qmatch_asmsub_rename_tac : term quotation -> tactic
  val qmatch_goalsub_rename_tac : term quotation -> tactic
  val qmatch_asmsub_abbrev_tac : term quotation -> tactic
  val qmatch_goalsub_abbrev_tac : term quotation -> tactic
  val rename1 : term quotation -> tactic
  val rename : term quotation list -> tactic
  val qabbrev_tac : term quotation -> tactic
  val qunabbrev_tac : term quotation -> tactic
  val qunabbrevl_tac : term quotation list -> tactic
  val unabbrev_all_tac : tactic
end
