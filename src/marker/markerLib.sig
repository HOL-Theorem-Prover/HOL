signature markerLib =
sig
  include Abbrev
  type 'a set = 'a HOLset.set

  val stmark_term     : conv
  val stmark_conjunct : (term -> bool) -> conv
  val stmark_disjunct : (term -> bool) -> conv

  val move_stmarked_conj_left  : conv
  val move_stmarked_conj_right : conv
  val move_stmarked_disj_left  : conv
  val move_stmarked_disj_right : conv

  val move_conj_left  : (term -> bool) -> conv
  val move_conj_right : (term -> bool) -> conv
  val move_disj_left  : (term -> bool) -> conv
  val move_disj_right : (term -> bool) -> conv

  val AC     : thm -> thm -> thm
  val unAC   : thm -> thm * thm

  val Cong   : thm -> thm
  val unCong : thm -> thm

  val Excl   : string -> thm
  val destExcl : thm -> string option
  val ExclSF : string -> thm
  val destExclSF : thm -> string option

  val FRAG   : string -> thm
  val destFRAG : thm -> string option

  val mk_Req0 : thm -> thm
  val mk_ReqD : thm -> thm
  val dest_Req0 : thm -> thm option
  val dest_ReqD : thm -> thm option
  val mk_require_tac : (thm list -> tactic) -> (thm list -> tactic)

  val ABB                 : term -> term -> tactic
  val ABB'                : {redex : term, residue : term} -> tactic
  val ABBREV_TAC          : term -> tactic
  val PAT_ABBREV_TAC      : term set -> term -> tactic
  val MATCH_ABBREV_TAC    : term set -> term -> tactic
  val MATCH_ASSUM_ABBREV_TAC : term set -> term -> tactic
  val HO_MATCH_ABBREV_TAC : term set -> term -> tactic
  val UNABBREV_TAC        : string -> tactic
  val UNABBREV_ALL_TAC    : tactic
  val CNTXT_REABBREV_TAC  : term list -> tactic
  val REABBREV_TAC        : tactic
  val WITHOUT_ABBREVS     : tactic -> tactic
  val RM_ABBREV_TAC       : string -> tactic
  val RM_ALL_ABBREVS_TAC  : tactic
  val ABBRS_THEN          : (thm list -> tactic) -> thm list -> tactic
  val TIDY_ABBREV_CONV    : conv
  val TIDY_ABBREV_RULE    : thm -> thm
  val TIDY_ABBREVS        : tactic
  val MK_ABBREVS_OLDSTYLE : tactic
  val Abbr                : term quotation -> thm
  val safe_inst_cmp       : {redex:term,residue:term} Lib.cmp
  val safe_inst_sort      : (term,term) subst -> (term,term) subst

  val L                : string -> thm
  val MK_LABEL         : string * thm -> thm
  val DEST_LABEL       : thm -> thm
  val DEST_LABELS      : thm -> thm
  val DEST_LABEL_CONV  : conv
  val DEST_LABELS_CONV : conv
  val DEST_LABELS_TAC  : tactic

  val find_labelled_assumption : thm -> term list -> thm

  val ASSUME_NAMED_TAC : string -> thm -> tactic
  val LABEL_ASSUM      : string -> thm_tactic -> tactic
  val LABEL_X_ASSUM    : string -> thm_tactic -> tactic
  val LLABEL_RESOLVE   : thm list -> term list -> thm list
  val LLABEL_RES_THEN  : (thm list -> tactic) -> thm list -> tactic

  val using            : tactic * thm -> tactic
  val usingA           : tactic -> thm_tactic  (* curry of above *)
  val maybe_using      : (unit -> thm list) -> thm_tactic -> tactic

  val mk_hide : string -> term -> term
  val is_hide : term -> bool
  val dest_hide : term -> string * term
  val install_hidepp : unit -> unit (* it starts installed *)
  val remove_hidepp : unit -> unit
  val unignoring_hide : ('a -> 'b) -> ('a -> 'b)

  val MK_HIDE : string -> thm -> thm
  val UNHIDE : thm -> thm
  val hide_tac : string -> thm -> tactic
  val unhide_tac : string -> tactic
  val hide_assum : string -> thm_tactic -> tactic
  val unhide_assum : string -> thm_tactic -> tactic
  val unhide_x_assum : string -> thm_tactic -> tactic
  val use_hidden_assum : string -> thm_tactic -> tactic

  val IgnAsm : 'a quotation -> thm
  val NoAsms : thm

  val process_taclist_then : {arg: thm list} -> (thm list -> tactic) -> tactic

end

(*
   [stmark_term t] wraps term t in a "short term marker".

   [stmark_conjunct P t] finds the first conjunct c amongst the
   conjuncts of term t (conjuncts as returned by strip_conj), for which
   P c returns true and marks it as per stmark_term.  The traversal is
   from left to right.

   [stmark_disjunct P t] finds the first disjunct d amongst the
   disjuncts of term t (disjuncts as returned by strip_disj), for which
   P d returns true and marks it as per stmark_term.  The traversal is
   from left to right.

   [move_stmarked_conj_left t] moves the st-marked conjunct in t to
   the left, so that if t is of the form ... /\ stmark c /\ ..., then
   the returned theorem is of the form
      |- t = c /\ ...
   where c has lost its marker.   The behaviour is undefined if there
   is not exactly one marked conjunct.

   [move_stmarked_conj_right t] moves the st-marked conjunct to the
   right.  Analogous to move_stmarked_conj_left.

   [move_stmarked_disj_left t] moves the st-marked disjunct to the
   left.  Analogous to move_stmarked_conj_left.

   [move_stmarked_disj_right t] moves the st-marked disjunct to the
   right.  Analogous to move_stmarked_conj_left.

   [move_conj_left P t] first looks for a conjunct satisfying P, marks it,
   and then moves it to the left.  Is a composition of stmark_conjunct and
   move_stmarked_conj_left.

   [move_conj_right P t] moves a conjunct satisfying P to the right.
   Analogous to move_conj_left.

   [move_disj_left P t] moves a disjunct satisfying P to the left.
   Analogous to move_conj_left.

   [move_disj_right P t] moves a disjunct satisfying P to the right.
   Analogous to move_conj_left.

*)
