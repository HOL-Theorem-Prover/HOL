Theory marker[bare]
Libs
  HolKernel Parse boolLib

(* ----------------------------------------------------------------------
    stmarker

    stmarker stands for "short term marker"; use this constant to mark
    sub-terms for a short period (within a conversion, say) and be sure
    to remove the marker soon after use.
   ---------------------------------------------------------------------- *)

Definition stmarker_def[nocompute]: stmarker (x:'a) = x
End
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy="marker",Name="stmarker"},name=(["Unwanted"],"id")}

(* the following move_<dir>_<op> theorems will loop if more than one term
   is marked at the same level *)
val move_left_conj = store_thm(
  "move_left_conj",
  ``!p q m. (p /\ stmarker m <=> stmarker m /\ p) /\
            ((stmarker m /\ p) /\ q <=> stmarker m /\ (p /\ q)) /\
            (p /\ (stmarker m /\ q) <=> stmarker m /\ (p /\ q))``,
  REWRITE_TAC [stmarker_def, CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  MATCH_ACCEPT_TAC CONJ_COMM);

val move_right_conj = store_thm(
  "move_right_conj",
  ``!p q m. (stmarker m /\ p <=> p /\ stmarker m) /\
            (p /\ (q /\ stmarker m) <=> (p /\ q) /\ stmarker m) /\
            ((p /\ stmarker m) /\ q <=> (p /\ q) /\ stmarker m)``,
  REWRITE_TAC [stmarker_def, GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  MATCH_ACCEPT_TAC CONJ_COMM);

val move_left_disj = store_thm(
  "move_left_disj",
  ``!p q m. (p \/ stmarker m <=> stmarker m \/ p) /\
            ((stmarker m \/ p) \/ q <=> stmarker m \/ (p \/ q)) /\
            (p \/ (stmarker m \/ q) <=> stmarker m \/ (p \/ q))``,
  REWRITE_TAC [stmarker_def, DISJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  MATCH_ACCEPT_TAC DISJ_COMM);

val move_right_disj = store_thm(
  "move_right_disj",
  ``!p q m. (stmarker m \/ p <=> p \/ stmarker m) /\
            (p \/ (q \/ stmarker m) <=> (p \/ q) \/ stmarker m) /\
            ((p \/ stmarker m) \/ q <=> (p \/ q) \/ stmarker m)``,
  REWRITE_TAC [stmarker_def, GSYM DISJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  MATCH_ACCEPT_TAC DISJ_COMM);

(* Note, if you want to move a pair of things to the edge of a term,
   you can move one of them, and then the second in two successive
   passes.  Something like
     find_and_move_left THENC RAND_CONV find_and_move_left
   will result in a term
     t1 /\ (t2 /\ ...)
   rewriting with CONJ_ASSOC will even give you
     (t1 /\ t2) /\ ...
*)

(* ----------------------------------------------------------------------
    unint

    unint stands for "uninterpreted", and can be used to mark and/or
    breakup terms that represent "bad" situations.  One can be sure
    that unint terms will never be written away, so that they will
    persist and act as a signal to the user that something has gone wrong.

    Just make sure that unint never appears on the LHS of a rewrite rule.
    (Idea and name taken from Joe Hurd's development of the positive reals
    with an infinity.)
   ---------------------------------------------------------------------- *)

Definition unint_def[nocompute]:
  unint (x:'a) = x
End
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy="marker",Name="unint"},name=(["Unwanted"],"id")}

(* ----------------------------------------------------------------------
    Abbrev

    For wrapping up abbreviations in the assumption list.  This tag
    protects equalities so that they can appear in assumptions and not
    be eliminated or unduly messed with by other tactics
   ---------------------------------------------------------------------- *)

Definition Abbrev_def[nocompute]: Abbrev (x:bool) = x
End
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy="marker",Name="Abbrev"},name=(["Unwanted"],"id")}

val Abbrev_CONG = store_thm(
  "Abbrev_CONG",
  “r1 = r2 ==> Abbrev(v = r1) = Abbrev (v = r2)”,
  STRIP_TAC THEN ASM_REWRITE_TAC[]);


(* ----------------------------------------------------------------------
   For telling the simplifier to case-split on if-then-else terms in
   the goal. Not used as yet.
   ---------------------------------------------------------------------- *)

Definition IfCases_def[nocompute]: IfCases = T
End
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy="marker",Name="IfCases"},name=(["Data","Bool"],"T")}

(*---------------------------------------------------------------------------*)
(* Support for the simplifier                                                *)
(*---------------------------------------------------------------------------*)

Definition AC_DEF[nocompute]: AC b1 b2 <=> b1 /\ b2
End
Definition Req0_def[nocompute]: Req0 = T
End
Definition ReqD_def[nocompute]: ReqD = T
End
Definition Cong_def[nocompute]: Cong (x:bool) = x
End
Definition Exclude_def[nocompute]: Exclude (x:'a) = T
End
Definition ExcludeFrag_def[nocompute]: ExcludeFrag (x:'a) = T
End
Definition FRAG_def[nocompute]: FRAG (x:'a) = T
End
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy="marker",Name="AC"},name=(["Data","Bool"],"/\\")}
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy="bool",Name="/\\"},name=(["Data","Bool"],"/\\")}
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy="marker",Name="Cong"},name=(["Unwanted"],"id")}


(*---------------------------------------------------------------------------*)
(* Support for random user-supplied labels.                                  *)
(*---------------------------------------------------------------------------*)

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 2)),
                   fixity = Infix(NONASSOC, 80),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [HardSpace 1, TOK ":-", BreakSpace(1,0)],
                   term_name = ":-"};

Type label[local] = “:ind”

Definition label_def[nocompute]:
  ((lab:label) :- (argument:bool)) = argument
End

(* ----------------------------------------------------------------------
    The 'using' label
   ---------------------------------------------------------------------- *)

Definition using_def[nocompute]: using (x:label) = T
End
Definition usingThm_def[nocompute]: usingThm (b:bool) = b
End
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy="marker",Name="usingThm"},name=(["Unwanted"],"id")}

val _ = remove_ovl_mapping  "using" {Name = "using", Thy = "marker"}
val _ = remove_ovl_mapping  "usingThm" {Name = "usingThm", Thy = "marker"}

(*---------------------------------------------------------------------------*)
(* Case                                                                      *)
(*                                                                           *)
(* For marking the current case in case divisions and inductive proofs       *)
(*---------------------------------------------------------------------------*)

Definition Case_def[nocompute]:
  Case X = T
End

val add_Case = store_thm (
  "add_Case",
  ``!X. P <=> (Case X ==> P)``,
  REWRITE_TAC [Case_def]);

val elim_Case = store_thm (
  "elim_Case",
  ``(Case X /\ Y) = Y /\
    (Y /\ Case X) = Y /\
    (Case X ==> Y) = Y``,
  REWRITE_TAC [Case_def]
  );

(* ----------------------------------------------------------------------
    hide

    for hiding assumptions from both the user and many tools
   ---------------------------------------------------------------------- *)

Definition hide_def[nocompute]:
  hide (nm:bool) (x:bool) = x
End

val hideCONG = store_thm(
  "hideCONG",
  “hide nm x = hide nm x”,
  REWRITE_TAC[]);

Definition NoAsms[nocompute]: NoAsms = T
End
Definition IgnAsm_def[nocompute]: IgnAsm (v:'a) = T
End

val _ = Tactic.export_ignore {Name = "hide", Thy = "marker"}

val _ = List.app permahide [“hide”, “AC”, “Req0”, “ReqD”]




