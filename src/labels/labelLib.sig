signature labelLib =
sig

  include Abbrev
  val label_tm : term
  val label_ty : hol_type

  val lb : string -> term

  val LB : string -> thm
  val is_label_ref : thm -> bool
  val dest_label_ref : thm -> string

  val is_label : term -> bool
  val dest_label : term -> string * term
  val mk_label : string * term -> term

  val MK_LABEL : string * thm -> thm
  val DEST_LABEL : thm -> thm
  val DEST_LABELS : thm -> thm

  val DEST_LABEL_CONV : conv
  val DEST_LABELS_CONV : conv

  val DEST_LABELS_TAC : tactic

  val find_labelled_assumption : thm -> term list -> thm

  val ASSUME_NAMED_TAC : string -> thm -> tactic
  val LABEL_ASSUM : string -> thm_tactic -> tactic
  val LABEL_X_ASSUM : string -> thm_tactic -> tactic

  val LLABEL_RESOLVE : thm list -> term list -> thm list

end;

(*

   [label_tm] is the operator used to construct labelled terms.  It is of
   type label -> bool -> bool, and label x y has value y (by definition).

   [label_ty] is the type of labels, used only to create variables of
   this type, which in turn serve as variables.

   [lb s] creates a variable of type label.  Such terms are the labels
   used in labelled terms.

   [LB s] creates a "label reference theorem".  This is essentially a
   mechanism for storing a string in a theorem.  The exact form of the
   theorem is not interesting and shouldn't be relied on.  The point
   is that instead of passing a theorem to some tactic, one can pass a
   label reference, and the tactic will know enough to follow the reference
   and turn it into a genuine theorem off the assumption list.

   [is_label_ref th] returns true if th is a "label reference theorem".

   [dest_label_ref th] returns the string that a "label reference theorem"
   encodes.  Forall strings s, dest_label (LB s) = s.  dest_label_ref will
   raise a HOL_ERR if th is not a label reference theorem.

   [is_label t] returns true if t is a labelled term, conceptually of the
   form ``label s t0``.

   [dest_label t] returns (s, t0) if t is ``label s t0``.

   [mk_label (s,t)] returns ``label s t``

   [MK_LABEL(s, th)] when th is A |- t, then this call returns
       A |- label s t

   [DEST_LABEL (A |- label s t)] returns A |- t.  If the argument is not of
   the required form, then a HOL_ERR exception is raised.

   [DEST_LABELS th] replaces all instances of ``label s t`` in the
   conclusion of th with t.

   [DEST_LABEL_CONV t] if t is of the form ``label s t``, this returns the
   theorem  |- label s t = t

   [DEST_LABELS_CONV t] replaces all instances of ``label s t0`` in t with t0,
   generating the term t', and returns the theorem |- t = t'

   [DEST_LABELS_TAC (asl,w)] applies DEST_LABELS_CONV to both w, and
   all of the assumptions, asl.

   [find_labelled_assumption thm asl] If thm is a label reference theorem,
   and there is a term of the form label s t in asl, and s is the label
   referred to in thm, then return [label s t] |- t.  Otherwise, raise a
   HOL_ERR.

   [ASSUME_NAMED_TAC s th] assumes th and gives it label s.

   [LABEL_ASSUM s ttac] looks for an assumption labelled with s, and passes
   the theorem (less its label) to ttac.

   [LABEL_X_ASSUM s ttac] as for LABEL_ASSUM, but the assumption is pulled
   from the goal's list of assumptions.

   [LLABEL_RESOLVE thlist asl] works through the list of theorems
   thlist, and for each label reference theorem in thlist, pulls out a
   matching labelled theorem (using find_labelled_assumption, above)
   from asl.  These, the non-labelled assumptions in asl (which are
   all ASSUMEd), and the non-reference theorems in thlist are
   concatenated together and returned.

*)
