(* ========================================================================= *)
(* ADDITIONS TO HOL TERM AND TYPE MATCHING.                                  *)
(* Created by Joe Hurd, June 2002.                                           *)
(* ========================================================================= *)

signature matchTools =
sig

type ('a, 'b) subst = ('a, 'b) Lib.subst
type hol_type       = Type.hol_type
type term           = Term.term
type thm            = Thm.thm
type tySubst        = (hol_type, hol_type) subst
type Subst          = (term, term) subst * tySubst

(* Basic operations on substitutions *)
val pinst             : Subst -> term -> term
val INST_TY           : tySubst -> thm -> thm
val PINST             : Subst -> thm -> thm
val type_refine_subst : tySubst -> tySubst -> tySubst
val refine_subst      : Subst -> Subst -> Subst

(* Raw matching *)
type raw_subst
val empty_raw_subst : raw_subst
val raw_match_term  : raw_subst -> term -> term -> raw_subst
val raw_match_ty    : raw_subst -> hol_type -> hol_type -> raw_subst
val finalize_subst  : raw_subst -> Subst

(* Operations on types containing "locally constant" variables *)
type tyVars = hol_type -> bool
val vmatch_type  : tyVars -> hol_type -> hol_type -> tySubst
val vunifyl_type : tyVars -> tySubst -> (hol_type * hol_type) list -> tySubst
val vunify_type  : tyVars -> hol_type list -> tySubst

(* Operations on terms containing "locally constant" variables *)
type tmVars = term -> bool
type Vars   = tmVars * tyVars
val vfree_names : tmVars -> term -> string list
val vfree_vars  : Vars -> term -> term list * hol_type list
val vmatch      : Vars -> term -> term -> Subst
val vunifyl     : Vars -> Subst -> (term * term) list -> Subst
val vunify      : Vars -> term list -> Subst
val vmatch_uty  : Vars -> term -> term -> Subst

end
