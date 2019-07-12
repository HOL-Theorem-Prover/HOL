(* =====================================================================
 * FILE        : simpLib.sig
 * DESCRIPTION : A programmable, contextual, conditional simplifier
 *
 * AUTHOR      : Donald Syme
 *               Based loosely on original HOL rewriting by
 *               Larry Paulson et al, and on the Isabelle simplifier.
 * =====================================================================*)


signature simpLib =
sig
 include Abbrev

   (* ---------------------------------------------------------------------
    * type simpset
    *
    * A simpset contains:
    *    - a collection of rewrite rules
    *    - a collection of equational conversions
    *    - a traversal strategy for applying them
    *
    * The traversal strategy may include other actions, especially
    * decision procedures, which can work cooperatively with
    * rewriting during simplification.
    *
    * REWRITE RULES
    *
    * Simpsets are foremost a collection of rewrite theorems stored
    * efficiently in a termnet.  These are made into conversions
    * by using COND_REWR_CONV.
    *
    * CONVERSIONS IN SIMPSETS
    *
    * Simpsets can contain arbitrary user conversions, as well as
    * rewrites and contextual-rewrites.  These conversions should
    * be thought of as infinite families of rewrites.
    *
    * Conversions can be keyed by term patterns (implemented
    * using termnets).  Thus a conversion won't even be called if
    * the target term doesn't match (in the termnet sense of matching)
    * its key.
    * ---------------------------------------------------------------------*)

  type convdata = { name: string,
                     key: (term list * term) option,
                   trace: int,
                    conv: (term list -> term -> thm) -> term list -> conv}

  type stdconvdata = { name: string,
                       pats: term list,
                       conv: conv}

  type relsimpdata = {refl: thm,
                      trans:thm,
                      weakenings:thm list,
                      subsets : thm list,
                      rewrs : thm list}

  type controlled_thm = BoundedRewrites.controlled_thm

  type ssfrag

  val SSFRAG :
    {name : string option,
     convs: convdata list,
     rewrs: (string option * thm) list,
        ac: (thm * thm) list,
    filter: (controlled_thm -> controlled_thm list) option,
    dprocs: Traverse.reducer list,
     congs: thm list} -> ssfrag

  val frag_rewrites : ssfrag -> thm list
  val frag_name : ssfrag -> string option

  (*------------------------------------------------------------------------*)
  (* Easy building of common kinds of ssfrag objects                        *)
  (*------------------------------------------------------------------------*)

  val Cong        : thm -> thm
  val AC          : thm -> thm -> thm
  val Excl        : string -> thm
  val Req0        : thm -> thm
  val ReqD        : thm -> thm

  val rewrites       : thm list -> ssfrag
  val rewrites_with_names : (string * thm) list -> ssfrag
  val dproc_ss       : Traverse.reducer -> ssfrag
  val ac_ss          : (thm * thm) list -> ssfrag
  val conv_ss        : convdata -> ssfrag
  val relsimp_ss     : relsimpdata -> ssfrag
  val std_conv_ss    : stdconvdata -> ssfrag
  val merge_ss       : ssfrag list -> ssfrag
  val name_ss        : string -> ssfrag -> ssfrag
  val named_rewrites : string -> thm list -> ssfrag
  val named_rewrites_with_names : string -> (string * thm) list -> ssfrag
  val named_merge_ss : string -> ssfrag list -> ssfrag
  val type_ssfrag    : hol_type -> ssfrag
  val tyi_to_ssdata  : TypeBasePure.tyinfo -> ssfrag

  val partition_ssfrags : string list -> ssfrag list ->
                          (ssfrag list * ssfrag list)

   (* ---------------------------------------------------------------------
    * mk_simpset: Joins several ssfrag fragments to make a simpset.
    * This is a "runtime" object - the ssfrag can be thought of as the
    * static, data objects.
    * Beware of duplicating information - you should only
    * merge distinct ssfrag fragments! (like BOOL_ss and PURE_ss).
    * You cannot merge simpsets with lower-case names (like bool_ss).
    *
    * The order of the merge is significant w.r.t. congruence rules
    * and rewrite makers.
    * ---------------------------------------------------------------------*)

  type simpset
  type weakener_data = Travrules.preorder list * thm list * Traverse.reducer

  val empty_ss        : simpset
  val ssfrags_of      : simpset -> ssfrag list
  val mk_simpset      : ssfrag list -> simpset
  val remove_ssfrags  : simpset -> string list -> simpset
  val ssfrag_names_of : simpset -> string list
  val ++              : simpset * ssfrag -> simpset  (* infix *)
  val -*              : simpset * string list -> simpset (* infix *)
  val &&              : simpset * thm list -> simpset  (* infix *)
  val limit           : int -> simpset -> simpset
  val unlimit         : simpset -> simpset

  val add_weakener : weakener_data -> simpset -> simpset

  val add_relsimp  : relsimpdata -> simpset -> simpset

  val traversedata_for_ss: simpset -> Traverse.traverse_data


   (* ---------------------------------------------------------------------
    * SIMP_CONV : simpset -> conv
    *
    * SIMP_CONV makes a simplification conversion from the given simpset.  The
    * conversion uses a top-depth strategy for rewriting.  It sets both
    * the solver and the depther to be SIMP_CONV itself.
    *
    * FAILURE CONDITIONS
    *
    * SIMP_CONV never fails, though it may diverge.  Beware of
    * divergence when trying to solve conditions to conditional rewrites.
    * ---------------------------------------------------------------------*)

   val SIMP_PROVE : simpset -> thm list -> term -> thm
   val SIMP_CONV  : simpset -> thm list -> conv

   (* ---------------------------------------------------------------------
    * SIMP_TAC : simpset -> tactic
    * ASM_SIMP_TAC : simpset -> tactic
    * FULL_SIMP_TAC : simpset -> tactic
    *
    * SIMP_TAC makes a simplification tactic from the given simpset.  The
    * tactic uses a top-depth strategy for rewriting, and will be recursively
    * reapplied when a simplification step makes a change to a term.
    * This is done in the same way as similar to TOP_DEPTH_CONV.
    *
    * ASM_SIMP_TAC draws extra rewrites (conditional and unconditional)
    * from the assumption list.  These are also added to the context that
    * will be passed to conversions.
    *
    * FULL_SIMP_TAC simplifies the assumptions one by one, before
    * simplifying the goal.  The assumptions are simplified in the order
    * that they are found in the assumption list, and the simplification
    * of each assumption is used when simplifying the next assumption.
    *
    * FAILURE CONDITIONS
    *
    * These tactics never fail, though they may diverge.
    * ---------------------------------------------------------------------*)

   val SIMP_TAC      : simpset -> thm list -> tactic
   val simp_tac      : simpset -> thm list -> tactic
   val ASM_SIMP_TAC  : simpset -> thm list -> tactic
   val asm_simp_tac  : simpset -> thm list -> tactic
   val FULL_SIMP_TAC : simpset -> thm list -> tactic
   val full_simp_tac : simpset -> thm list -> tactic

   val REV_FULL_SIMP_TAC          : simpset -> thm list -> tactic
   val rev_full_simp_tac          : simpset -> thm list -> tactic
   val NO_STRIP_FULL_SIMP_TAC     : simpset -> thm list -> tactic
   val NO_STRIP_REV_FULL_SIMP_TAC : simpset -> thm list -> tactic

   (* ---------------------------------------------------------------------
    * SIMP_RULE : simpset -> tactic
    * ASM_SIMP_RULE : simpset -> tactic
    *
    * Make a simplification rule from the given simpset.  The
    * rule uses a top-depth strategy for rewriting.
    *
    * FAILURE CONDITIONS
    *
    * These rules never fail, though they may diverge.
    * ---------------------------------------------------------------------*)

   val SIMP_RULE     : simpset -> thm list -> thm -> thm
   val ASM_SIMP_RULE : simpset -> thm list -> thm -> thm

   (* ---------------------------------------------------------------------*)
   (* Accumulating the rewrite rules that are actually used.               *)
   (* ---------------------------------------------------------------------*)

   val used_rewrites : thm list ref
   val track_rewrites : bool ref

   val track : ('a -> 'b) -> 'a -> 'b

   (* ---------------------------------------------------------------------*)
   (* Prettyprinters for ssfrags and simpsets.                             *)
   (* ---------------------------------------------------------------------*)

   val pp_ssfrag : ssfrag Parse.pprinter
   val pp_simpset : simpset Parse.pprinter

end
