(* ===================================================================== 
 * FILE        : simpLib.sig
 * DESCRIPTION : A programmable, contextual, conditional simplifier 
 *                                                                       
 * AUTHOR      : Donald Syme
 *               Based loosely on original HOL rewriting by 
 *               Larry Paulson et al, and on the Isabelle simplifier.
 * ===================================================================== *)

(* =====================================================================
 * The Simplifier
 *
 * Simplification is traversal/reduction under equality.  This
 * is mainly about rewriting and applying conversions.
 * =====================================================================*)


signature simpLib =
sig
 include Abbrev

   (* ---------------------------------------------------------------------
    * type simpset
    *
    * A Simpset contains:
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
                    conv: (term list -> term -> thm) -> term list -> conv};

  datatype ssdata = SIMPSET of
    { convs: convdata list,
      rewrs: thm list,
         ac: (thm * thm) list,
     filter: (thm -> thm list) option,
     dprocs: Traverse.reducer list,
      congs: thm list};

  (*------------------------------------------------------------------------*)
  (* Easy building of common kinds of ssdata objects                        *)
  (*------------------------------------------------------------------------*)

  val rewrites : thm list -> ssdata
  val dproc_ss : Traverse.reducer -> ssdata
  val ac_ss    : (thm * thm) list -> ssdata
  val merge_ss : ssdata list -> ssdata

   (* ---------------------------------------------------------------------
    * mk_simpset: Joins several ssdata fragments to make a simpset.
    * This is a "runtime" object - the ssdata can be thought of as the
    * static, data objects.
    * Beware of duplicating information - you should only
    * merge distinct ssdata fragments! (like BOOL_ss and PURE_ss).
    * You cannot merge simpsets with lower-case names (like bool_ss).
    *
    * The order of the merge is significant w.r.t. congruence rules
    * and rewrite makers.
    * ---------------------------------------------------------------------*)

  type simpset

  val empty_ss   : simpset
  val mk_simpset : ssdata list -> simpset
  val ++         : simpset * ssdata -> simpset  (* infix *)

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
   val ASM_SIMP_TAC  : simpset -> thm list -> tactic
   val FULL_SIMP_TAC : simpset -> thm list -> tactic
   
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

   (* ---------------------------------------------------------------------
    * Simpset pretty printing
    * ---------------------------------------------------------------------*)

end
