signature tflLib =
sig
 type term = Term.term
 type fixity = Term.fixity
 type thm =  Thm.thm
 type tactic = Abbrev.tactic

 val current_congs : unit -> thm list

   val rfunction  
    : ({induction:thm, rules:thm, TCs:term list list} 
        -> {induction:thm, rules:thm, nested_tcs:thm list})
            -> (thm list -> thm -> thm)
                 -> string -> term frag list -> term frag list 
                     -> {induction:thm, rules:thm, tcs:term list}

   val Rfunction  : string 
                     -> term frag list 
                       -> term frag list 
                         -> {induction:thm, rules:thm, tcs:term list}

   val lazyR_def : string -> term frag list -> thm
   val function  : string -> term frag list -> thm

   val WF_TAC : thm list -> tactic
   val tc_simplifier : thm list -> term -> thm
   val terminator : tactic
   val std_postprocessor 
     : {induction:thm, rules:thm, TCs:term list list} 
       -> {induction:thm, rules:thm, nested_tcs:thm list}

   val REC_INDUCT_TAC : thm -> tactic
   val PROGRAM_TAC : {induction: thm, rules : thm} -> tactic
   val PROG_TAC : {induction: thm, rules : thm} -> tactic

   val tgoal : {induction:thm,rules:thm,tcs:term list} -> goalstackLib.proofs
   val prove_termination : {induction:thm,rules:thm,tcs:term list}
                            -> tactic -> thm

   (* Miscellaneous *)
   val pred : term
   val list_pred : term
   val timing : bool ref
  end ;
