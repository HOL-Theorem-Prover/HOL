signature TotalDefn =
sig

  type hol_type = Type.hol_type
  type term     = Term.term
  type thm      = Thm.thm;
  type conv     = Abbrev.conv
  type tactic   = Abbrev.tactic
  type proofs   = GoalstackPure.proofs
  type defn     = Defn.defn
  type 'a quotation = 'a Portable.frag list

   (* Support for automated termination proofs *)
   val default_prover : tactic
   val guessR         : defn -> term list
   val try_proof      : defn -> tactic -> term -> defn
   val proveTotal0    : tactic -> defn -> defn 
   val proveTotal     : defn -> defn

   (* Support for interactive termination proofs *)
   val tgoal          : defn -> proofs
   val tprove         : defn * tactic -> thm * thm
   val TC_SIMP_CONV   : thm list -> conv
   val TC_SIMP_TAC    : tactic
   val TC_INTRO_TAC   : defn -> tactic
   val WF_REL_TAC     : defn -> term quotation -> tactic

   (* Definitions with automated termination proof support *)
   val xDefine        : string -> term quotation -> thm
   val Define         : term quotation -> thm

   val ind_suffix     : string ref
   val def_suffix     : string ref

end
