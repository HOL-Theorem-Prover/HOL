signature Defn =
sig

   type hol_type = Type.hol_type
   type term = Term.term
   type thm = Thm.thm
   type conv = Abbrev.conv
   type tactic = Abbrev.tactic
   type proofs = GoalstackPure.proofs

   type defn

   val monitoring : bool ref

   val define : string -> term -> defn


   (* What kind of definition is it? *)

   val abbrev  : defn -> bool
   val primrec : defn -> bool
   val nestrec : defn -> bool
   val mutrec  : defn -> bool


   (* Extracting recursion equations, in various formats *)

   val eqns_of : defn -> thm
   val eqnl_of : defn -> thm list


   (* Extracting induction theorem *)
   val ind_of     : defn -> thm option

   (* Peculiar to nested and mutual recursions, respectively *)
   val aux_defn   : defn -> defn option
   val union_defn : defn -> defn option


   (* Parameters of a schematic defn *)
   val parameters : defn -> term list

   (* Extracting termination conditions, setting termination relation *)

   val tcs_of     : defn -> term list
   val reln_of    : defn -> term option
   val set_reln   : defn -> term -> defn

   (* Manipulating termination conditions *)

   val inst_defn  : defn -> (term,term)Lib.subst * 
                            (hol_type,hol_type)Lib.subst -> defn
   val elim_tcs   : defn -> thm list -> defn
   val simp_tcs   : defn -> conv -> defn
   val prove_tcs  : defn -> tactic -> defn

   val tgoal      : defn -> proofs
   val tprove     : defn * tactic -> thm * thm
   val TC_TAC     : defn -> tactic

end
