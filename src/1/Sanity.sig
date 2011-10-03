signature Sanity =
sig

 type term = Term.term
 type thm = Thm.thm
 type theory = Hol_pp.theory
 type tactic = Abbrev.tactic

 val accepted_axioms  : string list ref;
 val accepted_oracles : string list ref;

 (* Traces 

    "Santity Check Strict":
    ------------------------
    Turn warnings or exception on or off.
    Default: true (through exception)

    "Santity Check Verbose":
    ------------------------
    Turn verbose reporting on or off.
    Default: true
  

    "Santity Check Free Vars":
    --------------------------
    Turn checking for free top-level variables to different levels:
      0 : allow no free vars
      1 : if theorem starts with an allquantor, then allow no free vars
      2 : no check        
    Default: 1
  

    "Santity Check Var-Const Clash":
    --------------------------------
    Turn checks whether constant names are used as variables on or off.
    Default: true


    "Santity Check Thm-Name Clash":
    -------------------------------
    Turn checks whether the same theorem name is used in multiple theories.
    Default: true

  *)


 (* sanity checks the given theory *)
 val sanity_check_theory    : string -> bool

 (* sanity checks the current theory *)
 val sanity_check           : unit   -> bool

 (* sanity checks all loaded theories *)
 val sanity_check_all       : unit   -> bool

 (* sanity checks a theorem *)
 val sanity_check_thm       : thm -> bool

 (* sanity checks a theorem with a given name *)
 val sanity_check_named_thm : (string * thm) -> bool


 (* versions of prove, store_thm and save_thm that perform checks,
    see trace "Sanity Check Strict" *)  
 val sanity_prove : (term * tactic) -> thm
 val save_thm     : (string * thm) -> thm
 val store_thm    : (string * term * tactic) -> thm

end
