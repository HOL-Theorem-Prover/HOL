structure res_quanLib :> res_quanLib =
struct

 open Res_quan;
 open Cond_rewrite; 

   type hol_type = Type.hol_type
   type term = Term.term
   type thm = Thm.thm
   type tactic = Abbrev.tactic
   type conv = Abbrev.conv
   type thm_tactic = Abbrev.thm_tactic

end;
