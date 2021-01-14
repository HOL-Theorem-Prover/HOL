(**
  Structure: TacticMap

  Uses the association map implemented in AssocMap.sml that maps strings to
  tactic "closures".
  Lassie uses it internally to map the SEMPRE returned intermediate language
  into concrete HOL4 tactics code
**)
structure TacticMap =
struct

  open Lib Tactic Tactical Rewrite bossLib mesonLib;

  datatype tacticClos =
    Tactic of tactic
    | Tactical of (tactic -> tactic)
    | TacticComb of (tactic * tactic -> tactic)
    | TermComb of (term quotation * tactic -> tactic)
    | ThmTactic of (thm -> tactic)
    | QuotTactic of (term quotation -> tactic)
    | ThmListTactic of (thm list -> tactic)
    (* first_x_assum ,... *)
    | AsmTestTactic of (thm_tactic -> Tactical.tactic) (* TODO: Fix overloading? *)
    (* qpat_assum, ... *)
    | AsmMatchTactic of (term quotation -> (thm -> tactic) -> tactic)
    (* qspec_then, ... *)
    | QuotSpecThmTactic of (term quotation -> (thm -> tactic) -> thm -> tactic)
    (* qspecl_then, ... *)
    | QuotListSpecThmTactic of (term quotation list -> (thm -> tactic) -> thm -> tactic);

  fun empty (_:unit) = AssocMap.Leaf;

  fun lookupTac (s:string) (tr:(string,tacticClos) AssocMap.tree) =
    AssocMap.lookup s tr String.compare;

  fun insertTac (s:string) (t:tacticClos) (tr:(string,tacticClos) AssocMap.tree) =
    AssocMap.append s t tr String.compare;

  fun insTac (s,t) = insertTac s (Tactic t);
  fun insTact (s, tt) = insertTac s (Tactical tt);
  fun insTacComb (s, tc) = insertTac s (TacticComb tc);
  fun insTmComb (s, tc) = insertTac s (TermComb tc);
  fun insThmTac (s,t) = insertTac s (ThmTactic t);
  fun insQuotTac (s,t) = insertTac s (QuotTactic t);
  fun insThmsTac (s,t) = insertTac s (ThmListTactic t);
  fun insAsmTt (s,t) = insertTac s (AsmTestTactic t);
  fun insAsmMt (s,t) = insertTac s (AsmMatchTactic t);
  fun insQuotSpecTac (s,t) = insertTac s (QuotSpecThmTactic t)
  fun insQuotListSpecTac (s,t) = insertTac s (QuotListSpecThmTactic t);

  fun appendTacs tf s = fn t => foldl (fn (e,t) => tf e t) t s;

  (* Define a standard Lassie Tree that has rudimentary support for the most
     common tactics *)
  val stdTree =
    appendTacs insTac
      [("cheat", cheat), ("strip_tac", strip_tac), ("gen_tac", gen_tac),
       ("Cases", Cases), ("Induct", Induct), ("res_tac", res_tac),
       ("conj_tac", conj_tac), ("all_tac", all_tac), ("NO_TAC", NO_TAC),
       ("EQ_TAC", EQ_TAC), ("CCONTR_TAC", CCONTR_TAC),
       ("AP_THM_TAC", AP_THM_TAC), ("AP_TERM_TAC", AP_TERM_TAC)]
      (empty())
    |> appendTacs insTact [("rpt", rpt), ("TRY", TRY)]
    |> appendTacs insTacComb [("THEN",op THEN), ("ORELSE", op ORELSE)]
    |> appendTacs insTmComb [("by", op by), ("suffices_by", op suffices_by)]
    |> appendTacs insThmTac
        [("imp_res_tac", imp_res_tac), ("assume_tac", assume_tac),
         ("irule", irule), ("drule", drule), ("match_mp_tac", match_mp_tac),
         ("mp_tac", mp_tac)]
    |> appendTacs insQuotTac
        [("Cases_on", Cases_on), ("Induct_on", Induct_on),
         ("completeInduct_on", completeInduct_on), ("qexists_tac", qexists_tac),
         ("sg", sg), ("subgoal", subgoal)]
    |> appendTacs insThmsTac
        [("asm_rewrite_tac", asm_rewrite_tac), ("rewrite_tac", rewrite_tac),
         ("once_rewrite_tac", once_rewrite_tac),
         ("once_asm_rewrite_tac", once_asm_rewrite_tac), ("simp", simp),
         ("fs", fs), ("rfs", rfs), ("rw", rw), ("metis_tac", metis_tac),
         ("MESON_TAC", MESON_TAC)]
    |> appendTacs insAsmTt
        [("first_x_assum", first_x_assum), ("first_assum", first_assum),
         ("last_x_assum", last_x_assum), ("last_assum", last_assum),
         ("spose_not_then", spose_not_then), ("pop_assum", pop_assum) ]
    |> appendTacs insAsmMt
      [("qpat_x_assum", qpat_x_assum), ("qpat_assum", qpat_assum)]
    |> appendTacs insQuotSpecTac [("qspec_then", qspec_then)]
    |> appendTacs insQuotListSpecTac [("qspecl_then", qspecl_then)];

end;
