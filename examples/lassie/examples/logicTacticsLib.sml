structure logicTacticsLib =
struct

  open LassieLib;

  local open realTheory in end;
  val _ =
    let
    fun jargon () =
      let
        val _ =
        map (uncurry def) [
          (* Case splitting *)
          (‘split conjuncts’, ‘conj_tac THEN rpt conj_tac’),
          (`case split`, `(split conjuncts) ORELSE (EQ_TAC ORELSE Cases)`),
          (`case split for 's'`,`Cases_on 's'`),
          (`perform a case split`,`case split`),
          (`specialize for 'T'`,`first_x_assum qspec_then ' T ' assume_tac`),
          (`assume the contrary`,`CCONTR_TAC`),
          (* Automation a la textbook *)
          (`trivial`,`metis_tac [ ]`),
          (`trivial using [CONJ_COMM]`, `metis_tac [ CONJ_COMM ]`),
          (`follows trivially`,`fs [ ]`),
          (`follows from [ADD_COMM]`, `fs [ ADD_COMM ]`),
          (* Simplification *)
          (`simplify`, `fs [ ]`),
          (`simplify with [CONJ_COMM]`, `fs [ CONJ_COMM ]`),
          (`simplify conclusion`, `simp [ ]`),
          (`simplify conclusion with [CONJ_COMM]`, `simp [ CONJ_COMM ]`),
          (* lc aliases *)
          (`try gen_tac`, `TRY gen_tac`),
          (* `try solving with [CONJ_COMM]` [`TRY simp [CONJ_COMM]`]; *)
          (* Textbook style tactics for existentials, modus ponens, ... *)
          (`choose 'e'`, `qexists_tac ' e '`),
          (`use transitivity for 'x'`, `irule REAL_LE_TRANS THEN qexists_tac ' x '`),
          (`use REAL_LE_TRANS`, `irule REAL_LE_TRANS`),
          (`resolve with REAL_NEG_INV`, `imp_res_tac REAL_NEG_INV`),
          (`induction on 'n'`, `Induct_on ' n '`),
          (* rewriting *)
          (`rewrite once [REAL_INV_1OVER]`, `once_rewrite_tac [ REAL_INV_1OVER ]`),
          (`rewrite once [<- REAL_INV_1OVER]`, `once_rewrite_tac [ GSYM REAL_INV_1OVER ]`),
          (`rewrite with [REAL_INV_1OVER]`, `rewrite_tac [REAL_INV_1OVER]`),
          (`rewrite with [<- REAL_INV_1OVER]`, `rewrite_tac [GSYM REAL_INV_1OVER]`),
          (`rewrite assumptions`, `asm_rewrite_tac []`),
          (`rewrite assumptions and [ADD_ASSOC] `, `asm_rewrite_tac [ADD_ASSOC]`),
          (* subgoals *)
          (`we show first 'T'`, `sg 'T'`),
          (`we show next 'T'`, `we show first 'T'`),
          (`we show 'T' using (gen_tac)`, `'T' by gen_tac`),
          (`we know 'T'`, `'T' by (fs [ ])`),
          (`thus 'T'`, `we know 'T'`),
          (`'T' using (cheat)`, `'T' by (cheat)`),
          (`showing 'T' closes the proof because (gen_tac)`, `'T' suffices_by (gen_tac)`),
          (‘Case 'x'’, ‘Goal 'x'’),
          (‘cheat then cheat’, ‘cheat THEN cheat’),
          (‘Next Goal’, ‘Goal 1’)
        ]
      in () end;
  in
    LassieLib.registerJargon "Logic" (jargon)
  end

end;
