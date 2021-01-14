structure realTacticsLib =
struct

  open LassieLib;

  local open realTheory RealArith in end;
  val _ =
    let
      fun jargon () =
        let val _ = LassieLib.addCustomTactic RealArith.REAL_ASM_ARITH_TAC "REAL_ASM_ARITH_TAC"
        val _ = LassieLib.addCustomTactic DECIDE_TAC "DECIDE_TAC"
        val rw_th = fn thm => once_rewrite_tac[thm];
        val _ = LassieLib.addCustomThmTactic rw_th "rw_th";
        val _ =
          map (uncurry def) [
          (* intro tactics *)
            (`introduce variables`, `rpt gen_tac`),
            (`introduce assumptions`, `rpt strip_tac`),
          (* Custom tactic *)
            (`rewrite last assumption`, `pop_assum rw_th`),
            (`rewrite ADD_ASSOC for 'n'`, `qspec_then 'n' rw_th ADD_ASSOC`),
            (‘trivial’, ‘REAL_ASM_ARITH_TAC’),
            (`we know 'T'`, `'T' by (REAL_ASM_ARITH_TAC ORELSE DECIDE_TAC)`)
          ]
        in () end
    in
      LassieLib.registerJargon "Reals" jargon
    end;
end;
