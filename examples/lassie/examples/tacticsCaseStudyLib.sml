structure tacticsCaseStudyLib =
struct

(** Below we add some natural language tactics to Lassie first, then we showcase
    how Lassie generalizes them using SEMPRE **)

(* First, add some custom tactics, this is also how a hand crafted decision
   procedure can be added *)
val _ = LassieLib.addCustomTactic "REAL_ASM_ARITH_TAC";
val _ = LassieLib.addCustomTactic "impl_tac";
val _ = LassieLib.addCustomTactic "cheat";
val _ = LassieLib.addCustomTactic "EQ_TAC";

val _ = LassieLib.def `introduce variables` [`rpt gen_tac`];
val _ = LassieLib.def `introduce variables and assumptions` [`rpt strip_tac`];
val _ = LassieLib.def `case split for 's'` [`Cases_on 's'`];
val _ = LassieLib.def `case split` [`(rpt conj_tac ORELSE EQ_TAC) ORELSE Cases`];
val _ = LassieLib.def `trivial using [CONJ_COMM]` [`metis_tac [CONJ_COMM]`];
val _ = LassieLib.def `simplify with [CONJ_COMM]` [`simp [CONJ_COMM]`];
val _ = LassieLib.def `try solving with [CONJ_COMM]` [`TRY simp [CONJ_COMM]`];
val _ = LassieLib.def `choose 'e'` [`qexists_tac 'e'`];
val _ = LassieLib.def `use transitivity for 'x'` [`irule REAL_LE_TRANS THEN qexists_tac 'x'`];
val _ = LassieLib.def `use REAL_LE_TRANS` [`irule REAL_LE_TRANS`];
val _ = LassieLib.def `perform a case split` [`rpt conj_tac`];
val _ = LassieLib.def `we show first 'T'` [`sg 'T'`];
val _ = LassieLib.def `we show 'T' using (gen_tac)` [`'T' by (gen_tac)`];
val _ = LassieLib.def `introduce assumptions` [`rpt strip_tac`];
val _ = LassieLib.def `rewrite once [REAL_INV_1OVER]` [`once_rewrite_tac [REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite once [<- REAL_INV_1OVER]` [`once_rewrite_tac [GSYM REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite with [REAL_INV_1OVER]` [`rewrite_tac [REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite with [<- REAL_INV_1OVER]` [`rewrite_tac [GSYM REAL_INV_1OVER]`];
val _ = LassieLib.def `we show next 'T'` [`we show first 'T'`];
val _ = LassieLib.def `'T' using (fs[])` [`'T' by ( fs[] )`];
val _ = LassieLib.def `we know 'T'` [`'T' by (REAL_ASM_ARITH_TAC)`];
val _ = LassieLib.def `thus 'T'` [`we know 'T'`];
val _ = LassieLib.def `resolve with REAL_NEG_INV` [`imp_res_tac REAL_NEG_INV`];
val _ = LassieLib.def `follows from [CONJ_COMM]` [`asm_rewrite_tac [CONJ_COMM] THEN fs[CONJ_COMM]`];
val _ = LassieLib.def `gen_tac . gen_tac` [`gen_tac THEN gen_tac`];
val _ = LassieLib.def `gen_tac .` [`gen_tac THEN all_tac`];

(*
local open LassieLib;
in
val _ = LassieLib.def "introduce variables" ["rpt gen_tac"];
val _ = LassieLib.def "introduce assumptions" ["rpt strip_tac"];
end;

val _ = LassieLib.def "introduce variables and assumptions" ["introduce variables THEN introduce assumptions"];
val _ = LassieLib.def "we show `T` using (gen_tac)" ["`T` by (gen_tac)"];

val _ = LassieLib.def "case split" ["rpt conj_tac ORELSE EQ_TAC"];
val _ = LassieLib.def "case split for `s`" ["Cases_on `s`"];

val _ = LassieLib.nltac "case split for `t`.";
val _ = LassieLib.nltac "case split for `A and B`.";

val _ = LassieLib.def "trivial using [CONJ_COMM]" ["metis_tac [CONJ_COMM]"];

val _ = LassieLib.nltac "trivial using [REAL_ADD_ASSOC].";
val _ = LassieLib.nltac "trivial using [REAL_ADD_ASSOC, CONJ_COMM, REAL_LDISTRIB].";

(** The below tactics generalize for arbitrary list similarly *)
val _ = LassieLib.def "simplify with [MULT]" ["simp [MULT]"];
val _ = LassieLib.def "solve with [MULT]" ["simp [MULT]"];
val _ = LassieLib.def "try solve with [MULT]" ["TRY solve with [MULT]"];

(* Note that the above generalizes "try" for any! tactic *)
val _ = LassieLib.nltac "try simplify with [MULT].";

val _ = LassieLib.def "choose `e`" ["qexists_tac `e`"];
val _ = LassieLib.def "use REAL_LE_TRANS" ["irule REAL_LE_TRANS"];
val _ = LassieLib.def "perform a case split" ["rpt conj_tac"];
val _ = LassieLib.def "we show first `T`" ["sg `T`"];
val _ = LassieLib.def "use transitivity for `x`" ["irule REAL_LE_TRANS THEN qexists_tac `x`"];

val _ = LassieLib.def "rewrite once [REAL_INV_1OVER]" ["once_rewrite_tac [REAL_INV_1OVER]"];
val _ = LassieLib.def "rewrite once [<- REAL_INV_1OVER]" ["once_rewrite_tac [GSYM REAL_INV_1OVER]"];

val _ = LassieLib.nltac "rewrite once [<- MULT].";
(* FIXME: LassieLib.nltac "solve with [<- MULT]." *)

val _ = LassieLib.def "rewrite with [REAL_INV_1OVER]" ["rewrite_tac [REAL_INV_1OVER]"];
val _ = LassieLib.def "rewrite with [<- REAL_INV_1OVER]" ["rewrite_tac [GSYM REAL_INV_1OVER]"];

val _ = LassieLib.def "we show next `T`" ["we show first `T`"];
val _ = LassieLib.def "`T` using (fs[])" ["`T` by (fs[])"];
val _ = LassieLib.def "we know `T`" ["`T` by (REAL_ASM_ARITH_TAC)"];
val _ = LassieLib.def "thus `T`" ["we know `T`"];
val _ = LassieLib.def "resolve with REAL_NEG_INV" ["imp_res_tac REAL_NEG_INV"];
val _ = LassieLib.def "follows from [CONJ_COMM]" ["asm_rewrite_tac [CONJ_COMM] THEN fs[CONJ_COMM]"];
*)

end
