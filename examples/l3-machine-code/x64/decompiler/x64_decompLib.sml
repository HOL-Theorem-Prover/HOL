structure x64_decompLib :> x64_decompLib =
struct

open HolKernel Parse boolLib bossLib
open helperLib set_sepTheory addressTheory progTheory wordsTheory wordsLib
open pred_setTheory combinTheory x64_progTheory listTheory decompilerLib

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars x64_progTheory.x64_prog_grammars
end

open Parse

local
   val x64_triple = Q.INST [`rip` |-> `p`] o x64_progLib.x64_spec
   val match_pc_cond = fst o match_term ``x64_PC (if b then x else y)``
   val lemma1 = prove(``b ==> (x64_PC (if b then x else y) = x64_PC x)``,
                      SIMP_TAC std_ss []);
   val lemma2 = prove(``~b ==> (x64_PC (if b then x else y) = x64_PC y)``,
                      SIMP_TAC std_ss []);
   val lemma3 = SPEC_MOVE_COND |> GSYM |> REWRITE_RULE [GSYM precond_def]
   fun get_length th =
      let
         val (_,_,c,_) = th |> concl |> dest_spec
      in
         c |> rator |> rand |> rand |> listSyntax.dest_list |> fst |> length
      end
   val find_exit =
      stateLib.get_pc_delta
         (Lib.equal "x64_prog$x64_PC" o fst o boolSyntax.dest_strip_comb)
   fun finalise th = (th, get_length th, find_exit th)
in
   fun x64_triples hex =
      let
         val th = x64_triple hex
         val (th1, th2) =
            let
               val m = match_pc_cond (find_term (can match_pc_cond) (concl th))
               fun fix l = finalise o REWRITE_RULE [lemma3] o
                           DISCH_ALL o REWRITE_RULE [UNDISCH (INST m l)]
            in
               (fix lemma1 th, SOME (fix lemma2 th))
            end
            handle HOL_ERR _ => (finalise th, NONE)
      in
         (th1, th2)
      end
end

val (x64_tools:decompiler_tools) =
   (x64_triples, fn _ => fail(), x64_ALL_EFLAGS_def, ``x64_PC``)

val x64_decompile = decompilerLib.decompile x64_tools

val x64_decompile_code =
   decompilerLib.decompile_with x64AssemblerLib.x64_code_no_spaces x64_tools


(* Testing:

val (text_cert, test_def) = x64_decompile_code "test" `add rax, rbx`

val x64_triples = Count.apply x64_triples

  val hex = "55"; x64_triples hex;
  val hex = "4889E5"; x64_triples hex;
  val hex = "48897DE8"; x64_triples hex;
  val hex = "8975E4"; x64_triples hex;
  val hex = "C745F800000000"; x64_triples hex;
  val hex = "EB3B"; x64_triples hex;
  val hex = "8B45F8"; x64_triples hex;
  val hex = "4863D0"; x64_triples hex;
  val hex = "488B45E8"; x64_triples hex;
  val hex = "4801D0"; x64_triples hex;
  val hex = "0FB600"; x64_triples hex;
  val hex = "0FBEC0"; x64_triples hex;
  val hex = "8945FC"; x64_triples hex;
  val hex = "837DFC60"; x64_triples hex;
  val hex = "7E1B"; x64_triples hex;
  val hex = "837DFC7A"; x64_triples hex;
  val hex = "7F15"; x64_triples hex;
  val hex = "8B45F8"; x64_triples hex;
  val hex = "4863D0"; x64_triples hex;
  val hex = "488B45E8"; x64_triples hex;
  val hex = "4801C2"; x64_triples hex;
  val hex = "8B45FC"; x64_triples hex;
  val hex = "83E820"; x64_triples hex;
  val hex = "8802"; x64_triples hex;
  val hex = "8345F801"; x64_triples hex;
  val hex = "8B45F8"; x64_triples hex;
  val hex = "3B45E4"; x64_triples hex;
  val hex = "7CBD"; x64_triples hex;
  val hex = "5D"; x64_triples hex;

*)

end
