structure riscv_decompLib :> riscv_decompLib =
struct

open HolKernel Parse boolLib bossLib
open helperLib set_sepTheory addressTheory progTheory
open pred_setTheory combinTheory
open riscv_progLib decompilerLib

val ERR = Feedback.mk_HOL_ERR "riscv_decompLib"

local
  fun syn n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "riscv_prog"
  val riscv_1 = syn 2 HolKernel.dest_monop HolKernel.mk_monop
  val (riscv_PC_tm, _, _, is_riscv_PC) = riscv_1 "riscv_PC"
  fun get_inst_length th =
    let
      val (_,_,c,_) = dest_spec (concl th)
    in
      c |> rator |> rand |> rand |> listSyntax.dest_list |> fst |> length
    end handle HOL_ERR _ => 4
  fun format_thm th = (th, get_inst_length th, stateLib.get_pc_delta is_riscv_PC th)
  fun format_riscv_spec hex =
    case List.map format_thm (riscv_progLib.riscv_spec_hex hex) of
       [x] => (x, NONE)
     | [x1, x2] => (x1, SOME x2)
     | _ => raise ERR "format_riscv_spec" ""
in
  val riscv_tools =
    (format_riscv_spec, fn _ => fail(), TRUTH, riscv_PC_tm): decompiler_tools
end

val riscv_decompile =
  decompilerLib.decompile_with helperLib.quote_to_strings riscv_tools:
  string -> string frag list -> thm * thm

end
