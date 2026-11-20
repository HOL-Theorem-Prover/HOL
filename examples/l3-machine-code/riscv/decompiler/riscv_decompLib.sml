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
  val (riscv_PC_noC_tm, _, _, is_riscv_PC_noC) = riscv_1 "riscv_PC_noC"
  fun get_inst_length th =
    let
      val (_,_,c,_) = dest_spec (concl th)
    in
      c |> rator |> rand |> rand |> listSyntax.dest_list |> fst |> length
    end handle HOL_ERR _ => 4
  fun format_thm is_pc th = (th, get_inst_length th, stateLib.get_pc_delta is_pc th)
  fun spec_hex rvc hex =
    let
      val old = riscv_progLib.riscv_rvc ()
      val () = riscv_progLib.riscv_rvc_config rvc
    in
      riscv_progLib.riscv_spec_hex hex before riscv_progLib.riscv_rvc_config old
      handle e => (riscv_progLib.riscv_rvc_config old; raise e)
    end
  fun format_riscv_spec rvc hex =
    case List.map (format_thm (if rvc then is_riscv_PC else is_riscv_PC_noC))
           (spec_hex rvc hex) of
       [x] => (x, NONE)
     | [x1, x2] => (x1, SOME x2)
     | _ => raise ERR "format_riscv_spec" ""
  fun tools rvc =
    (format_riscv_spec rvc, fn _ => fail(), TRUTH,
     if rvc then riscv_PC_tm else riscv_PC_noC_tm): decompiler_tools
in
  val riscv_tools = tools true
  val riscv_tools_noC = tools false
end

val riscv_decompile =
  decompilerLib.decompile_with helperLib.quote_to_strings riscv_tools:
  string -> string frag list -> thm * thm

val riscv_decompile_noC =
  decompilerLib.decompile_with helperLib.quote_to_strings riscv_tools_noC:
  string -> string frag list -> thm * thm

end
