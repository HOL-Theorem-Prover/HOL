structure mips_decompLib :> mips_decompLib =
struct

open HolKernel Parse boolLib bossLib
open helperLib set_sepTheory addressTheory progTheory
open pred_setTheory combinTheory
open mips_progLib decompilerLib

val ERR = Feedback.mk_HOL_ERR "mips_decompLib"

(* automation *)

local
   fun format_thm th =
      let
         val c = progSyntax.dest_code (Thm.concl th)
         val n = List.length (pred_setSyntax.strip_set c) * 4
      in
         (th, n,
          stateLib.get_pc_delta
             (Lib.equal "mips_prog$MIPS_PC" o fst o
              boolSyntax.dest_strip_comb) th)
      end
in
   fun format_mips_spec hex =
      case List.map format_thm (mips_progLib.mips_spec_hex2 hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "format_mips_spec" ""
end

val mips_pc = Term.prim_mk_const {Thy = "mips_prog", Name = "MIPS_PC"}

val mips_tools =
   (format_mips_spec, fn _ => fail(), TRUTH, mips_pc): decompiler_tools

local
   fun is_branch h =
      case BitsN.fromHexString (h, 32) of
         SOME opc =>
            (case mips.Decode opc of mips.Branch _ => true | _ => false)
       | NONE => false
in
   fun mips_parse (q: string quotation) =
      let
         fun fill_delay a =
            fn x :: y :: r =>
                 if is_branch x
                    then fill_delay (x ^ " " ^ y :: a) r
                 else fill_delay (x :: a) (y :: r)
             | r => r @ a
      in
         List.rev (fill_delay [] (helperLib.quote_to_strings q))
      end
end

val mips_decompile = decompilerLib.decompile_with mips_parse mips_tools

end
