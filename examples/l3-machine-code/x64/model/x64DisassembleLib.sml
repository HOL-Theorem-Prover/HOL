(* -------------------------------------------------------------------------
   Disassembly support for the x86-64 architecture specification
   ------------------------------------------------------------------------- *)

structure x64DisassembleLib :> x64DisassembleLib =
struct

open HolKernel boolLib bossLib wordsSyntax

local
   open MutableMap x64
in
end

local
   val s_byte = L3.lowercase o x64.s_byte
   fun decodeStream a =
      fn [] => List.rev a
       | l =>
          let
             val (h, t) = if List.length l <= 20
                             then (l, [])
                          else (List.take (l, 20), List.drop (l, 20))
          in
              case x64.x64_decode h of
                 x64.Zfull_inst (_, (ast, rest)) =>
                    let
                       val w = List.length h - List.length rest
                       val s = x64.joinString (x64.instructionToString (ast, w))
                       val used =
                          List.take (h, List.length h - List.length rest)
                       val b = String.concat
                                 (Lib.separate " " (List.map s_byte used))
                    in
                       decodeStream ((b, s) :: a) (rest @ t)
                    end
               | _ => decodeStream ((s_byte (hd l), "") :: a) (tl l)
          end
   val decodeStream = decodeStream []
   val err = ERR "x64_disassemble_byte_list" "not a byte list"
   val w8 = wordsSyntax.mk_int_word_type 8
   fun toByte b = BitsN.fromNat (wordsSyntax.uint_of_word b, 8)
in
   fun x64_disassemble tm =
      case Lib.total listSyntax.dest_list tm of
         SOME (l, ty) => if ty <> w8 then raise err
                         else decodeStream (List.map toByte l)
       | NONE => raise err
end

end
