(* -------------------------------------------------------------------------
   Assembly code support for the x86-64 architecture specification
   ------------------------------------------------------------------------- *)

structure x64AssemblerLib :> x64AssemblerLib =
struct

open HolKernel boolLib bossLib

local
   open MutableMap x64 assemblerLib
in
end

val ERR = Feedback.mk_HOL_ERR "x64AssemblerLib"

fun jcc_width (c, i) =
   if i = BitsN.zero 64 then 2 else if c = x64.Z_ALWAYS then 5 else 6

fun x64_syntax_pass1 q =
   let
      open x64
      val pc = ref 0
      val line = ref 0
      val errors = ref ([]: assemblerLib.lines)
      fun addError e = errors := {line = !line, string = e} :: !errors
      val labelDict =
        ref (Redblackmap.mkDict String.compare : (string, int) Redblackmap.dict)
      fun addLabel s =
         case p_label (L3.lowercase s) of
            SOME l =>
              labelDict := Redblackmap.update
                             (!labelDict, l,
                              fn NONE => !pc
                               | SOME otherpc =>
                                   ( addError ("Duplicate label: " ^ l)
                                   ; otherpc ))
          | NONE => addError ("Bad label: " ^ stripSpaces s)
      fun incpc w = pc := !pc + w
      fun pend w l = (incpc w; mlibUseful.INL (!line, l))
      fun ok l = (incpc (List.length l); mlibUseful.INR l)
      val l =
        List.foldl
          (fn (s, p1) =>
            let
               val () = Portable.inc line
               val (s1, _) = L3.splitl (fn c => c <> #";", s)
               val (l1, s1) = L3.splitr (fn c => c <> #":", s1)
               val () = if l1 = "" then ()
                        else addLabel (assemblerLib.dropLastChar l1)
               val s1 = stripSpaces s1
            in
               if s1 = ""
                  then p1
               else case instructionFromString s1 of
                       OK ast =>
                         (case encode ast of
                             [] => (addError "failed to encode"; p1)
                           | l => ok l :: p1)
                     | PENDING (s, ast as Zloop _) => pend 2 (s, ast) :: p1
                     | PENDING (s, ast as Zcall _) => pend 5 (s, ast) :: p1
                     | PENDING (s, ast as Zjcc c_i) =>
                         pend (jcc_width c_i) (s, ast) :: p1
                     | PENDING _ => (addError "unexpected pend"; p1)
                     | STREAM l => ok l :: p1
                     | FAIL err => (addError err; p1)
            end) [] (assemblerLib.quote_to_strings q)
   in
      if List.null (!errors)
         then (List.rev l, !labelDict)
      else raise assemblerLib.Assembler (List.rev (!errors))
   end

local
   open x64
   fun w64 i = BitsN.fromInt (i, 64)
   fun sub i = fn j => BitsN.- (j, w64 i)
   val s2 = sub 2
   val s5 = sub 5
   fun err line s =
      raise assemblerLib.Assembler [{string = "encode failed" ^ s, line = line}]
   fun encode_pending (line, pc, ast, i) =
      let
         val (w, l) =
            case ast of
               Zloop (c, _) => (2, encode (Zloop (c, s2 i)))
             | Zcall (Zimm _) => (5, encode (Zcall (Zimm (s5 i))))
             | Zjcc (c, imm) =>
                  let
                     val w = jcc_width (c, imm)
                  in
                     (w, if w = 2 then encode (Zjcc (c, s2 i))
                         else e_jcc_rel32 (Zjcc (c, sub w i)))
                  end
             | _ => raise ERR "encode_pending" "unexpected AST"
         val n = List.length l
      in
         if n = w
            then ()
         else err line (if List.null l then ""
                        else ": got " ^ Int.toString n ^ " bytes, expecting " ^
                             Int.toString w)
       ; pc := !pc + w
       ; writeBytes l
      end
in
   fun x64_syntax_pass2 (l, ldict) =
      let
         val pc = ref 0
      in
         List.map
           (fn mlibUseful.INL (line, (label, ast)) =>
               (case Redblackmap.peek (ldict, label) of
                   SOME lpc => encode_pending (line, pc, ast, w64 (lpc - !pc))
                 | NONE =>
                     raise assemblerLib.Assembler
                              [{string = "Missing label: " ^ label,
                                line = line}])
             | mlibUseful.INR b => (pc := !pc + List.length b; writeBytes b)) l
      end
end

val x64_code = x64_syntax_pass2 o x64_syntax_pass1

val removeWhitespace =
   String.translate (fn c => if Char.isSpace c then "" else String.str c)

val x64_code_no_spaces = List.map removeWhitespace o x64_code

local
   val err = ERR "opcodeToBytes" ""
   fun iter a =
      fn h1 :: h2 :: r =>
        (case IntExtra.fromHexString (String.implode [h1, h2]) of
            SOME i => iter (BitsN.fromNat (i, 8) :: a) r
          | NONE => raise err)
       | [] => List.rev a
       | _ => raise err
   fun opcodeToBytes s =
      let
         val s = x64.stripSpaces s
         val t = if String.isPrefix "0x" s
                    then String.extract (s, 2, NONE)
                 else s
      in
          SOME (iter [] (String.explode t))
          handle HOL_ERR {origin_function = "opcodeToBytes", ...} =>
             x64.p_bytes s
      end
   fun bytes [] = "encoding error"
     | bytes l = L3.lowercase (x64.writeBytes l)
   fun enc s =
      case x64.instructionFromString s of x64.OK ast => x64.encode ast | _ => []
   fun check false _ _ = NONE
     | check true l s =
         let val l2 = enc s in if l = l2 then NONE else SOME (bytes l2) end
in
   fun decodeToAssembly c s =
      case opcodeToBytes s of
         SOME [] => ("", NONE)
       | SOME l =>
           let
              val bs = bytes l
           in
              case x64.x64_decode l of
                 x64.Zfull_inst (_, (ast, [])) =>
                    let
                       val s = x64.joinString
                                 (x64.instructionToString (ast, List.length l))
                    in
                       (s, SOME (bs, check c l s))
                    end
               |  _ => ("bytes " ^ bs, NONE)
           end
       | NONE => raise ERR "decodeToAssembly" "failed to parse bytes"
end

val x64_disassemble =
   List.mapPartial (fn s => case decodeToAssembly true s of
                               ("", NONE) => NONE
                             | (v, _) => SOME v) o
   assemblerLib.quote_to_strings

val pad = StringCvt.padRight #" "

fun printFormatted (f, c, p) ll =
   let
      val pr = if p then pad else Lib.K Lib.I
      val l = ref 0
      val r = ref 0
      fun update_m (x, y) =
         ( l := Int.max (!l, String.size x)
         ; r := Int.max (!r, String.size (Option.getOpt (y, "")))
         ; (x, y)
         )
      val ll = List.map (update_m o f) ll
   in
      Portable.inc l
    ; Portable.inc r
    ; List.app
        (fn (a, b) =>
           let
              val x =
                 pad (!l) a ^ (case b of SOME s => c (pr (!r) s) | NONE => "")
           in
              if x64.stripSpaces x = "" then () else assemblerLib.printn x
           end) ll
   end

val print_x64_disassemble =
   printFormatted
      (fn s => case decodeToAssembly true s of
                  (a, SOME (b, NONE)) => (a, SOME b)
                | (a, SOME (b, SOME c)) => (a, SOME (b ^ " -> " ^ c))
                | (a, NONE) => (a, NONE),
       fn s => " ; " ^ s,
       false) o
   assemblerLib.quote_to_strings

val print_x64_code =
   printFormatted
      (fn s => case decodeToAssembly false s of
                  (s, NONE) => (String.extract (s, 6, NONE), NONE)
                | (s, SOME (l, NONE)) => (l, SOME s)
                | _ => raise ERR "print_x64_code" "mismatch",
       fn s => " (*  " ^ s ^ " *)",
       true) o
   x64_code

(*

val dec = x64.x64_decode o Option.valOf o x64.p_bytes

open x64AssemblerLib

x64_disassemble
   `acde
    90
    0f8507000000
    eb05
    e900000000
    90`

print_x64_code
   `add al, 255
    add eax, 127
    add eax, 255
    add eax, 256
    add rax, 127
    add rax, 255
    add rax, 256
   `

print_x64_code
   `bytes ac ac
    cpuid
    nop
    mov rax, rbx
    cmpxchg [rax+rbx*8+1000], rcx`

*)

end
