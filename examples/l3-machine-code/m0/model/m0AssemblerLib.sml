(* -------------------------------------------------------------------------
   Assembly code support for the ARMv6-M architecture specification
   ------------------------------------------------------------------------- *)

structure m0AssemblerLib :> m0AssemblerLib =
struct

open HolKernel boolLib bossLib

local
   open m0
in end

val ERR = Feedback.mk_HOL_ERR "m0AssemblerLib"

val hex = assemblerLib.hex
fun hex32 w = hex (BitsN.bits (31, 16) w) ^ " " ^ hex (BitsN.bits (15, 0) w)
val w16 = assemblerLib.word 16

fun isBranchLink (m0.Branch (m0.BranchLinkImmediate _)) = true
  | isBranchLink _ = false

fun m0_syntax_pass1 q =
   let
      open m0
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
      fun encoding e =
         case e of
            "w" => Enc_Wide
          | "n" => Enc_Narrow
          | "" => Enc_Thumb
          | x => (addError ( "Instruction has ." ^ x ^ " suffix"); Enc_Thumb)
      fun incpc e =
         (Portable.inc pc; if e = Enc_Wide then Portable.inc pc else ())
      fun pend e l = (incpc e; mlibUseful.INL (!line, l))
      fun ok e r = (incpc e; mlibUseful.INR r)
      fun wide e =
         ( if e = Enc_Narrow
             then addError "narrow branch link not available"
           else ()
         ; Enc_Wide
         )
      fun narrow e =
         ( if e = Enc_Wide
             then addError "wide version not available"
           else ()
         ; Enc_Narrow
         )
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
                       OK ((c, e), ast) =>
                        ((case Encode (c, (ast, encoding e)) of
                             Thumb16 w => ok Enc_Narrow w :: p1
                           | Thumb32 (w1, w2) =>
                               ok Enc_Wide (BitsN.@@ (w1, w2)) :: p1
                           | BadCode err => (addError err; p1))
                         handle UNPREDICTABLE _ =>
                                  (addError "UNPREDICTABLE"; p1))
                     | PENDING (s, ((c, e), ast)) =>
                         let
                            val enc0 = encoding e
                            val enc = if isBranchLink ast
                                         then wide enc0
                                      else narrow enc0
                         in
                            pend enc (s, c, enc, ast) :: p1
                         end
                     | HALFWORD w => ok Enc_Narrow w :: p1
                     | FAIL err => (addError err; p1)
            end) [] (assemblerLib.quote_to_strings q)
   in
      if List.null (!errors)
         then (List.rev l, !labelDict)
      else raise assemblerLib.Assembler (List.rev (!errors))
   end

fun encode (line, pc, c, enc, ast) =
   let
      fun err s = raise assemblerLib.Assembler
                          [{string = "Encode failed" ^ s, line = line}]
   in
     (case m0.Encode (c, (ast, enc)) of
         m0.Thumb16 w => (Portable.inc pc; hex w)
       | m0.Thumb32 (w1, w2) =>
           (Portable.inc pc; Portable.inc pc; hex w1 ^ " " ^ hex w2)
       | m0.BadCode e => err e)
     handle m0.UNPREDICTABLE _ => err ": UNPREDICTABLE."
   end

fun offErr (label, line) =
   raise assemblerLib.Assembler
     [{string = "bad reference to: " ^ label, line = line}]

fun m0_syntax_pass2 (l, ldict) =
   let
      open m0
      val err = ERR "m0_syntax_pass2" "unexpected AST"
      val r15 = BitsN.fromNat (15, 4)
      fun check (add, label, line) x ast =
         if x = r15
            then if add then ast else offErr (label, line)
         else raise err
      val pc = ref 0
   in
      List.map
        (fn mlibUseful.INL (line, (label, cond, enc, ast)) =>
            (case Redblackmap.peek (ldict, label) of
                SOME lpc =>
                 let
                    val offset = BitsN.fromNativeInt (2 * (lpc - !pc - 2), 32)
                    val chk = check (!pc + 1 <= lpc, label, line)
                 in
                    encode (line, pc, cond, enc,
                      case ast of
                         Branch (BranchLinkImmediate _) =>
                           Branch (BranchLinkImmediate (offset))
                       | Branch (BranchTarget (_)) =>
                           Branch (BranchTarget offset)
                       | Data (ArithLogicImmediate (_, (false, (d, (x, _))))) =>
                          chk x
                            (Data (ArithLogicImmediate
                                     (BitsN.fromInt (4, 4),
                                        (false, (d, (x, offset))))))
                       | Load (LoadLiteral (t, _)) =>
                           chk r15 (Load (LoadLiteral (t, offset)))
                       | Load (LoadByte (u, (t, (x, _)))) =>
                           chk x
                             (Load (LoadByte
                                      (u, (t, (x, immediate_form offset)))))
                       | Load (LoadHalf (u, (t, (x, _)))) =>
                           chk x
                              (Load (LoadHalf
                                      (u, (t, (x, immediate_form offset)))))
                       | Store (StoreWord (t, (x, immediate_form _))) =>
                           chk x
                             (Store (StoreWord (t, (x, immediate_form offset))))
                       | Store (StoreByte (t, (x, immediate_form offset))) =>
                           chk x
                             (Store (StoreByte (t, (x, immediate_form offset))))
                       | Store (StoreHalf (t, (x, immediate_form _))) =>
                           chk x
                             (Store (StoreHalf (t, (x, immediate_form offset))))
                       | _ => raise err)
                 end
              | NONE =>
                  raise assemblerLib.Assembler
                           [{string = "Missing label: " ^ label, line = line}])
          | mlibUseful.INR w =>
              ( Portable.inc pc
              ; if BitsN.size w = 32
                   then (Portable.inc pc; hex32 w)
                else hex w
              )) l
   end

fun m0_code q = m0_syntax_pass2 (m0_syntax_pass1 q)

local
   val al = BitsN.fromNat (14, 4)
   val mask = BitsN.fromNat (0xD000, 16)
   fun canEncodeAsThumb ast = (* should just pick up UDF.W *)
      (case m0.Encode (al, (ast, m0.Enc_Narrow)) of
          m0.Thumb16 _ => true
        | _ => false) handle m0.UNPREDICTABLE _ => true
   fun pad16 s = StringCvt.padLeft #"0" 4 (L3.lowercase s)
in
   fun thumbCondition opc =
      if BitsN.toNat (BitsN.bits (15, 12) opc) = 13
         then let
                 val code = BitsN.bits (11, 8) opc
              in
                 m0.SetPassCondition code
               ; code
              end
      else al
   fun decode s =
      case String.tokens Char.isSpace s of
         [w] => let
                   val opc = w16 w
                   val c = thumbCondition opc (* has side-effect *)
                   val ast = m0.Decode (m0.Thumb opc)
                   val (m, a) = m0.instructionToString (c, ast)
                in
                   ("     " ^ pad16 w, m, a)
                end
       | [w1, w2] =>
                let
                   val opc = (w16 w1, w16 w2)
                   val ast = m0.Decode (m0.Thumb2 opc)
                   val w = if canEncodeAsThumb ast then ".w" else ""
                   val (m, a) = m0.instructionToString (al, ast)
                in
                   (pad16 w1 ^ " " ^ pad16 w2, m ^ w, a)
                end
       | _ => raise ERR "decode" "bad string"
end

fun commentCode (mm, ma) =
   fn (c, m, a) =>
       c ^ "  (*  " ^ StringCvt.padRight #" " mm m ^
       StringCvt.padRight #" " ma a ^ "*)"

fun commentHex (mm, ma) =
   fn (c, m, a) =>
       StringCvt.padRight #" " mm m ^
       StringCvt.padRight #" " ma a ^ "; " ^ c

fun codeStrings f l =
   let
      val mm = ref 0
      val ma = ref 0
      fun iter acc =
         fn [] => List.map (f (!mm + 1, !ma + 2)) acc
          | s :: r =>
              let
                 val c as (_, m, a) = decode s
              in
                 mm := Int.max (!mm, String.size m)
               ; ma := Int.max (!ma, String.size a)
               ; iter (c :: acc) r
              end
   in
      List.rev (iter [] l): string list
   end

local
   open assemblerLib
in
   fun print_m0_code q =
      List.app printn (codeStrings commentCode (m0_code q))
      handle Assembler l =>
               ( printn ">> Failed to assemble code."
               ; printLines l
               ; printn "<<")
end

val m0_disassemble = codeStrings commentHex o assemblerLib.quote_to_strings

val print_m0_disassemble = List.app assemblerLib.printn o m0_disassemble

end (* structure m0Parse *)

(* Testing

open m0AssemblerLib

print_m0_code`
  b -#2
  b -#0
  b +#0
  b +#2
  b +#4
  `

print_m0_code`
  adr r1, +#4
  adr r1, +#8
  adr r1, +#12
  `

print_m0_code`
  ldr r1, +#4
  ldr r1, +#8
  ldr r1, +#12
  `

print_m0_code
  `    adr r1, label
       nop
       nop
       nop
label: nop`

print_m0_code
  `label: nop
   b label
   b label
   bl label
   bl label
   label2: b label2`

print_m0_code
  `b.n label
   adr r1, label
   nop
   nop
   nop
   add.n r1, r2
   movs r0, r0
   bl.w label
   label: muls r2, r3`;

local
   open assemblerLib
   val al = BitsN.fromNat (14, 4)
   fun astEquiv a b = a = b
   val gen = Random.newgenseed 1.0
   fun random16 () = BitsN.fromNat (Random.range (0, 0x10000) gen, 16)
   fun test1 () =
      let
         val w = random16 ()
         val c = thumbCondition w
         val i = m0.DecodeThumb w
         val (m, a) = m0.instructionToString (c, i)
         val s = m ^ " " ^ a
      in
         if String.isPrefix "nop" m orelse String.isPrefix "udf" m
            then NONE
         else
            case m0.instructionFromString s of
               m0.OK ((c', ""), i') =>
                 (case m0.instructionEncode (c', (i', m0.Enc_Narrow)) of
                     m0.Thumb16 w' =>
                       if w = w' orelse c = c' andalso astEquiv i i'
                          then (* (print (s ^ "\n"); NONE) *) NONE
                       else SOME (hex w, i, s, SOME (hex w', i'))
                   | _ => SOME (hex w, i, s, SOME ("???", i')))
             | _ => SOME (hex w, i, s, NONE)
      end
      handle m0.UNPREDICTABLE _ => NONE
   fun test2 () =
      let
         val opc as (w1, w2) =
            (BitsN.|| (BitsN.fromNat (0xF000, 16), random16 ()), random16 ())
         val i = m0.DecodeThumb2 opc
         val (m, a) = m0.instructionToString (al, i)
         val s = m ^ " " ^ a
      in
         if String.isPrefix "udf" m orelse m = "isb" andalso a <> "sy"
            then NONE
         else
            case m0.instructionFromString s of
               m0.OK ((c', _), i') =>
                 (case m0.instructionEncode (c', (i', m0.Enc_Wide)) of
                     m0.Thumb32 (opc' as (w1', w2')) =>
                       if opc = opc' orelse al = c' andalso astEquiv i i'
                          then (* (print (s ^ "\n"); NONE) *) NONE
                       else SOME (hex w1, hex w2, i, s,
                                  SOME (hex w1', hex w2', i'))
                   | _ => SOME (hex w1, hex w2, i, s,
                                SOME ("???", "???", i')))
             | _ => SOME (hex w1, hex w2, i, s, NONE)
      end
      handle m0.UNPREDICTABLE _ => NONE
in
   val examine16 = ref []
   val examine32 = ref []
   fun test16 n =
      let
         val () = examine16 := []
      in
        Lib.funpow n
          (fn () =>
             case test1 () of
                SOME x => examine16 := Lib.insert x (!examine16)
              | NONE => ()) ()
      end
   fun test32 n =
      let
         val () = examine32 := []
      in
        Lib.funpow n
          (fn () =>
             case test2 () of
                SOME x => examine32 := Lib.insert x (!examine32)
              | NONE => ()) ()
      end
end

(test16 1000000; !examine16)
(test32 1000000; !examine32)


*)
