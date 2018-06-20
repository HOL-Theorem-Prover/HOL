(* -------------------------------------------------------------------------
   Assembly code support for the ARMv7-AR architecture specification
   ------------------------------------------------------------------------- *)

structure armAssemblerLib :> armAssemblerLib =
struct

open HolKernel boolLib bossLib

local
   open arm assemblerLib
in
end

val ERR = Feedback.mk_HOL_ERR "armAssemblerLib"

fun init () =
   let
      open arm
   in
      Architecture := ARMv7_A
    ; Extensions := [Extension_Virtualization]
    ; VFPExtension := VFPv4
    ; CPSR := rec'PSR (Option.valOf (BitsN.fromHexString ("10", 32)))
   end

fun arm_syntax_pass1 q =
   let
      open arm
      val () = init ()
      val pc = ref 0
      val line = ref 0
      val errors = ref ([]: assemblerLib.lines)
      fun addError e = errors := {line = !line, string = e} :: !errors
      val warnings = ref ([]: assemblerLib.lines)
      fun addWarning s = warnings := {line = !line, string = s} :: !warnings
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
      fun pend l = (Portable.inc pc; mlibUseful.INL (!line, l))
      fun ok r = (Portable.inc pc; mlibUseful.INR r)
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
                       OK ((c, ""), ast) =>
                         (case instructionEncode (c, (ast, Enc_ARM)) of
                             ARM w =>
                               (let
                                   val () = SetPassCondition c
                                   val ast' = DecodeARM w
                                in
                                   if ast' = ast
                                      then ok w :: p1
                                   else (addError "Encoding error"; p1)
                                end
                                handle UNPREDICTABLE _ =>
                                  ( addWarning s1; ok w :: p1 ))
                           | BadCode err => (addError err; p1)
                           | _ => (addError "Encoding error"; p1))
                     | OK ((_, x), _) =>
                         (addError ("Instruction has ." ^ x ^ " suffix"); p1)
                     | PENDING (s, ((c, ""), ast)) =>
                         (pend (s, c, ast) :: p1)
                     | PENDING (_, ((_, x), _)) =>
                         (addError ("Instruction has ." ^ x ^ " suffix"); p1)
                     | WORD w => ok w :: p1
                     | FAIL err => (addError err; p1)
            end) [] (assemblerLib.quote_to_strings q)
   in
      if List.null (!errors)
         then (List.rev l, !labelDict, List.rev (!warnings))
      else raise assemblerLib.Assembler
              (List.rev (!errors) @
               List.map (fn {string, line} =>
                            {string = "Unpredictable: " ^ string,
                             line = line}) (List.rev (!warnings)))
   end

fun encode (line, c, ast) =
   let
      fun err s = raise assemblerLib.Assembler
                          [{string = "Encode failed" ^ s, line = line}]
   in
      case arm.instructionEncode (c, (ast, arm.Enc_ARM)) of
         arm.ARM w =>
           (let
               val () = arm.SetPassCondition c
               val ast' = arm.DecodeARM w
            in
               if ast' = ast
                  then BitsN.toHexString w
               else err "."
            end
            handle arm.UNPREDICTABLE _ => err ": UNPREDICTABLE.")
       | _ => err ": not ARM."
   end

fun arm_syntax_pass2 ldict l =
   let
      open arm
      val err = ERR "arm_syntax_pass2" "unexpected AST"
      val r15 = BitsN.fromNat (15, 4)
      fun check15 x ast = if x = r15 then ast else raise err
      val pc = ref 0
   in
      List.map
        (fn mlibUseful.INL (line, (label, cond, ast)) =>
            (case Redblackmap.peek (ldict, label) of
                SOME lpc =>
                 let
                    val offset = BitsN.fromNativeInt (4 * (lpc - !pc - 2), 32)
                    val (add, uoffset) =
                       if !pc + 2 <= lpc
                           then (true, offset)
                       else (false,
                             BitsN.fromNativeInt (4 * (!pc + 2 - lpc), 32))
                 in
                    Portable.inc pc
                  ; encode (line, cond,
                      case ast of
                         Branch
                           (BranchLinkExchangeImmediate (iset, _)) =>
                           Branch (BranchLinkExchangeImmediate (iset, offset))
                       | Branch (BranchTarget (_)) =>
                           Branch (BranchTarget offset)
                       | Data (ArithLogicImmediate (_, (false, (d, (x, _))))) =>
                           check15 x
                            (case arm.EncodeARMImmediate uoffset of
                                SOME imm12 =>
                                  Data (ArithLogicImmediate
                                     (BitsN.fromInt (if add then 4 else 2, 4),
                                      (false, (d, (x, imm12)))))
                              | NONE =>
                                  raise assemblerLib.Assembler
                                    [{string =
                                       "Label address not encodable: " ^ label,
                                      line = line}])
                       | Load (LoadLiteral (_, (t, _))) =>
                           Load (LoadLiteral (add, (t, uoffset)))
                       | Load (LoadByteLiteral (u, (_, (t, _)))) =>
                           Load (LoadByteLiteral (u, (add, (t, uoffset))))
                       | Load (LoadHalfLiteral (u, (_, (t, _)))) =>
                           Load (LoadHalfLiteral (u, (add, (t, uoffset))))
                       | Load (LoadDualLiteral (_, (t1, (t2, _)))) =>
                           Load (LoadDualLiteral (add, (t1, (t2, uoffset))))
                       | Store
                           (StoreWord
                              (_,
                                (true,
                                  (false, (t, (x, immediate_form1 _)))))) =>
                           check15 x
                              (Store (StoreWord (add, (true, (false, (t,
                                        (x, immediate_form1 uoffset)))))))
                       | Store
                           (StoreByte
                              (_,
                                (true,
                                  (false, (t, (x, immediate_form1 _)))))) =>
                           check15 x
                              (Store (StoreByte (add, (true, (false, (t,
                                        (x, immediate_form1 uoffset)))))))
                       | Store
                           (StoreHalf
                              (_,
                                (true,
                                  (false, (t, (x, immediate_form1 _)))))) =>
                           check15 x
                              (Store (StoreHalf (add, (true, (false, (t,
                                        (x, immediate_form1 uoffset)))))))
                       | Store
                           (StoreDual
                              (_,
                                (true,
                                  (false,
                                    (t1, (t2, (x, immediate_form2 _))))))) =>
                           check15 x
                              (Store (StoreDual (add, (true, (false, (t1, (t2,
                                        (x, immediate_form2 uoffset))))))))
                       | VFP (vldr (s, (_, (d, (x, _))))) =>
                           check15 x (VFP (vldr (s, (add, (d, (x, uoffset))))))
                       | VFP (vstr (s, (_, (d, (x, _))))) =>
                           check15 x (VFP (vstr (s, (add, (d, (x, uoffset))))))
                       | _ => raise err)
                 end
              | NONE =>
                 raise assemblerLib.Assembler
                         [{string = "Missing label: " ^ label, line = line}])
          | mlibUseful.INR w => (Portable.inc pc; BitsN.toHexString w)) l
   end

fun arm_code_with_warnings q =
   let
      val (l, ldict, wrns) = arm_syntax_pass1 q
   in
      (arm_syntax_pass2 ldict l, wrns)
   end

fun arm_code q =
   let
      val (code, warnings) = arm_code_with_warnings q
   in
      if List.null warnings
         then code
      else raise assemblerLib.Assembler warnings
   end

local
   fun code3 s =
      let
         val w = assemblerLib.word 32 s
         val c = BitsN.bits (31, 28) w
         val () = (init(); arm.SetPassCondition c)
         val h = StringCvt.padLeft #"0" 8 (L3.lowercase s)
         val (m, a) = arm.instructionToString (c, arm.DecodeARM w)
                      handle arm.UNPREDICTABLE _ => ("WORD", h)
      in
         (h, m, a)
      end
      handle Option => raise ERR "" ("could not decode: " ^ s)
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
                    val c as (_, m, a) = code3 s
                 in
                    mm := Int.max (!mm, String.size m)
                  ; ma := Int.max (!ma, String.size a)
                  ; iter (c :: acc) r
                 end
      in
         List.rev (iter [] l): string list
      end
   open assemblerLib
in
   fun print_arm_code q =
      let
         val (code, wrns) = arm_code_with_warnings q
         val code = codeStrings commentCode code
      in
         if List.null wrns
            then ()
         else ( printn ">> Warning: UNPREDICTABLE code."
              ; printLines wrns
              ; printn "<<"
              )
       ; List.app printn code
      end
      handle Assembler l => ( printn ">> Failed to assemble code."
                            ; printLines l
                            ; printn "<<")
   val arm_disassemble =
      codeStrings commentHex o List.concat o
      List.map (String.tokens Char.isSpace) o assemblerLib.quote_to_strings
   val print_arm_disassemble = List.app printn o arm_disassemble
end

end (* structure armParse *)

(* Testing

open armAssemblerLib

val () = print_arm_code
  `b -#12
   b -#8
   b -#4
   b -#0
   b +#0
   b +#4
   b +#8
   b +#12
   `

val () = print_arm_code
  `label:
   adr r1, label2
   adr r1, -#12
   adr r1, -#8
   adr r1, -#4
   adr r1, -#0
   adr r1, +#0
   adr r1, +#4
   adr r1, +#8
   adr r1, +#12
   label2:
   adr r1, label`

val () = print_arm_code
  `ldmdbeq r1!, {r3-r6}
   add r1, r2, r3, lsl r4
  `

local
   val hex = assemblerLib.hex
   fun immEquiv x y = arm.ExpandImm_C (x, false) = arm.ExpandImm_C (y, false)
   fun astEquiv a b =
      a = b orelse
      case (a, b) of
         (arm.Data (arm.Move (setflags, (negate, (d, imm12a)))),
          arm.Data (arm.Move (_, (_, (_, imm12b))))) =>
           b = arm.Data (arm.Move (setflags, (negate, (d, imm12b)))) andalso
           immEquiv imm12a imm12b
       | (arm.Data (arm.TestCompareImmediate (opc, (n, imm12a))),
          arm.Data (arm.TestCompareImmediate (_, (_, imm12b)))) =>
           b = arm.Data (arm.TestCompareImmediate (opc, (n, imm12b))) andalso
           immEquiv imm12a imm12b
       | (arm.Data
            (arm.ArithLogicImmediate (opc, (setflags, (d, (n, imm12a))))),
          arm.Data (arm.ArithLogicImmediate (_, (_, (_, (_, imm12b)))))) =>
           b = arm.Data
                 (arm.ArithLogicImmediate (opc, (setflags, (d, (n, imm12b)))))
           andalso immEquiv imm12a imm12b
       | (arm.Data (arm.RegisterShiftedRegister
                      (opc, (setflags, (d, (n, (m, (shift_t, s))))))),
          arm.Data (arm.RegisterShiftedRegister
                      (opc', (setflags', (d', (n', (m', (shift_t', s')))))))) =>
            opc = opc' andalso setflags = setflags' andalso
            (BitsN.bits (3, 2) opc = BitsN.fromNat (2, 2) orelse d = d')
            andalso n = n' andalso m = m' andalso shift_t = shift_t' andalso
            s = s'
       | _ => false
   val gen = Random.newgenseed 1.0
   fun random32 () = BitsN.fromNat (Random.range (0, 0x100000000) gen, 32)
   fun test1 () =
      let
         val w = random32 ()
         val c = BitsN.bits (31, 28) w
         val i = arm.DecodeARM w
         val (m, a) = arm.instructionToString (c, i)
         val c = if c = BitsN.fromNat (15, 4) then BitsN.fromNat (14, 4) else c
         val s = m ^ " " ^ a
      in
         if String.isPrefix "nop" m orelse String.isPrefix "udf" m orelse
            m = "isb" andalso a <> "sy"
            then NONE
         else
            case arm.instructionFromString s of
               arm.OK ((_, ""),
               arm.Branch
                 (arm.BranchLinkExchangeImmediate (arm.InstrSet_ARM, _))) =>
                  NONE
             | arm.OK ((c', ""), i') =>
                 (case arm.instructionEncode (c', (i', arm.Enc_ARM)) of
                     arm.ARM w' =>
                       if w = w' orelse c = c' andalso astEquiv i i'
                          then (* (print (s ^ "\n"); NONE) *) NONE
                       else SOME (hex w, i, s, SOME (hex w', i'))
                   | _ => SOME (hex w, i, s, SOME ("???", i')))
             | _ => SOME (hex w, i, s, NONE)
      end
      handle arm.UNPREDICTABLE _ => NONE
in
   val examine = ref []
   fun test n =
      ( init ()
      ; examine := []
      ; Lib.funpow n
          (fn () =>
             case test1 () of
                SOME x => examine := Lib.insert x (!examine)
              | NONE => ()) ()
      )
end

(test 100000; !examine)

*)
