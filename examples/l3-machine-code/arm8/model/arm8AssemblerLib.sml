structure arm8AssemblerLib :> arm8AssemblerLib =
struct

open HolKernel boolLib bossLib
open sptreeSyntax wordsSyntax

local
   open MutableMap arm8 assemblerLib
in
end

val ERR = Feedback.mk_HOL_ERR "arm8AssemblerLib"

(*

val () = sptreeSyntax.temp_add_sptree_printer()
val () = Globals.max_print_depth := 10

*)

(*
   Compute inverse for the function arm8.DecodeBitMasks.
*)

local
   val b0 = BitsN.B (0, 1)
   val b1 = BitsN.B (1, 1)
   type dtype = BitsN.nbit * int * int
   val mkDict =
      List.foldl (fn ((SOME k, d: dtype), m) => Redblackmap.insert (m, k, d)
                   | ((NONE, _), m) => m)
         (Redblackmap.mkDict BitsN.compare) o Lib.mk_set o List.concat
   fun mask (m, n) (s, r) =
      Option.map fst
         (arm8.DecodeBitMasks m
            (BitsN.fromNat (n, 1),
             (BitsN.fromNat (s, 6), (BitsN.fromNat (r, 6), true))))
   val mask32 = mask (32, 0)
   val mask64_0 = mask (64, 0)
   val mask64_1 = mask (64, 1)
   val d64 =
     (List.tabulate
        (64, fn i => List.tabulate (64, fn j => (mask64_1 (i, j), (b1, i, j))))
      @
      List.tabulate
        (62, fn i => List.tabulate (64, fn j => (mask64_0 (i, j), (b0, i, j)))))
     |> mkDict
   val d32 =
     List.tabulate
        (62, fn i => List.tabulate (64, fn j => (mask32 (i, j), (b0, i, j))))
     |> mkDict
   val imm6 =
      Option.map (fn (a, b, c): dtype => (a, (BitsN.B (b, 6), BitsN.B (c, 6))))
   val bits2num = Arbnum.fromHexString o BitsN.toHexString
   val sptree =
      sptreeSyntax.fromAList o
      List.map
         (fn (k, (a, b, c): dtype) =>
            (bits2num k,
             pairSyntax.list_mk_pair
                [wordsSyntax.mk_wordi (bits2num a, 1),
                 wordsSyntax.mk_wordii (b, 6),
                 wordsSyntax.mk_wordii (c, 6)])) o Redblackmap.listItems
   val EncodeBitMask =
      fn arm8.Imm32 i => imm6 (Redblackmap.peek (d32, i))
       | arm8.Imm64 i => imm6 (Redblackmap.peek (d64, i))
in
   fun instructionEncode ast = arm8.Encode (EncodeBitMask, ast)
   val m32 = sptree d32
   val m64 = sptree d64
end

fun arm_syntax_pass1 q =
   let
      open arm8
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
                       OK ast =>
                         (case instructionEncode ast of
                             ARM8 w =>
                                let
                                   val ast' = Decode w
                                in
                                   if ast' = ast
                                      then ok w :: p1
                                   else (addError "Encoding error"; p1)
                                end
                           | BadCode err => (addError err; p1))
                     | PENDING (s, ast) => (pend (s, ast) :: p1)
                     | WORD w => ok w :: p1
                     | FAIL err => (addError err; p1)
            end) [] (assemblerLib.quote_to_strings q)
   in
      if List.null (!errors)
         then (List.rev l, !labelDict)
      else raise assemblerLib.Assembler (List.rev (!errors))
   end

fun encode (line, ast) =
   let
      fun err s = raise assemblerLib.Assembler
                          [{string = "Encode failed" ^ s, line = line}]
   in
      case instructionEncode ast of
         arm8.ARM8 w =>
            let
               val ast' = arm8.Decode w
            in
               if ast' = ast
                  then BitsN.toHexString w
               else err "."
            end
       | _ => err ": not ARM."
   end

fun arm_syntax_pass2 (l, ldict) =
   let
      open arm8
      val err = ERR "arm_syntax_pass2" "unexpected AST"
      val pc = ref 0
   in
      List.map
        (fn mlibUseful.INL (line, (label, ast)) =>
            (case Redblackmap.peek (ldict, label) of
                SOME lpc =>
                 let
                    val offset = BitsN.fromInt (4 * (lpc - !pc), 64)
                 in
                    Portable.inc pc
                  ; encode (line,
                      case ast of
                         LoadStore
                           (LoadLiteral''32 (sz, (memop, (signed, (_, rt))))) =>
                         LoadStore
                           (LoadLiteral''32
                              (sz, (memop, (signed, (offset, rt)))))
                       | LoadStore
                           (LoadLiteral''64 (sz, (memop, (signed, (_, rt))))) =>
                         LoadStore
                           (LoadLiteral''64
                              (sz, (memop, (signed, (offset, rt)))))
                       | Address (page, (_, xd)) => Address (page, (offset, xd))
                       | Branch (BranchConditional (_, cd)) =>
                         Branch (BranchConditional (offset, cd))
                       | Branch (BranchImmediate (_, branch_type)) =>
                         Branch (BranchImmediate (offset, branch_type))
                       | Branch
                           (CompareAndBranch''32 (sz, (iszero, (_, rt)))) =>
                         Branch
                           (CompareAndBranch''32 (sz, (iszero, (offset, rt))))
                       | Branch
                           (CompareAndBranch''64 (sz, (iszero, (_, rt)))) =>
                         Branch
                           (CompareAndBranch''64 (sz, (iszero, (offset, rt))))
                       | Branch
                           (TestBitAndBranch''32
                              (sz, (bit_pos, (bit_val, (_, rt))))) =>
                         Branch
                           (TestBitAndBranch''32
                              (sz, (bit_pos, (bit_val, (offset, rt)))))
                       | Branch
                           (TestBitAndBranch''64
                              (sz, (bit_pos, (bit_val, (_, rt))))) =>
                         Branch
                           (TestBitAndBranch''64
                              (sz, (bit_pos, (bit_val, (offset, rt)))))
                       | _ => raise err)
                 end
              | NONE =>
                 raise assemblerLib.Assembler
                         [{string = "Missing label: " ^ label, line = line}])
          | mlibUseful.INR w => (Portable.inc pc; BitsN.toHexString w)) l
   end

val arm8_code = arm_syntax_pass2 o arm_syntax_pass1

local
   fun code3 s =
      let
         val w = assemblerLib.word 32 s
         val h = StringCvt.padLeft #"0" 8 (L3.lowercase s)
         val (m, a) = arm8.instructionToString (arm8.Decode w)
         val (m, a) =
            if String.isPrefix "??" m then ("WORD", "0x" ^ h) else (m, a)
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
   fun print_arm8_code q =
      List.app printn (codeStrings commentCode (arm8_code q))
      handle Assembler l => ( printn ">> Failed to assemble code."
                            ; printLines l
                            ; printn "<<")
   val arm8_disassemble =
      codeStrings commentHex o List.concat o
      List.map (String.tokens Char.isSpace) o assemblerLib.quote_to_strings
   val print_arm8_disassemble = List.app printn o arm8_disassemble
end

(* Testing

open MutableMap arm8AssemblerLib

local
   val hex = assemblerLib.hex
   fun astEquiv a b =
      a = b orelse
      case (a, b) of
         (arm8.LoadStore (arm8.LoadStoreAcquire''8
               (size, (memop, (acctype, (excl, (_, (_, (_, r)))))))),
          arm8.LoadStore (arm8.LoadStoreAcquire''8
               (size2, (memop2, (acctype2, (excl2, (_, (_, (_, r2))))))))) =>
            size = size2 andalso memop = memop2 andalso
            acctype = acctype2 andalso excl = excl2 andalso r = r2
       | (arm8.LoadStore (arm8.LoadStoreAcquire''16
               (size, (memop, (acctype, (excl, (_, (_, (_, r)))))))),
          arm8.LoadStore (arm8.LoadStoreAcquire''16
               (size2, (memop2, (acctype2, (excl2, (_, (_, (_, r2))))))))) =>
            size = size2 andalso memop = memop2 andalso
            acctype = acctype2 andalso excl = excl2 andalso r = r2
       | (arm8.LoadStore (arm8.LoadStoreAcquire''32
               (size, (memop, (acctype, (excl, (_, (_, (_, r)))))))),
          arm8.LoadStore (arm8.LoadStoreAcquire''32
               (size2, (memop2, (acctype2, (excl2, (_, (_, (_, r2))))))))) =>
            size = size2 andalso memop = memop2 andalso
            acctype = acctype2 andalso excl = excl2 andalso r = r2
       | (arm8.LoadStore (arm8.LoadStoreAcquire''64
               (size, (memop, (acctype, (excl, (_, (_, (_, r)))))))),
          arm8.LoadStore (arm8.LoadStoreAcquire''64
               (size2, (memop2, (acctype2, (excl2, (_, (_, (_, r2))))))))) =>
            size = size2 andalso memop = memop2 andalso
            acctype = acctype2 andalso excl = excl2 andalso r = r2
       | (arm8.LoadStore
            (arm8.LoadStoreAcquirePair''64
               (size, (memop, (acctype, (_, (_, (rs, r))))))),
          arm8.LoadStore
            (arm8.LoadStoreAcquirePair''64
               (size2, (memop2, (acctype2, (_, (_, (rs2, r2)))))))) =>
            size = size2 andalso memop = memop2 andalso acctype = acctype2
            andalso r = r2 andalso (memop <> arm8.MemOp_STORE orelse rs = rs2)
       | (arm8.LoadStore
            (arm8.LoadStoreAcquirePair''128
               (size, (memop, (acctype, (_, (_, (rs, r))))))),
          arm8.LoadStore
            (arm8.LoadStoreAcquirePair''128
               (size2, (memop2, (acctype2, (_, (_, (rs2, r2)))))))) =>
            size = size2 andalso memop = memop2 andalso acctype = acctype2
            andalso r = r2 andalso (memop <> arm8.MemOp_STORE orelse rs = rs2)
       | _ => false
   val gen = Random.newgenseed 1.0
   fun random32 () = BitsN.fromNat (Random.range (0, 0x100000000) gen, 32)
   fun test1 () =
      let
         val w = random32 ()
         val i = arm8.Decode w
         val (m, a) = arm8.instructionToString i
      in
         if String.isPrefix "??" m
            then NONE
         else let
               val s = m ^ " " ^ a
              in
               case arm8.instructionFromString s of
                  arm8.OK i' =>
                    (case arm8AssemblerLib.instructionEncode i' of
                        arm8.ARM8 w' =>
                          if w = w' orelse astEquiv i i'
                             then (* (print (s ^ "\n"); NONE) *) NONE
                          else SOME (hex w, i, s, SOME (hex w', i'))
                      | _ => SOME (hex w, i, s, SOME ("???", i')))
                | _ => SOME (hex w, i, s, NONE)
              end
      end
in
   val examine = ref []
   fun test n =
      let
         val () = examine := []
      in
        Lib.funpow n
          (fn () =>
             case test1 () of
                SOME x => examine := Lib.insert x (!examine)
              | NONE => ()) ()
      end
end

arm8.instructionFromString "mov w26, w12, lsr #0"

fun bin s =
   StringCvt.padLeft #"0" 32
      (BitsN.toBinString (Option.valOf (BitsN.fromHexString (s, 32))))

bin"b8ef4961"
bin"b8af4961"

arm8.diss "d3403e6d"
arm8.diss "53003e6d"

(test 100000; !examine)

*)

end
