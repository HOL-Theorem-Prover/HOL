(* -------------------------------------------------------------------------
   Support for assembly code parsing and pretty-printing
   ------------------------------------------------------------------------- *)

structure assemblerLib :> assemblerLib =
struct

open HolKernel boolLib bossLib

local
  open IntExtra Nat Set L3 Bitstring BitsN FP32 FP64 FPConvert
in
end

(* Turns a quote `...` into a list of strings, removing comments *)
local
   val compressNewlines =
      Substring.full o Substring.translate (fn #"\n" => "\n" | _ => "")
   fun strip_comments (d, a) s =
      if Substring.size s = 0
         then a
      else let
              val (l, r) =
                 Substring.splitl (fn c => c <> #"(" andalso c <> #"*") s
              val a' = a @ [if 0 < d then compressNewlines l else l]
           in
              if Substring.isPrefix "(*" r
                 then strip_comments (d + 1, a') (Substring.triml 2 r)
              else if Substring.isPrefix "*)" r
                 then strip_comments (d - 1, a') (Substring.triml 2 r)
              else if Substring.size r = 0
                 then a'
              else let
                      val (r1, r2) = Substring.splitAt (r, 1)
                   in
                      strip_comments (d, if 0 < d then a' else a' @ [r1]) r2
                   end
           end
   val lines = String.fields (fn c => c = #"\n") o Substring.concat o
               strip_comments (0, []) o Substring.full
in
   val quote_to_strings = fn [QUOTE s] => lines s | _ => raise General.Bind
end

type lines = {string : string, line : int} list

exception Assembler of lines

fun printn s = print (s ^ "\n")

val printLines: lines -> unit =
   List.app (fn {string, line} =>
               printn ("line " ^ Int.toString line ^ " : " ^ string))

fun dropLastChar "" = ""
  | dropLastChar s = String.substring (s, 0, String.size s - 1)

fun hex w = StringCvt.padLeft #"0" (Nat.toNativeInt (BitsN.size w) div 4)
              (L3.lowercase (BitsN.toHexString w))

fun word n s = Option.valOf (BitsN.fromHexString (s, Nat.fromNativeInt n))

end
