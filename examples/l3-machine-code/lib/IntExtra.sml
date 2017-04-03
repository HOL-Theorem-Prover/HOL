(* -------------------------------------------------------------------------
   Extra Int functions
   ------------------------------------------------------------------------- *)

structure IntExtra :> IntExtra =
struct
   val toBinString = IntInf.fmt StringCvt.BIN
   val toHexString = IntInf.fmt StringCvt.HEX

   val fromBool = fn true => 1 | false => 0: IntInf.int

   local
      fun scanInt b s =
         case IntInf.scan b Substring.getc (Substring.full s) of
           SOME (i, r) => if Substring.size r = 0 then SOME i else NONE
         | _ => NONE
   in
      val fromString = scanInt StringCvt.DEC
      val fromBinString = scanInt StringCvt.BIN
      val fromHexString = scanInt StringCvt.HEX

      fun fromLit s =
         let
            val v = String.extract (s, 1, NONE)
         in
            case String.sub (s, 0) of
              #"d" => fromString v
            | #"?" => fromString v
            | #"b" => fromBinString v
            | #"x" => fromHexString v
            | _ => NONE
         end
   end
end (* structure IntExtra *)
