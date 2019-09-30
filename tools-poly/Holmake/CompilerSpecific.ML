structure CompilerSpecific :>
  sig
    val quietbind : string -> unit
  end
= struct

fun reader s =
    let
      val i = ref 0
      val sz = String.size s
      fun r () = if !i < sz then SOME (String.sub(s,!i)) before i := !i + 1
                 else NONE
    in
      r
    end

fun quietbind s =
    let open PolyML.Compiler
    in
      PolyML.compiler (reader s, [CPOutStream (fn _ => ())]) ()
    end

end
