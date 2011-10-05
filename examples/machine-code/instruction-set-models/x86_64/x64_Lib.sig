signature x64_Lib =
sig
    include Abbrev

    val x64_decode          : string -> thm
    val x64_step            : string -> thm

    val x64_test            : string -> (string * string * string) list -> unit

end
