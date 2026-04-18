structure SmlnjHolmake = struct

fun main (_ : string, _ : string list) : OS.Process.status =
    (Holmake.main ()
       handle e => Holmake.die_with ("Holmake failed with exception: " ^
                                     exnMessage e);
     OS.Process.success)

end
