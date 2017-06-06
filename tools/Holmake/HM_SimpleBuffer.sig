signature HM_SimpleBuffer =
sig

  val mkBuffer : unit -> {push : string -> unit, read : unit -> string,
                          reset : unit -> unit}

end
