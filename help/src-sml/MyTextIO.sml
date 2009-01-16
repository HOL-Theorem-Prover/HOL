structure TextIO = struct
  open TextIO
  fun inputLine strm = case TextIO.inputLine strm of
                          "" => NONE
                        | s => SOME s
end
