(* the systeml function takes a list of strings and passes this to the
   OS to be executed.  The first string is the command, the rest are
   arguments. *)
structure Systeml = struct
local
  fun dquote s = concat ["\"", s, "\""];
  fun squote s = concat ["'", s, "'"];
  fun concat_wspaces munge acc strl =
    case strl of
      [] => concat (List.rev acc)
    | [x] => concat (List.rev (munge x :: acc))
    | (x::xs) => concat_wspaces munge (" " :: munge x :: acc) xs
in
  fun winnt_systeml l = let
    val command = "call "^concat_wspaces dquote [] l
  in
    Process.system command
  end

  fun unix_systeml l = let
    fun unix_trans c = case c of #"'" => "'\\''" | x => str x
    val command = concat_wspaces (squote o String.translate unix_trans) [] l
  in
    Process.system command
  end
end

end;
