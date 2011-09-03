structure Logging :> Logging =
struct

datatype log_state =
  Not_logging
| Active_logging of TextIO.outstream

val log_state = ref Not_logging

local val op ^ = OS.Path.concat in
  val opentheory_dir = Globals.HOLDIR^"src"^"opentheory"
end

val mk_path = let
  exception exists
  fun mk_path name = let
    val path = OS.Path.concat(opentheory_dir,OS.Path.joinBaseExt{base=name,ext=SOME"4rt"})
  in if OS.FileSys.access(path,[]) then raise exists else path end
in fn name => let
     fun try n = mk_path (name^(Int.toString n)) handle exists => try (n+1)
   in mk_path name handle exists => try 0 end
end

fun start_logging() =
  case !log_state of
    Not_logging => let
      val name = Theory.current_theory()
      val path = mk_path name
      val file = TextIO.openOut path
    in log_state := Active_logging file end
  | Active_logging _ => ()

fun stop_logging() =
  case !log_state of
    Active_logging h => let
      val _ = TextIO.closeOut h
    in log_state := Not_logging end
  | Not_logging => ()

fun log_raw s =
  case !log_state of
    Active_logging h => TextIO.output h (s^"\n")
  | Not_logging => ()

fun log_num n = log_raw (Int.toString n)

fun log_name s = log_raw ("\""^String.toString s^"\"")

fun log_command s = log_raw s

fun log_nil () = log_command "nil"

fun log_list log = let
  fun logl []     = log_nil ()
    | logl (h::t) = (log h; logl t; log_command "cons")
in logl end

fun log_term tm = raise (Fail "unimplemented")

fun export_thm th = let
  val _ = case !log_state of
      Not_logging => ()
    | Active_logging _ => let
      val _ = log_thm th
      val _ = log_list log_term (Thm.hyp th)
      val _ = log_term (Thm.concl th)
           in log_command "thm" end
  val _ = Thm.delete_proof th
in () end

end
