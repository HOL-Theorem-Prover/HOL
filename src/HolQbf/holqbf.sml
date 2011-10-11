open Opentheory Logging
fun main() = let
  exception E of term
  val t = ( raw_read_article TextIO.stdIn {
    define_tyop = fn _ => raise Fail "define_tyop",
    define_const = fn _ => raise Fail "define_const",
    axiom = fn _ => fn (_,c) => raise (E c),
    const_name = const_name_in_map,
    tyop_name = tyop_name_in_map } ; raise Fail "no theorem" )
  handle E t => t
  val _ = Feedback.emit_MESG := false
  val _ = raw_start_logging TextIO.stdOut
  val th = HolQbfLib.decide t
  val _ = export_thm th
  val _ = stop_logging()
in () end
val _ = PolyML.export("holqbf",main)
