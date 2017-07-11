(* build command line tool *)

structure Globals =
struct
  val HOLDIR = "../../../../..";
end;

use "header.sml";
use "holfoot_command_line.sml";

val examplesDir = ".";

val use = QUse.use
