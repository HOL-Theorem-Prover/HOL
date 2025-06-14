(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Terminal =
struct

  val defaultCols = 60

  val tputPath =
    case FindInPath.find "tput" of
      SOME path => FilePath.toHostPath path
    | NONE => "tput"

  fun currentCols () =
    let
      val output =
        RunProcess.captureOutput {cmdPath = tputPath, args = ["cols"]}
    in
      valOf (Int.fromString output)
    end
    handle _ => defaultCols

end
