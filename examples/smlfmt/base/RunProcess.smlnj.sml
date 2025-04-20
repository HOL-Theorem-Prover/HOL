(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure RunProcess:
sig
  val captureOutput: {cmdPath: string, args: string list} -> string
end =
struct

  fun captureOutput {cmdPath, args} =
    raise Fail "RunProcess.smlnj.sml: captureOutput not yet implemented"

end
