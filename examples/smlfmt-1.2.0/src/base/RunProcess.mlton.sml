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
    let
      open MLton.Process

      val p = create
        { path = cmdPath
        , env = NONE
        , args = args
        , stderr = Param.self
        , stdin = Param.null
        , stdout = Param.pipe
        }

      val output = TextIO.inputAll (Child.textIn (getStdout p))
    in
      output
    end

end
