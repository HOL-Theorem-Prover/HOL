(* PFT replay test: replays a .pft.bin file given as the first
   command-line argument and reports the number of theorems produced. *)
open Feedback

val () = case CommandLine.arguments () of
  [file] => let
    val db = PFTReplay.replay PFTReplay.empty_trDB file
      handle e as (HOL_ERR r) =>
        (print ("Uncaught HOL_ERR: " ^ message_of r ^ "\n"); raise e)
  in
    print ("Replay produced " ^ Int.toString (PFTReplay.size db) ^
           " theorems\n")
  end
| _ => print ("Usage: pft-replay-test <file.pft.bin>\n")
