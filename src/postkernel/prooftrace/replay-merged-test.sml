open Feedback PFTReplay
val db = replay empty_trDB "merged.pft.bin"
handle (e as (HOL_ERR m)) => (print("Uncaught HOL_ERR: "^(message_of m)); raise e)
val () = print ("Replay produced "^(Int.toString(size db))^" theorems\n")
