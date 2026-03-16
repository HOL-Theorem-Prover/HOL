signature PFTReplay = sig

  (* Database of replayed theorems, shared across theories.
     Keys are "Thy$name" for named theorems and "Thy#n" for
     anonymous theorems. *)
  type trDB

  val empty_trDB : trDB

  (* Replay a single .pft file. The theory name and format are
     inferred from the filename:
       foo.pft.bin   -> binary, thyname = "foo"
       foo.pft.jsonl -> JSONL,  thyname = "foo"
       foo.pft       -> binary, thyname = "foo"
     Ancestor theories must already be in the trDB.
     Replayed theorems are inserted into the trDB as they are saved. *)
  val replay : trDB -> string -> trDB

  (* Look up a theorem by key: "Thy$name" or "Thy#n" *)
  val lookup : trDB -> string -> Thm.thm option

  (* Number of theorems stored *)
  val size : trDB -> int

  (* All entries as (key, thm) pairs *)
  val listItems : trDB -> (string * Thm.thm) list

end
