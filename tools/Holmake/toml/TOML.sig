signature TOML =
sig


datatype value = datatype TOMLvalue_dtype.value
type table = TOMLvalue_dtype.table
type key = string list
  (* key allows for following string lists like 'grandparent.parent.child' *)

val lookupInValue : value -> key -> value option
val lookupInTable : table -> key -> value option


val fromString : string -> table
val fromFile : string -> table (* can raise parse/file-not-found exceptions *)

(* You may wish to merge multiple TOML config files the exist in the
   ascending path of parent directories, with lower files
   overriding/refining higher ones.
   (Lower = "closer to my directory", higher = "closer to the root /".)

   This "merged" configuration is implemented by the dirmerged type
*)

type dirmerged

val dmFromFile : string -> dirmerged
val mergeDMs : dirmerged -> dirmerged -> dirmerged
val lookupValueFromPath : dirmerged -> string -> key -> value
  (* string is path of current directory *)


end
