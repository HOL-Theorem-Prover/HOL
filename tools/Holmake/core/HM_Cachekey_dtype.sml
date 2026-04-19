(* Shared datatypes for the cachekey-based rebuild machinery.
   Kept separate from HM_Cachekey so that HM_Core_Cline can depend
   on the datatype without needing HM_DepGraph (which HM_Cachekey
   depends on, and which is loaded after HM_Core_Cline). *)

structure HM_Cachekey_dtype =
struct

  (* Strategy for deciding whether a theory target needs rebuilding.
       Mtime    : use Holmake's traditional modification-time comparison.
       Cachekey : use a recursive content hash of the target's inputs;
                  skip the script run when the hash matches a stamp
                  recorded at the previous successful build. *)
  datatype rebuild_strategy = Mtime | Cachekey

  fun rebuild_strategy_toString Mtime    = "mtime"
    | rebuild_strategy_toString Cachekey = "cachekey"

  fun rebuild_strategy_fromString s =
      case s of
          "mtime"    => SOME Mtime
        | "cachekey" => SOME Cachekey
        | _          => NONE

end
