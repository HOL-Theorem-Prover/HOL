structure Keepers = struct
(*---------------------------------------------------------------------------*)
(* A list of the signatures that we think users will not be interested in.   *)
(*---------------------------------------------------------------------------*)

val exclude =
  [ "MLY_base.sig", "DiskFiles.grm.sig", "holindex.grm.sig",
    "holindex.sig" ]

end
