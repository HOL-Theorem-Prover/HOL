signature statementDossierConfig =
sig

(* Read a TOML configuration, load its theories, and write the report.
   File paths are relative to the configuration file's directory.
   Raises Fail on invalid configuration. *)
val run : string -> unit

end
