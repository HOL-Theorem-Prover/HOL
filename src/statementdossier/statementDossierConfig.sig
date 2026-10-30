signature statementDossierConfig =
sig

(* Read a TOML configuration without loading theories or writing reports.
   File paths are relative to the configuration file's directory.
   Raises Fail on invalid configuration. *)
val read : string -> {config : statementDossierLib.config,
                      load_path : string list, theories : string list}

end
