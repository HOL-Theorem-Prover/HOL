signature ReplCommands =
sig

(* Facilities for turning chunks of script file text into commands that can
   be fed to running REPL instances.

   Editor is responsible for detecting/selecting the relevant text but does
   not need to examine it further. Instead, it can feed, for example

    ReplCommands.execute_command (sml_text (...,{filename=...,text =...}));

   to the running session.  The ...s above correspond solely to trivially
   derived information about where and what the text is.  The editor needs to
   know to use temporary files to stash particularly huge bits of text, using
   the ViaFile constructor to the string_src type rather than writing huge
   string literals into the REPL.

   If the parsing of text into commands fails, the functions will put their
   errors into the Failure constructor and the execute_command can then get the
   REPL to emit the appropriate diagnostics.

*)

datatype string_src =
         Direct of string
       | ViaFile of {proxy_filename : string}
       | FromSource
         (* given the locn and filename (locn can't be unknown or similar;
            filename can't be NONE), the desired text is as specified in the
            script_text value (see below). *)

type script_text = locn.locn * {filename : string option, text : string_src}

datatype repl_command = Success of string | Failure of string

val sml_text : script_text -> repl_command
val set_initial_goal : script_text -> repl_command
val set_by_subgoal : script_text -> repl_command
val set_suffices_by_subgoal : script_text -> repl_command
val apply_tactic : script_text -> repl_command
val apply_tactic_pattern : script_text -> repl_command
  (* tactic patterns as per the second argument to the >~ operator *)
val load_dependencies : script_text -> repl_command

val execute_command : repl_command -> unit

end
