(* ===================================================================== *)
(* FILE          : Msg.sig                                               *)
(* DESCRIPTION   : Building messages out of HOL values.                  *)
(* ===================================================================== *)

signature Msg =
sig

  type term = Term.term
  type hol_type = Type.hol_type
  type thm = Thm.thm

  type message = HOLmessage.message

  (* re-exported from HOLmessage so that a caller needs one name *)
  val empty    : message
  val txt      : string -> message
  val pp       : (unit -> HOLPP.pretty) -> message
  val ^^       : message * message -> message
  val concat   : message list -> message
  val isEmpty  : message -> bool
  val isPlain  : message -> bool
  val toString : message -> string
  val toPretty : message -> HOLPP.pretty

  (* The point of the type.  None of these prints anything: each
     suspends the value, to be printed later by whichever back end the
     reader has installed.  So

         raise mk_HOL_ERRm "Struct" "f" (txt "not a " ^^ tm R)

     costs an allocation where the string-concatenation form it
     replaces costs a pretty-print -- which matters because most of
     the errors HOL raises are caught and discarded. *)
  val tm       : term -> message
  val ty       : hol_type -> message
  val th       : thm -> message

  (* The message rendered through `PPBackEnd.lsp_terminal', i.e. as
     text carrying what the terminal back ends say in colour: which
     spans are constants, which are free variables, and their types.
     Concatenating the segments' `text' gives exactly `toString' under
     a raw back end. *)
  val segments : message -> PPBackEnd.pp_segment list

end
