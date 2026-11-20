(* ===================================================================== *)
(* FILE          : HOLmessage.sig                                        *)
(* DESCRIPTION   : Messages that carry HOL values rather than their      *)
(*                 printed form.                                         *)
(* ===================================================================== *)

signature HOLmessage =
sig

  (* A message is text with holes in it that hold HOL values.  The
     point of the type is what it does *not* do: a value put into a
     message is not printed when the message is built.  It is printed
     when -- and if -- someone looks at it, by whichever back end that
     consumer has installed.

     That matters for two separate reasons.

     Errors in HOL are mostly speculative: `Lib.total', `can' and the
     1800-odd `handle HOL_ERR' sites raise and discard exceptions as a
     control structure, and an error message that rendered a term at
     the raise site would charge every one of those for output nobody
     reads.  `Msg.tm' allocates a closure instead.

     And a consumer that is not a terminal wants more than characters.
     `PPBackEnd.lsp_terminal' renders the same value into annotated
     segments, so a front end can show the type of a free variable the
     message mentions; `EmitTeX' renders it into \HOL... macros.  Text
     is what a message degrades to, not what it is. *)
  type message

  val empty    : message
  val txt      : string -> message

  (* [pp f] is the value whose printed form is `f ()'.  `f' is called
     at most once per rendering, under the caller's back end, and is
     allowed to fail: a renderer substitutes a placeholder rather than
     letting an exception escape while reporting an error. *)
  val pp       : (unit -> HOLPP.pretty) -> message

  val ^^       : message * message -> message
  val concat   : message list -> message

  val isEmpty  : message -> bool

  (* true when the message holds no HOL values, so that a consumer
     with a structured surface can skip building one. *)
  val isPlain  : message -> bool

  (* [toString m] never re-wraps text that went in through `txt' --
     it comes back byte for byte, embedded newlines and all.  A
     message built only from `txt' is therefore indistinguishable
     from the string it was built from, which is what lets the
     string-valued interfaces in `Feedback' keep their meaning. *)
  val toString : message -> string
  val toPretty : message -> HOLPP.pretty

  (* How `toString' renders a suspended value.  A HOL printer renders
     through whatever back end the session has installed, which in an
     interactive session is a colour one -- and the text a message
     degrades to must not depend on that, because it is what every
     string-valued interface in `Feedback' hands back.  `src/parse'
     replaces this with a renderer that pins a plain back end, making
     `toString o Msg.tm' agree with `Parse.term_to_string' exactly.
     `toPretty' deliberately does not go through here: that is the
     path a colour terminal and the LSP's segment back end want. *)
  val plain_renderer : ((unit -> HOLPP.pretty) -> string) ref

end
