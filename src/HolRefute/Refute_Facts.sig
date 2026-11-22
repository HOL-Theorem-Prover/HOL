(* The one checked point for theorems the finder uses: every theorem
   whose conclusion becomes a term or a value of the problem, or whose
   proof decides a step of it, goes through [concl] (or [rhs], [check]).
   A theorem with hypotheses or with a tag other than the disk marker (an
   oracle such as [cheat], or an axiom) is refused, and so is a
   registration the finder did not make itself ([foreign]); the running
   Refute call records each refusal, and its counterexamples without a
   kernel certificate are then only Potential, with the refusals as
   reasons. *)
signature Refute_Facts = sig
  (* No hypotheses, and a tag that is empty or only HOL's disk marker. *)
  val trusted : Thm.thm -> bool
  (* The conclusion, after recording the theorem if it is not [trusted]. *)
  val concl : Thm.thm -> Term.term
  val rhs : Thm.thm -> Term.term
  val check : Thm.thm -> unit
  (* For tables read whole of which a problem uses a part: [defer thm tm]
     returns [tm], read from [thm], and holds its refusal until [use] meets
     [tm] (or a term [carry tm] made from it), when a problem reads it.
     Held refusals last for the running call. *)
  val defer : Thm.thm -> Term.term -> Term.term
  val carry : Term.term -> Term.term -> Term.term
  val use : Term.term -> unit
  (* Records a registration the finder did not make that the problem
     used, by its description. *)
  val foreign : string -> unit
  (* [capture f] runs [f ()] and also returns what it refused on this
     thread, for a cache that must not keep a value resting on a refused
     fact. *)
  val capture : (unit -> 'a) -> 'a * string list
  (* [tentative f] runs [f ()] and keeps what it refused only if it
     returns: an attempt that raises (a reading the caller then abandons)
     leaves no refusal behind. *)
  val tentative : (unit -> 'a) -> 'a
  (* What the running call has refused so far, and whether anything. *)
  val refused : unit -> string list
  val any_refused : unit -> bool
  (* [recording f] runs [f ()] as one Refute call and returns what it
     refused, in order, without duplicates. *)
  val recording : (unit -> 'a) -> 'a * string list
end
