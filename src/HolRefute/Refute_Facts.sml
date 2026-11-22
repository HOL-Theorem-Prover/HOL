structure Refute_Facts :> Refute_Facts = struct
  (* Disk theorems are checked kernel imports: DISK_THM is the marker HOL4
     itself accepts, subtracting it in Theory.oracle_string_of and listing
     it in Sanity.accepted_oracles.  Every other oracle, and every axiom,
     is not a proof. *)
  fun trusted theorem =
    null (Thm.hyp theorem) andalso
    (Tag.isEmpty (Thm.tag theorem) orelse Tag.isDisk (Thm.tag theorem))

  (* Refute calls run one at a time ([Refute_Core.refute_problem] holds
     its output mutex for the whole call), so one record serves every
     thread working for the running call.  Outside a call nothing is
     recorded: a registration's theorems are checked where a call uses
     them. *)
  val record = Synchronized.var "Refute_Facts" (NONE : string list option)

  val max_shown = 160

  fun shorten text =
    if size text <= max_shown then text
    else String.substring (text, 0, max_shown) ^ "..."

  (* The refusals of the innermost [capture] running on this thread. *)
  val captured : string list ref Thread_Data.var = Thread_Data.var ()

  (* The refusals the innermost [tentative] on this thread holds back. *)
  val held : string list ref Thread_Data.var = Thread_Data.var ()

  fun add reasons reason =
    if Lib.mem reason (!reasons) then () else reasons := !reasons @ [reason]

  (* A [capture] inside a [tentative] sees the refusal at once, so that
     no cache keeps a value resting on it. *)
  fun refuse reason =
    (Option.app (fn reasons => add reasons reason) (Thread_Data.get captured);
     case Thread_Data.get held of
        SOME reasons => add reasons reason
      | NONE =>
          (* only a thread working for the call ([Refute_Session.bind]):
             a registration on another thread caps nothing *)
          if Option.isSome (Refute_Session.current ()) then
            Synchronized.change record (fn
                NONE => NONE
              | SOME reasons =>
                  SOME (if Lib.mem reason reasons then reasons
                        else reasons @ [reason]))
          else ())

  fun tentative f =
    let
      val reasons = ref []
      val result = Thread_Data.setmp held (SOME reasons) f ()
    in
      List.app refuse (!reasons); result
    end

  fun describe theorem =
    let
      val (oracles, axioms) = Tag.dest_tag (Thm.tag theorem)
      val oracles = List.filter (fn oracle => oracle <> "DISK_THM") oracles
      val why =
        (if null (Thm.hyp theorem) then []
         else if length (Thm.hyp theorem) = 1 then ["1 hypothesis"]
         else [Int.toString (length (Thm.hyp theorem)) ^ " hypotheses"]) @
        map (fn oracle => "oracle " ^ oracle) oracles @
        map (fn axiom => "axiom " ^ axiom) axioms
    in
      "refused fact (" ^ String.concatWith ", " why ^ "): " ^
      shorten (Parse.term_to_string (Thm.concl theorem))
    end

  fun check theorem =
    if trusted theorem then () else refuse (describe theorem)

  fun concl theorem = (check theorem; Thm.concl theorem)

  fun rhs theorem = boolSyntax.rhs (concl theorem)

  (* Terms read from theorems the finder may never use, each with the
     refusal it carries until a problem uses it. *)
  val pending = Synchronized.var "Refute_Facts.pending"
    ([] : (Term.term * string) list)

  fun pending_reason term =
    Option.map #2
      (List.find (fn (other, _) => Term.aconv other term)
         (Synchronized.value pending))

  fun defer theorem term =
    (if trusted theorem then ()
     else Synchronized.change pending (fn terms =>
            (term, describe theorem) :: terms);
     term)

  fun carry from to =
    (case pending_reason from of
         SOME reason =>
           Synchronized.change pending (fn terms => (to, reason) :: terms)
       | NONE => ();
     to)

  fun use term = Option.app refuse (pending_reason term)

  fun foreign registration =
    refuse ("refused registration the finder did not make: " ^ registration)

  fun capture f =
    let
      val outer = Thread_Data.get captured
      val reasons = ref []
      fun pass_on () =
        Option.app (fn outer =>
          outer := !outer @
            List.filter (fn reason => not (Lib.mem reason (!outer)))
              (!reasons)) outer
      val result =
        Thread_Data.setmp captured (SOME reasons) f ()
        handle e => (pass_on (); raise e)
    in
      pass_on (); (result, !reasons)
    end

  fun refused () = Option.getOpt (Synchronized.value record, [])

  fun any_refused () = not (null (refused ()))

  fun recording f =
    let
      val _ = Synchronized.change record (Lib.K (SOME []))
      val _ = Synchronized.change pending (Lib.K [])
      fun take () =
        (Synchronized.change pending (Lib.K []);
         Synchronized.change_result record (fn reasons =>
           (Option.getOpt (reasons, []), NONE)))
      val result = f () handle e => (ignore (take ()); raise e)
    in
      (result, take ())
    end
end
