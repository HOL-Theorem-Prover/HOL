signature hhReconstruct =
sig

  include Abbrev

  (* The limits of hh_reconstruct: reconstruction_timeout, of each replay,
     starts at hhConfig.default_preplay_timeout, and minimization_timeout,
     of each minimisation attempt, at hhConfig.default_minimize_timeout.
     Every replay limit and time is in CPU seconds of the thread running
     the replay (smlTimeout.thread_timeout). *)
  val minimization_timeout : real ref
  val reconstruction_timeout : real ref

  type settings =
    {minimize : bool, preplay_timeout : real, minimize_timeout : real,
     minimize_deadline : Time.time option}
  (* drop_one_minimize try minimize_timeout deadline lemmas best: the
     minimisation loop of hh_reconstruct_with over a replay function, for
     tests.  It drops the lemmas one at a time, keeping a lemma when the
     replay without it fails, and starts no attempt after deadline.  try
     limit candidate replays candidate within limit seconds, giving its
     result and time on success; the limit is min (minimize_timeout,
     2 t + 0.2), t the fastest verified replay so far (initially that of
     best, the verified result of lemmas), and so never rises.  The pair
     returned is the verified result of the kept list. *)
  val drop_one_minimize :
    (real -> string list -> ('a * real) option) -> real -> Time.time option ->
    string list -> 'a * real -> string list * ('a * real)
  (* timeout_tactic t tac g ctxt: the goals tac leaves on g, run in
     ctxt, and the CPU seconds it used, NONE when it fails or uses more
     than t CPU seconds; the limit every replay runs under, for tests. *)
  val timeout_tactic :
    real -> tactic -> goal -> Context.t -> (goal list * real) option
  (* hh_reconstruct_with settings lemmas g ctxt replays the lemmas with
     Metis on g in ctxt, the context of the proof HolyHammer was called
     from, within preplay_timeout, and if that fails, the lemmas without
     their permutative equations.  With minimize, drop_one_minimize then
     minimises the list replayed, with minimize_timeout and
     minimize_deadline, and the call is printed with the lemmas' short
     names if that replays too.  stac is the verified
     tactic and t_replay the CPU time its replay took.  Raises HOL_ERR if
     no list replays. *)
  type reconstruction = {stac : string, tac : tactic, t_replay : real}
  val hh_reconstruct_with :
    settings -> string list -> goal -> Context.t -> reconstruction
  (* hh_reconstruct_with, minimising, with the limits above, in the
     ambient context. *)
  val hh_reconstruct : string list -> goal -> (string * tactic)

end
