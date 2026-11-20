signature hhReconstruct =
sig

  include Abbrev

  (* Settings.  reconstruction_timeout, the replay limit of
     hh_reconstruct, starts at hhConfig.default_preplay_timeout, and
     minimization_timeout at hhConfig.default_minimize_timeout. *)
  val reconstruct_flag : bool ref
  val minimization_timeout : real ref
  val reconstruction_timeout : real ref

  (* Reconstruction.  The full lemma list is replayed first, within
     preplay_timeout.  Minimisation then drops lemmas while Metis still
     replays the rest; each attempt gets at most minimize_timeout, and at
     most twice the time of the first replay plus 0.2 s, and no attempt
     starts after minimize_deadline.  stac is the verified tactic and
     t_replay the time its replay took. *)
  type settings =
    {minimize : bool, preplay_timeout : real, minimize_timeout : real,
     minimize_deadline : Time.time option}
  (* drop_one_minimize try limit deadline lemmas best: the minimisation
     loop of hh_reconstruct_with over a replay function, for tests.
     try limit candidate replays candidate within limit seconds; every
     attempt gets the same limit. *)
  val drop_one_minimize :
    (real -> string list -> ('a * real) option) -> real -> Time.time option ->
    string list -> 'a * real -> string list * ('a * real)
  type reconstruction = {stac : string, tac : tactic, t_replay : real}
  val hh_reconstruct_with :
    settings -> string list -> goal -> reconstruction
  (* Minimizes, with the timeouts in the references above. *)
  val hh_reconstruct : string list -> goal -> (string * tactic)

end
