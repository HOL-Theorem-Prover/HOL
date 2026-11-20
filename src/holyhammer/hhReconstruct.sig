signature hhReconstruct =
sig

  include Abbrev

  (* Settings *)
  val reconstruct_flag : bool ref
  val minimization_timeout : real ref
  val reconstruction_timeout : real ref

  (* Reconstruction.  The full lemma list is replayed first, within
     preplay_timeout.  Minimisation then drops lemmas while Metis still
     replays the rest; each attempt gets at most minimize_timeout, less
     when the replays are fast, and no attempt starts after
     minimize_deadline.  stac is the verified tactic and t_replay the
     time its replay took.  on_verified, if given, is called with each
     lemma list as soon as Metis has replayed it: the full list (or the
     list without its permutative equations) after the first replay, and
     each shorter list after a successful minimisation step.  The last
     call is thus the shortest list verified so far, which a caller that
     abandons the reconstruction can resume from. *)
  type settings =
    {minimize : bool, preplay_timeout : real, minimize_timeout : real,
     minimize_deadline : Time.time option,
     on_verified : (string list -> unit) option}
  type reconstruction = {stac : string, tac : tactic, t_replay : real}
  val hh_reconstruct_with :
    settings -> string list -> goal -> reconstruction
  (* Minimizes, with the timeouts in the references above. *)
  val hh_reconstruct : string list -> goal -> (string * tactic)

end
