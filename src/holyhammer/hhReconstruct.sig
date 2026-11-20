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
     time its replay took, lemmas the verified list it uses.

     on_verified, if given, is called with the progress of the
     reconstruction each time it advances: when Metis has replayed a list
     (the full list, or the list without its permutative equations, after
     the first replay, and each shorter list after a successful
     minimisation step), and when a lemma is found to be needed.  A
     progress is a verified list and the position of the minimisation in
     it: its first kept lemmas are known to be needed, and the others
     are still to be tried for removal.  When the minimisation is complete
     kept is the length of lemmas.  The last call is thus the furthest
     point reached, which a caller that abandons the reconstruction can
     resume from.

     resume, if given (NONE for the other callers), makes the
     reconstruction start from such a progress instead of the lemma list
     argument: that list is replayed again (and so timed again, as the
     load may have changed), and the minimisation skips its first kept
     lemmas.  If the list can only be replayed without its permutative
     equations, the lemmas found needed are not kept.  The progress of a
     resume must have kept <= length lemmas. *)
  type progress = {lemmas : string list, kept : int}
  type settings =
    {minimize : bool, preplay_timeout : real, minimize_timeout : real,
     minimize_deadline : Time.time option,
     on_verified : (progress -> unit) option, resume : progress option}
  type reconstruction =
    {stac : string, tac : tactic, t_replay : real, lemmas : string list}
  (* An upper bound on the replays that a reconstruction runs (minimize
     on): replays_left lemmas progress for one that is about to start,
     with the list to reconstruct and its resume, which is two for the
     preplay (the list, then without its permutative equations) or one
     for the resumed list, one attempt per lemma not yet kept, and one
     final replay of the printed form.  attempts_left progress is the
     number that remain once a reconstruction has reported that progress
     (the attempts and the final replay).  A resumed list that fails to
     replay again, as the load may have changed, can exceed the bound by
     the preplay's second replay. *)
  val replays_left : string list -> progress option -> int
  val attempts_left : progress -> int
  val hh_reconstruct_with :
    settings -> string list -> goal -> reconstruction
  (* Minimizes, with the timeouts in the references above. *)
  val hh_reconstruct : string list -> goal -> (string * tactic)

end
