(* ========================================================================= *)
(* FILE          : ttt_recordall.sml                                        *)
(* DESCRIPTION   : Record a TacticToe tactic database for the ENTIRE       *)
(*                 HOL4 standard library, via tttUnfold.ttt_record ().      *)
(* ========================================================================= *)

(*
   Goal
   ----
   Produce a TacticToe tactic database (under
   ${XDG_CACHE_HOME:-$HOME/.cache}/tactictoe/ttt_tacdata by default) covering
   every theory
   of the HOL4 standard library.

   How it works
   ------------
   ttt_record () records the tactic data of ancestry(current_theory()).
   In HOL4, Theory.ancestry of the current theory is Graph.fringe() (see
   src/postkernel/Theory.sml: get_parents returns the fringe for the
   current theory), and the transitive closure of the fringe is the set
   of ALL theories currently loaded into the theory graph.  Hence
   ttt_record () records every theory that has been loaded.

   tttUnfold.load_sigobj () loads every theory that is symlinked into
   $HOLDIR/sigobj -- i.e. the whole standard library.  It runs
   `cd $HOLDIR/sigobj; find ... Theory.sig`, so it is independent of the
   current directory.  After load_sigobj () has run, ttt_record ()
   therefore picks up the entire standard library: every standard
   library module is effectively made an ancestor of the current theory
   segment, so that ttt_record () records all of them.

   Completeness
   ------------
   ttt_record () may continue past a failed theory so that independent
   theories can still be recorded.  This driver audits the final manifest
   and fails the process if anything remains stale.  A record-all run can
   therefore never report success after a failed or skipped recording.

   Prerequisites
   -------------
   1. A full HOL4 build, so that $HOLDIR/sigobj is populated:
        bin/build -F
   2. Raise the open-file limit (recording opens many files):
        ulimit -Sn 20000

   Usage
   -----
        hol > use "src/tactictoe/examples/ttt_recordall.sml";

   By default any previously recorded (or downloaded) data in the
   TacticToe cache is wiped before recording afresh.  Set
   TTT_RECORDALL_KEEP=1 (what ttt_recordall.sh --keep does) to instead
   let ttt_record () reuse up-to-date manifest entries and re-record only
   the stale theories.
*)

load "aiLib";
load "tttSetup";
load "tttUnfold";
open aiLib;       (* load_sigobj                                            *)
open tttUnfold;   (* ttt_record, ttt_clean_record                           *)

val keep_existing =
  case OS.Process.getEnv "TTT_RECORDALL_KEEP" of
    SOME s => s <> "" andalso s <> "0"
  | NONE => false;

(* Load every theory in $HOLDIR/sigobj = the entire standard library. *)
load_sigobj ();

tttSetup.record_flag := true;
tttSetup.record_savestate_flag := false;
if keep_existing then () else ttt_clean_record ();
ttt_record ();

val {stale,up_to_date} = ttt_record_plan CurrentAncestry;
val _ =
  if null stale then
    print_endline
      ("recording complete: " ^ Int.toString (length up_to_date) ^
       " theories up-to-date")
  else
    let
      fun incomplete (thy,reason) =
        thy ^ " (" ^ reason_to_string reason ^ ")"
      val details = String.concatWith ", " (map incomplete stale)
    in
      raise Fail ("ttt_recordall: incomplete recordings: " ^ details)
    end;
