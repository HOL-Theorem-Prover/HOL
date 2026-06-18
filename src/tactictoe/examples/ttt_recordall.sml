(* ========================================================================= *)
(* FILE          : ttt_recordall.sml                                        *)
(* DESCRIPTION   : Record a TacticToe tactic database for the ENTIRE       *)
(*                 HOL4 standard library, via tttUnfold.ttt_record ().      *)
(* ========================================================================= *)

(*
   Goal
   ----
   Produce a TacticToe tactic database (under src/tactictoe/ttt_tacdata)
   covering every theory of the HOL4 standard library.

   How it works
   ------------
   ttt_record () records the tactic data of ancestry(current_theory()).
   In HOL4, Theory.ancestry of the current theory is Graph.fringe() (see
   src/postkernel/Theory.sml: get_parents returns the fringe for the
   current theory), and the transitive closure of the fringe is the set
   of ALL theories currently loaded into the theory graph.  Hence
   ttt_record () records every theory that has been loaded.

   aiLib.load_sigobj () loads every theory that is symlinked into
   $HOLDIR/sigobj -- i.e. the whole standard library.  It runs
   `cd $HOLDIR/sigobj; find ... Theory.sig`, so it is independent of the
   current directory.  After load_sigobj () has run, ttt_record ()
   therefore picks up the entire standard library: every standard
   library module is effectively made an ancestor of the current theory
   segment, so that ttt_record () records all of them.

   Prerequisites
   -------------
   1. A full HOL4 build, so that $HOLDIR/sigobj is populated:
        bin/build -F
   2. Raise the open-file limit (recording opens many files):
        ulimit -Sn 20000

   Usage
   -----
        hol > use "src/tactictoe/examples/ttt_recordall.sml";

   This takes about 8 hours for the full standard library
   (see src/tactictoe/README).  ttt_clean_record () is called first, so
   any previously recorded (or downloaded) data in
   src/tactictoe/ttt_tacdata is wiped before recording afresh.  Comment
   out the ttt_clean_record () line below to instead accumulate / skip
   already-recorded theories.
*)

load "aiLib";
load "tttSetup";
load "tttUnfold";
open aiLib;       (* load_sigobj                                            *)
open tttUnfold;   (* ttt_record, ttt_clean_record                           *)

(* Load every theory in $HOLDIR/sigobj = the entire standard library. *)
load_sigobj ();

(* Fresh recording of tactic data for all loaded theories. *)
tttSetup.record_flag := true;
tttSetup.record_savestate_flag := false;
ttt_clean_record ();
ttt_record ();