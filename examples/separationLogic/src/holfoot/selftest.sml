open HolKernel bossLib

val _ = loadPath :=
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) ::
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot"]) ::
            !loadPath;

val _ = map load ["holfootParser", "holfoot_pp_print", "holfootLib"];
open holfootParser;
open holfoot_pp_print;
open holfootLib;

open separationLogicTheory vars_as_resourceTheory holfootTheory generalHelpersTheory;

val hard_fail = true;
val quiet = true;
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val examples_dir = concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot/EXAMPLES/automatic/"];

(* For manual

val hard_fail = false;
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;
val quiet = true
*)

fun test_file file = let
  open PPBackEnd Parse
  val ok = snd ((holfootLib.holfoot_interactive_verify_spec (not quiet) (not quiet) (concat [examples_dir, file]) (SOME [generate_vcs]) []));
  val _ = print "\n";
  val _ = if (not ok andalso hard_fail) then Process.exit Process.failure else ();
in ok end

val _ = test_file "append-parkinson.dsf";
val _ = test_file "append-parkinson.sf";
val _ = test_file "append-unroll.dsf";
val _ = test_file "append.dsf";
val _ = test_file "append.dsf2";
val _ = test_file "append.sf";
val _ = test_file "array_copy-shape.dsf";
val _ = test_file "assert-dispose.dsf";
(* val _ = test_file "binary_search-shape.dsf"; *)
val _ = test_file "business1.sf";
val _ = test_file "copy.dsf";
val _ = test_file "copy.dsf2";
val _ = test_file "copy.sf";
val _ = test_file "entailments.ent";
val _ = test_file "filter.sf";
val _ = test_file "filter_rec-gen.dsf";
val _ = test_file "filter_rec.dsf";
val _ = test_file "list.sf";
val _ = test_file "list_alloc_dealloc_length.dsf";
val _ = test_file "list_length.dsf";
val _ = test_file "list_length.sf";
val _ = test_file "list_length_iter.dsf";
val _ = test_file "list_length_iter.dsf2";
val _ = test_file "list_length_iter.sf";
val _ = test_file "memory_manager.sf";
val _ = test_file "mergesort.sf";
val _ = test_file "mm_buf.sf";
val _ = test_file "mm_non_blocking.sf";
val _ = test_file "parallel_mergesort.sf";
val _ = test_file "parallel_tree_deallocate.sf";
val _ = test_file "passive_stack_race.sf";
val _ = test_file "pointer_non_transferring_buffer.sf";
val _ = test_file "pointer_transferring_buffer.sf";
val _ = test_file "queue.dsf";
val _ = test_file "queue.sf";
val _ = test_file "quicksort-shape.dsf";
val _ = test_file "remove.sf";
val _ = test_file "reverse-parkinson.dsf";
val _ = test_file "reverse-parkinson.sf";
val _ = test_file "reverse.dsf";
val _ = test_file "reverse.dsf2";
val _ = test_file "reverse.sf";
val _ = test_file "split_binary_semaphore.sf";
val _ = test_file "tree.sf";
val _ = test_file "tree_copy.dsf";

val _ = Process.exit Process.success;
