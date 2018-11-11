(*  Title:      Pure/Concurrent/par_exn.ML
    Author:     Makarius

Parallel exceptions as flattened results from acyclic graph of
evaluations.  Interrupt counts as neutral element.
*)

signature PAR_EXN =
sig
  val make: exn list -> exn
  val dest: exn -> exn list option
  val is_interrupted: 'a Exn.result list -> bool
  val release_all: 'a Exn.result list -> 'a list
  val release_first: 'a Exn.result list -> 'a list
end;

structure Par_Exn: PAR_EXN =
struct

(* parallel exceptions *)

exception Par_Exn of exn list;
  (*non-empty list with unique identified elements sorted by exn_ord;
    no occurrences of Par_Exn or Exn.Interrupt*)

fun par_exns (Par_Exn exns) = exns
  | par_exns exn = if Exn.is_interrupt exn then [] else [exn];

fun make exns =
  let
    val exnss = map par_exns exns
    val exns' = List.concat exnss
  in if null exns' then Exn.Interrupt else Par_Exn exns' end;

fun dest (Par_Exn exns) = SOME exns
  | dest exn = if Exn.is_interrupt exn then SOME [] else NONE;


(* parallel results *)

fun is_interrupted results =
  List.exists (fn Exn.Exn _ => true | _ => false) results andalso
    Exn.is_interrupt (make (List.mapPartial Exn.get_exn results));

fun release_all results =
  if List.all (fn Exn.Res _ => true | _ => false) results
  then map Exn.release results
  else raise make (List.mapPartial Exn.get_exn results);

fun plain_exn (Exn.Res _) = NONE
  | plain_exn (Exn.Exn (Par_Exn _)) = NONE
  | plain_exn (Exn.Exn exn) = if Exn.is_interrupt exn then NONE else SOME exn;

fun release_first results =
  (case Portable.first_opt (fn _ => plain_exn) results of
    NONE => release_all results
  | SOME exn => Exn.reraise exn);

end;
