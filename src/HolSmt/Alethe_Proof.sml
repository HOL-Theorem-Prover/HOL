(* Proof reconstruction for cvc5/Alethe: SML type of Alethe proofs *)

structure Alethe_Proof =
struct

  (* A single Alethe proof step. We use a generic record representation
     rather than one-constructor-per-rule (unlike Z3_Proof), because
     Alethe is a standardized format with string-named rules.
     This is more extensible and easier to parse. *)

  type step = {
    id        : string,              (* step identifier: "h1", "t2", etc. *)
    clause    : Term.term list,      (* clause literals *)
    rule      : string,              (* rule name *)
    premises  : string list,         (* premise step IDs *)
    args      : Term.term list,      (* rule arguments *)
    discharge : string list          (* discharged assumption IDs *)
  }

  (* anchor for subproofs *)
  type anchor = {
    step_id  : string,              (* the step ID this anchor belongs to *)
    args     : (string * Term.term option) list
                                    (* variable bindings: (name, optional sort) *)
  }

  (* A proof command is either an assume, a step, or an anchor+subproof *)
  datatype command =
      ASSUME of string * Term.term            (* id, assumed formula *)
    | STEP of step                             (* a proof step *)
    | ANCHOR of anchor * command list          (* anchor with nested commands *)

  (* Full proof = ordered list of commands *)
  type proof = command list

end
