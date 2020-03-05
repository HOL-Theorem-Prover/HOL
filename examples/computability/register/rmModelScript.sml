open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open combinTheory;
open whileTheory;
open indexedListsTheory;
open numeralTheory;
open primrecfnsTheory;
open listTheory;
open mp_then;
open boolTheory;
open numpairTheory;
open pred_setTheory;

val _ = new_theory "rmModel";


Type reg = “:num”;
Type state = “:num”;

Datatype:
  action = Inc num (state option) | Dec num (state option) (state option) 
End

(* regOf :: action -> reg num *)
Definition regOf_def[simp]:
  regOf (Inc r _) = r ∧ regOf (Dec r _ _) = r
End

(* inst_Val :: action -> value -> updated value *)
Definition inst_Val_def[simp]:
  inst_Val (Inc _ _) v = v + 1 /\
  inst_Val (Dec _ _ _) v = if v = 0 then 0 else v - 1
End

(* inst_Dest :: action -> value -> next state *)
Definition inst_Dest_def[simp]:
  inst_Dest (Inc _ s) v = s ∧
  inst_Dest (Dec _ s1 s2) v = if v = 0 then s2 else s1
End

(* 
   ---------------------------------- 
   ----- Register Machine Model -----
   ----------------------------------
*)


(*
    Q : state set (each one represented with a number); 
    tf : state -> action (returns the action inside the state);
    q0 : state (initial state);
    I : reg list (input regs);
    O : reg (output register);
*)
Datatype:
  rm = <|
    Q : state set; 
    tf : state -> action ;
    q0 : state ;
    In : reg list ;
    Out : reg 
  |>
End

(* Initialise *)
val init_machine_def = Define `
  init_machine m i = 
    ((λn. if findi n m.In = LENGTH m.In then 0
            else EL (findi n m.In) i)
    ,
        SOME m.q0)
`;


(* run machine :: machine -> (registers, state option) ->  (registers, state option) *)
val run_machine_1_def = Define `
    (run_machine_1 m (rs, NONE) = (rs, NONE)) 
    ∧
  (run_machine_1 m (rs, SOME s) = if s ∉ m.Q then (rs, NONE) 
    else case m.tf s of
    | Inc r so => ( rs (| r |-> rs r + 1 |), so )
    | Dec r so1 so2 => if rs r > 0 then ( rs (| r |-> rs r - 1 |) , so1)
                          else ( rs, so2))
`;

Theorem run_machine_1_alt:
  (run_machine_1 m (rs, NONE) = (rs, NONE)) ∧
   (run_machine_1 m (rs, SOME s) = if s ∉ m.Q then (rs, NONE)
     else let i = m.tf s;
              r = regOf i
          in (rs(|r |-> inst_Val i (rs r)|), inst_Dest i (rs r)))
Proof 
  rw[run_machine_1_def] >> Cases_on`m.tf s` >> rw[] >> fs[] >>
  rw[APPLY_UPDATE_THM, FUN_EQ_THM] >> rw[] >> rw[]
QED

val run_machine_def = Define `
  (run_machine m = WHILE (λ(rs, so). so ≠ NONE) (run_machine_1 m)) 
`;

val rsf_def = Define ` 
  rsf m i = FST (run_machine m (init_machine m i))
`;

val RUN_def = Define `
  RUN m i = FST (run_machine m (init_machine m i)) m.Out
`;

Definition conv_def:
  (conv (SOME s) = s+1) ∧
  (conv NONE = 0)
End

Definition strip_state_def:
  strip_state action = case action of 
     | Inc _ so => [conv so]
     | Dec _ so1 so2 => conv so1::[conv so2]
End

Definition opt_to_set_def[simp]:
  opt_to_set (SOME q) = {q}   ∧
  opt_to_set NONE = {}
End

Definition action_states_def[simp]:
  action_states (Inc r qopt) = opt_to_set qopt ∧
  action_states (Dec r qopt1 qopt2) = opt_to_set qopt1 ∪ opt_to_set qopt2
End

(* Definition of wellformedness of a register machine :
      Has finite states initial state(q0) is in that machine's set of all states(Q),
      and a valid state only transits to a valid state or NONE.
*)
val wfrm_def = Define `
  wfrm m ⇔ 
    FINITE m.Q ∧
    m.q0 ∈ m.Q ∧
    (∀s. s ∈ m.Q ⇒ action_states (m.tf s) ⊆ m.Q) 
`;

val rm_component_equality = theorem "rm_component_equality"

val _ = export_theory ()