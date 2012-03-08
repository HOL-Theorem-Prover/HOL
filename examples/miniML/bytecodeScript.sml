open HolKernel boolLib bossLib Parse; val _ = new_theory "bytecode";

open arithmeticTheory listTheory finite_mapTheory;

infix \\ val op \\ = op THEN;


(* --- Syntax --- *)

val _ = Hol_datatype `
  bc_stack_op =
    Pop                     (* pop top of stack *)
  | Pops of num             (* pop n elements under stack top *)
  | PushNum of num          (* push num onto stack *)
  | Cons of num => num      (* push new cons with tag m and n elements *)
  | Load of num             (* push stack[n+1] *)
  | Store of num            (* pop and store in stack[n+1] *)
  | El of num               (* read field n of cons block *)
  | Tag                     (* read tag from cons block *)
  | IsNum | Equal           (* tests *)
  | Add | Sub | Mult | Div2 | Mod2 | Less  (* arithmetic *)`;

val _ = Hol_datatype `
  bc_inst =
    Stack of bc_stack_op
  | Jump of num             (* jump to location n *)
  | JumpNil of num          (* conditional jump to location n *)
  | Call of num             (* call location n *)
  | JumpPtr                 (* jump based on code pointer *)
  | CallPtr                 (* call based on code pointer *)
  | Return                  (* pop return address, jump *)
  | Ref                     (* create a new ref cell *)
  | Deref                   (* dereference a ref cell *)
  | Update                  (* update a ref cell *)`;


(* --- Semantics --- *)

(* the stack is a list of elements of bc_value *)

val _ = Hol_datatype `
  bc_value =
    Number of num                  (* natural *)
  | Block of num => bc_value list  (* cons block: tag and payload *)
  | CodePtr of num                 (* code pointer *)
  | RefPtr of num                  (* pointer to ref cell *)`;

val _ = Hol_datatype `
  bc_state =
   <| (* main state components *)
      stack : bc_value list;
      code : bc_inst list ;
      pc : num ;
      refs : num |-> bc_value ;
      (* artificial state components *)
      inst_length : bc_inst -> num
   |>`;

(* fetching the next instruction from the code *)

val bc_fetch_aux_def = Define `
  (bc_fetch_aux [] len n = NONE) /\
  (bc_fetch_aux (x::xs) len n =
     if n = 0 then SOME x else
     if n < len x + 1 then NONE else
       bc_fetch_aux xs len (n - (len x + 1)))`;

val bc_fetch_def = Define `
  bc_fetch s = bc_fetch_aux s.code s.inst_length s.pc`;

(* most instructions just bump the pc along, for this we use bump_pc *)

val bump_pc_def = Define `
  bump_pc s =
    case bc_fetch s of
       NONE => s
     | SOME x => s with pc := s.pc + s.inst_length x + 1`;

(* next state relation *)

val bool2num_def = Define `
  (bool2num T = 1) /\ (bool2num F = 0)`;

val (bc_stack_op_rules,bc_stack_op_ind,bc_stack_op_cases) = Hol_reln `
  bc_stack_op Pop (x::xs) (xs) /\
  bc_stack_op (Pops (LENGTH ys)) (x::ys++xs) (x::xs) /\
  bc_stack_op (PushNum n) (xs) (Number n::xs) /\
  bc_stack_op (Cons tag (LENGTH ys)) (ys ++ xs) (Block tag (REVERSE ys)::xs) /\
  (n < LENGTH xs ==> bc_stack_op (Load n) xs (EL n xs :: xs)) /\
  bc_stack_op (Store (LENGTH ys)) (y::ys ++ x::xs) (ys ++ y::xs) /\
  (n < LENGTH ys ==> bc_stack_op (El n) ((Block tag ys)::xs) (EL n ys::xs)) /\
  bc_stack_op Tag ((Block tag ys)::xs) (Number tag::xs) /\
  bc_stack_op IsNum (x::xs) (Number (bool2num (?n. x = Number n)) :: xs) /\
  bc_stack_op Equal (x2::x1::xs) (Number (bool2num (x1 = x2)) :: xs) /\
  bc_stack_op Less (Number n :: Number m :: xs) (Number (bool2num (m < n))::xs) /\
  bc_stack_op Add (Number n :: Number m :: xs) (Number (m + n)::xs) /\
  bc_stack_op Sub (Number n :: Number m :: xs) (Number (m - n)::xs) /\
  bc_stack_op Mult (Number n :: Number m :: xs) (Number (m * n)::xs) /\
  bc_stack_op Div2 (Number m :: xs) (Number (m DIV 2)::xs) /\
  bc_stack_op Mod2 (Number m :: xs) (Number (m MOD 2)::xs)`

val (bc_next_rules,bc_next_ind,bc_next_cases) = Hol_reln `
  (!s b ys.
     (bc_fetch s = SOME (Stack b)) /\ bc_stack_op b (s.stack) ys ==>
     bc_next s (bump_pc s with stack := ys))
  /\
  (!s n.
     (bc_fetch s = SOME (Jump n)) ==>
     bc_next s (s with pc := n))
  /\
  (!s s' n x xs.
     (bc_fetch s = SOME (JumpNil n)) /\ (s.stack = x::xs) /\
     (s' = s with stack := xs) ==>
     bc_next s (if x = Number 0 then bump_pc s' else s' with pc := n))
  /\
  (!s n x xs.
     (bc_fetch s = SOME (Call n)) /\ (s.stack = x::xs) ==>
     bc_next s (s with <| pc := n; stack := x :: CodePtr ((bump_pc s).pc) :: xs |>))
  /\
  (!s ptr x xs.
     (bc_fetch s = SOME CallPtr) /\ (s.stack = CodePtr ptr::x::xs) ==>
     bc_next s (s with <| pc := ptr; stack := x :: CodePtr ((bump_pc s).pc) :: xs |>))
  /\
  (!s ptr xs.
     (bc_fetch s = SOME JumpPtr) /\ (s.stack = CodePtr ptr::xs) ==>
     bc_next s (s with <| pc := ptr; stack := xs |>))
  /\
  (!s n x xs.
     (bc_fetch s = SOME Return) /\ (s.stack = x :: CodePtr n :: xs) ==>
     bc_next s (s with <| pc := n; stack := x::xs |>))
  /\
  (!s x xs ptr.
     (bc_fetch s = SOME Ref) /\ (s.stack = x::xs) /\
     ~(ptr IN FDOM s.refs) ==>
     bc_next s (bump_pc s with <| stack := (RefPtr ptr)::xs;
                                  refs := s.refs |+ (ptr,x) |>))
  /\
  (!s xs ptr.
     (bc_fetch s = SOME Deref) /\ (s.stack = (RefPtr ptr)::xs) /\
     (ptr IN FDOM s.refs) ==>
     bc_next s (bump_pc s with <| stack := (s.refs ' ptr)::xs |>))
  /\
  (!s x xs ptr.
     (bc_fetch s = SOME Update) /\ (s.stack = x::(RefPtr ptr)::xs) /\
     (ptr IN FDOM s.refs) ==>
     bc_next s (bump_pc s with <| stack := xs ;
                                  refs := s.refs |+ (ptr,x) |>))`;

val _ = export_theory();

