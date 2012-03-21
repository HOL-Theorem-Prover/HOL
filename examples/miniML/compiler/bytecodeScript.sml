open HolKernel boolLib bossLib Parse lcsymtacs
open arithmeticTheory listTheory finite_mapTheory integerTheory
val _ = new_theory "bytecode";
infix \\ val op \\ = op THEN;


(* --- Syntax --- *)

val _ = Hol_datatype `
  bc_stack_op =
    Pop                     (* pop top of stack *)
  | Pops of num             (* pop n elements under stack top *)
  | PushInt of int          (* push num onto stack *)
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
    Number of int                  (* integer *)
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
     if n = 0:num then SOME x else
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
  (bool2num T = 1) /\ (bool2num F = 0:int)`;

val (bc_stack_op_rules,bc_stack_op_ind,bc_stack_op_cases) = Hol_reln `
  bc_stack_op Pop (x::xs) (xs) /\
  bc_stack_op (Pops (LENGTH ys)) (x::ys++xs) (x::xs) /\
  bc_stack_op (PushInt n) (xs) (Number n::xs) /\
  bc_stack_op (Cons tag (LENGTH ys)) (ys ++ xs) (Block tag (REVERSE ys)::xs) /\
  (k < LENGTH xs ==> bc_stack_op (Load k) xs (EL k xs :: xs)) /\
  bc_stack_op (Store (LENGTH ys)) (y::ys ++ x::xs) (ys ++ y::xs) /\
  (k < LENGTH ys ==> bc_stack_op (El k) ((Block tag ys)::xs) (EL k ys::xs)) /\
  bc_stack_op Tag ((Block tag ys)::xs) (Number (&tag)::xs) /\
  bc_stack_op IsNum (x::xs) (Number (bool2num (?n. x = Number n)) :: xs) /\
  bc_stack_op Equal (x2::x1::xs) (Number (bool2num (x1 = x2)) :: xs) /\
  bc_stack_op Less (Number n :: Number m :: xs) (Number (bool2num (m < n))::xs) /\
  bc_stack_op Add (Number n :: Number m :: xs) (Number (m + n)::xs) /\
  bc_stack_op Sub (Number n :: Number m :: xs) (Number (m - n)::xs) /\
  bc_stack_op Mult (Number n :: Number m :: xs) (Number (m * n)::xs) /\
  bc_stack_op Div2 (Number m :: xs) (Number (m / 2)::xs) /\
  bc_stack_op Mod2 (Number m :: xs) (Number (m % 2)::xs)`

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

(* evaluation function *)

val isNumber_def = Define`
  (isNumber (Number _) = T) ∧
  (isNumber _ = F)`
val _ = export_rewrites["isNumber_def"]

val isNumber_exists_thm = store_thm(
"isNumber_exists_thm",
``∀x. isNumber x = ∃n. x = Number n``,
Cases >> rw[]);

val bc_eval_stack_def = Define`
  (bc_eval_stack Pop (x::xs) = SOME xs)
∧ (bc_eval_stack (Pops k) (x::xs) =
   if k ≤ LENGTH xs then SOME (x::(DROP k xs)) else NONE)
∧ (bc_eval_stack (PushInt n) (xs) =
   SOME (Number n::xs))
∧ (bc_eval_stack (Cons tag k) xs =
   if k ≤ LENGTH xs then SOME (Block tag (REVERSE (TAKE k xs))::(DROP k xs)) else NONE)
∧ (bc_eval_stack (Load k) xs =
   if k < LENGTH xs then SOME (EL k xs::xs) else NONE)
∧ (bc_eval_stack (Store k) (y::xs) =
   if k < LENGTH xs ∧ 0 < LENGTH xs
   then SOME (TAKE k xs ++ y :: (DROP (k+1) xs)) else NONE)
∧ (bc_eval_stack (El k) ((Block tag ys)::xs) =
   if k < LENGTH ys then SOME (EL k ys::xs) else NONE)
∧ (bc_eval_stack Tag ((Block tag ys)::xs) =
   SOME (Number (&tag)::xs))
∧ (bc_eval_stack IsNum (x::xs) =
   SOME (Number (bool2num (isNumber x)) :: xs))
∧ (bc_eval_stack Equal (x2::x1::xs) =
   SOME (Number (bool2num (x1 = x2)) :: xs))
∧ (bc_eval_stack Less (Number n :: Number m :: xs) =
   SOME (Number (bool2num (m < n))::xs))
∧ (bc_eval_stack Add (Number n :: Number m :: xs) =
   SOME (Number (m + n)::xs))
∧ (bc_eval_stack Sub (Number n :: Number m :: xs) =
   SOME (Number (m - n)::xs))
∧ (bc_eval_stack Mult (Number n :: Number m :: xs) =
   SOME (Number (m * n)::xs))
∧ (bc_eval_stack Div2 (Number m :: xs) =
   SOME (Number (m / 2)::xs))
∧ (bc_eval_stack Mod2 (Number m :: xs) =
   SOME (Number (m % 2)::xs))
∧ (bc_eval_stack _ _ = NONE)`

val bc_eval_stack_thm1 = prove(
``∀op xs ys. bc_stack_op op xs ys ⇒ (bc_eval_stack op xs = SOME ys)``,
ho_match_mp_tac bc_stack_op_ind >>
rw[bc_eval_stack_def, isNumber_exists_thm,
   rich_listTheory.FIRSTN_LENGTH_APPEND,
   rich_listTheory.BUTFIRSTN_LENGTH_APPEND] >>
srw_tac[ARITH_ss][GSYM arithmeticTheory.ADD1] >>
Induct_on `ys` >>
rw[rich_listTheory.BUTFIRSTN])

val bc_eval_stack_thm2 = prove(
``∀op xs ys. (bc_eval_stack op xs = SOME ys) ⇒ bc_stack_op op xs ys``,
Cases >> Cases >> fs[bc_eval_stack_def,bc_stack_op_cases,isNumber_exists_thm] >> rw[]
>- (
  qmatch_assum_rename_tac `n ≤ LENGTH t` [] >>
  qexists_tac `TAKE n t` >> rw[])
>- (
  qmatch_rename_tac
    `∃(ys:bc_value list).
      (n = LENGTH ys) ∧
      (h::t = ys ++ DROP (n - 1) t) ∧
      (REVERSE (TAKE (n - 1) t) ++ [h] = REVERSE ys)` [] >>
  qexists_tac `TAKE n (h::t)` >> rw[] )
>- (
  qmatch_assum_rename_tac `n < LENGTH t` [] >>
  map_every qexists_tac [`EL n t`,`DROP (n+1) t`,`TAKE n t`] >>
  imp_res_tac arithmeticTheory.LESS_IMP_LESS_OR_EQ >>
  rw[] >>
  qpat_assum `n < LENGTH t` mp_tac >>
  rpt (pop_assum (K ALL_TAC)) >>
  qid_spec_tac `n` >>
  Induct_on `t` >> fs[] >>
  rw[] >> fs[DROP_def] >>
  first_x_assum (qspec_then `n-1` mp_tac) >>
  srw_tac[ARITH_ss][] >>
  Cases_on `n` >> fs[] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack (El n) (h::t) = SOME ys` [] >>
  Cases_on `h` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Tag (h::t) = SOME ys` [] >>
  Cases_on `h` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Equal (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Add (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Sub (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Mult (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Div2 (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Mod2 (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Less (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
)

val bc_eval_stack_thm = store_thm(
"bc_eval_stack_thm",
``∀op xs ys. bc_stack_op op xs ys = (bc_eval_stack op xs = SOME ys)``,
rpt gen_tac >> EQ_TAC >| map (ACCEPT_TAC o SPEC_ALL)
[bc_eval_stack_thm1, bc_eval_stack_thm2])

val bc_eval_stack_NONE = store_thm(
"bc_eval_stack_NONE",
``∀op xs. (bc_eval_stack op xs = NONE) = (∀ys. ¬bc_stack_op op xs ys)``,
PROVE_TAC[bc_eval_stack_thm,
optionTheory.option_CASES,
optionTheory.NOT_SOME_NONE])

val bc_eval1_def = Define`
  bc_eval1 s = OPTION_BIND (bc_fetch s)
  (λx. case (x, s.stack) of
  | (Stack b, _) =>
    OPTION_BIND (bc_eval_stack b s.stack)
      (λys. SOME (bump_pc s with stack := ys))
  | (Jump n, _) => SOME (s with pc := n)
  | (JumpNil n, x::xs) =>
      let s' = s with stack := xs in
        SOME (if x = Number 0 then bump_pc s' else s' with pc := n)
  | (Call n, x::xs) =>
      SOME (s with <| pc := n; stack := x :: CodePtr ((bump_pc s).pc) :: xs |>)
  | (CallPtr, CodePtr ptr::x::xs) =>
      SOME (s with <| pc := ptr; stack := x :: CodePtr ((bump_pc s).pc) :: xs |>)
  | (JumpPtr, CodePtr ptr::xs) =>
     SOME (s with <| pc := ptr; stack := xs |>)
  | (Return, x :: CodePtr n :: xs) =>
     SOME (s with <| pc := n; stack := x::xs |>)
  | (Ref, x::xs) =>
     let ptr = LEAST n. n ∉ (FDOM s.refs) in
     SOME (bump_pc s with <| stack := (RefPtr ptr)::xs;
                             refs := s.refs |+ (ptr,x) |>)
  | (Deref, (RefPtr ptr)::xs) =>
      if (ptr IN FDOM s.refs) then
        SOME (bump_pc s with <| stack := (s.refs ' ptr)::xs |>)
      else NONE
  | (Update, x::(RefPtr ptr)::xs) =>
      if (ptr IN FDOM s.refs) then
        SOME (bump_pc s with <| stack := xs ;
                                refs := s.refs |+ (ptr,x) |>)
      else NONE
  | _ => NONE)`

val bc_eval1_SOME = store_thm(
"bc_eval1_SOME",
``∀s1 s2. (bc_eval1 s1 = SOME s2) ⇒ bc_next s1 s2``,
rw[bc_eval1_def] >>
qmatch_assum_rename_tac `bc_fetch s1 = SOME inst` [] >>
Cases_on `inst` >> fs[GSYM bc_eval_stack_thm]
>- rw[bc_next_rules]
>- rw[bc_next_rules]
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `h` >> fs[] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `h` >> Cases_on `t` >> fs[] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `t` >> fs [] >>
  qmatch_assum_rename_tac `s1.stack = x::y::t` [] >>
  Cases_on `y` >> fs [] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] >>
  numLib.LEAST_ELIM_TAC >>
  rw[] >- (
    match_mp_tac (
      SIMP_RULE (srw_ss()) []
        (INST_TYPE [alpha|->numSyntax.num] pred_setTheory.NOT_IN_FINITE)) >> rw[] ) >>
  qexists_tac `n` >> rw[] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `h` >> fs[] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `t` >> fs [] >>
  qmatch_assum_rename_tac `s1.stack = x::y::t` [] >>
  Cases_on `y` >> fs [] >>
  rw[bc_next_cases] ))

val bc_eval1_NONE = store_thm(
"bc_eval1_NONE",
``∀s1 s2. (bc_eval1 s1 = NONE) ⇒ ¬bc_next s1 s2``,
rw[bc_eval1_def] >- ( rw[bc_next_cases] ) >>
qmatch_assum_rename_tac `bc_fetch s1 = SOME inst` [] >>
Cases_on `inst` >> fs[bc_eval_stack_NONE]
>- rw[bc_next_cases]
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `h` >> fs[] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `h` >> Cases_on `t` >> fs[] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `t` >> fs[] >>
  qmatch_assum_rename_tac `s1.stack = x::y::t` [] >>
  Cases_on `y` >> fs[] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `h` >> fs[] >>
  Cases_on `n=ptr` >> fs[] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `t` >> fs[] >>
  qmatch_assum_rename_tac `s1.stack = x::y::t` [] >>
  Cases_on `y` >> fs[] >>
  Cases_on `n = ptr` >> rw[])
)

val bc_eval_exists = prove(
``∃bc_eval. ∀s. bc_eval s = case bc_eval1 s of NONE => s | SOME s => bc_eval s``,
qexists_tac `λs. WHILE (IS_SOME o bc_eval1) (THE o bc_eval1) s` >>
rw[] >>
Cases_on `bc_eval1 s` >>
rw[Once whileTheory.WHILE])
val bc_eval_def = new_specification("bc_eval_def",["bc_eval"],bc_eval_exists)

val _ = export_theory();
