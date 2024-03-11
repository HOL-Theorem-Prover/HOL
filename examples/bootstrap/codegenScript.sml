
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory source_syntaxTheory x64asm_syntaxTheory;
open parsingTheory wordsLib;

val _ = new_theory "codegen";

(* we return lists with explicit appends to avoid "bad append" performance *)

Datatype:
  app_list = List ('a list) | Append app_list app_list
End

Definition flatten_def:
  flatten (List xs) acc = xs ++ acc ∧
  flatten (Append l1 l2) acc = flatten l1 (flatten l2 acc)
End

(* initialization code *)

Definition init_def:
  init k = (*  0 *) [Const RAX 0w;
           (*  1 *)  Const R12 16w;
           (*  2 *)  Const R13 (n2w (2 ** 63 - 1));
           (* jump to main function *)
           (*  3 *)  Call k;
           (* return to exit 0 *)
           (*  4 *)  Const RDI 0w;
           (*  5 *)  Exit;
           (* alloc routine starts here: *)
           (*  6 *)  Comment "cons";
           (*  7 *)  Jump (Equal R14 R15) 14;
           (*  8 *)  Store RDI R14 0w;
           (*  9 *)  Store RAX R14 8w;
           (* 10 *)  Mov RAX R14;
           (* 11 *)  Add R14 R12;
           (* 12 *)  Ret;
           (* give up: *)
           (* 13 *)  Comment "exit 1";
           (* 14 *)  Push R15;
           (* 15 *)  Const RDI 1w;
           (* 16 *)  Exit]
End

Overload AllocLoc[inferior] = “7:num”;

(* Naming conventions:
    - prefix "c_" is used to mean "compile"
    - argument names:
       t - boolean indicating tail position (true if in tail position)
       l - location where the next instruction will be placed in memory
           (relative to first instruction of the entire program)
       vs - a model of the stack: the ith element is SOME v if the value
            of source variable v is at stack index i; positions containing
            NONE do not correspond to a source-level variable; this information
            is used by when compiling Var (in the c_var function)
       fs - an a-list with locations for all the function locations,
            compilation of Call (in c_exp) uses this information
*)

Definition even_len_def:
  even_len [] = T ∧
  even_len (x::xs) = odd_len xs ∧
  odd_len [] = F ∧
  odd_len (x::xs) = even_len xs
End

Definition give_up_def[simp]:
  give_up b = if b then 14:num else 15
End

Definition c_const_def:
  c_const l n vs = if 2**63-1 < n
                   then (List [Jump Always (give_up (odd_len vs))], l+1)
                   else (List [Push RAX; Const RAX (n2w n)], l+2)
End

Definition find_def:
  find n [] k = k ∧
  find n (NONE::vs) k = find n vs (k+1) ∧
  find n (SOME v::vs) k = if v = (n:num) then k else find n vs (k+1)
End

Definition c_var_def:
  c_var l n vs =
    let k = find n vs 0 in
      if k = 0 then (List [Push RAX], l+1) else
        (List [Push RAX; Load_RSP RAX k], l+2)
End

Definition c_add_def:
  c_add vs = [Pop RDI; Add RAX RDI; Jump (Less R13 RAX) (give_up (even_len vs))]
End

Definition c_sub_def:
  c_sub l = [Pop RDI;
             Jump (Less RAX RDI) (l+3); (* i.e. skip the next instruction *)
             Mov RAX RDI;
             Sub RDI RAX;
             Mov RAX RDI]
End

Definition c_div_def:
  c_div = [Mov RDI RAX;
           Pop RAX;
           Const RDX 0w;
           Div RDI]
End

Definition c_cons_def:
  c_cons vs = if even_len vs (* stack must be aligned at call *)
              then [Load_RSP RDI 0; Call AllocLoc; Pop RDI]
              else [Pop RDI; Call AllocLoc]
End

Definition c_head_def:
  c_head = [Load RAX RAX 0w]
End

Definition c_tail_def:
  c_tail = [Load RAX RAX 8w]
End

Definition align_def:
  align b cs = if b then [Push RAX]++cs++[Pop RDI] else cs
End

Definition c_read_def:
  c_read vs = align (even_len vs) [Push RAX; GetChar]
End

Definition c_write_def:
  c_write vs = align (even_len vs) [Mov RDI RAX; PutChar; Const RAX 0w]
End

Definition c_op_def:
  c_op Add vs l = c_add vs ∧
  c_op Sub vs l = c_sub l ∧
  c_op Div vs l = c_div ∧
  c_op Cons vs l = c_cons vs ∧
  c_op Head vs l = c_head ∧
  c_op Tail vs l = c_tail ∧
  c_op Read vs l = c_read vs ∧
  c_op Write vs l = c_write vs
End

Definition c_test_def:
  c_test (c:source_syntax$test) target =
    let cond = (case c of Equal => Equal RDI RBX | Less => Less RDI RBX) in
      [Mov RBX RAX; Pop RDI; Pop RAX; Jump cond target]
End

Definition c_if_def:
  c_if t test (c1,l1) (c2,l2) (c3,l3) =
    (Append c1 (Append (List (c_test test (l2 + if t then 0 else 1)))
               (Append c2 (Append (List (if t then [] else [Jump Always l3])) c3))),l3)
End

Definition c_pops_def:
  c_pops xs vs =
    let k = LENGTH xs in
      if k = 0 then [Push RAX] else
      if k = 1 then [] else
      if k = 2 then [Pop RDI] else
      if k = 3 then [Pop RDI; Pop RDX] else
      if k = 4 then [Pop RDI; Pop RDX; Pop RBX] else
      if k = 5 then [Pop RDI; Pop RDX; Pop RBX; Pop RBP] else
      otherwise [Jump Always (give_up (odd_len xs ≠ odd_len vs))]
End

Definition call_env_def:
  call_env [] acc = acc ∧
  call_env (x::xs) acc = call_env xs (SOME x :: acc)
End

Definition c_pushes_def:
  c_pushes vs l =
    let k = LENGTH vs in
    let e = call_env vs [] in
      if k = 0 then (List [], [NONE], l) else
      if k = 1 then (List [],e,l) else
      if k = 2 then (List [Push RDI],e,l + 1) else
      if k = 3 then (List [Push RDX; Push RDI],e,l + 2) else
      if k = 4 then (List [Push RBX; Push RDX; Push RDI],e,l + 3) else
          otherwise (List [Push RBP; Push RBX; Push RDX; Push RDI],e,l + 4)
End

Definition c_call_def:
  c_call t vs target xs (c,l) =
    let ys = c_pops xs vs in
      if t then
        (Append c (Append (List ys)
          (List [Add_RSP (LENGTH vs); Jump Always target])), l + LENGTH ys + 2)
      else
        let cs = align (even_len vs) [Call target] in
          (Append c (Append (List ys) (List cs)), l + LENGTH ys + LENGTH cs)
End

Definition lookup_def:
  lookup n [] = 0 ∧
  lookup n ((x,y)::xs) = if x = (n:num) then y else lookup n xs
End

Definition make_ret_def:
  make_ret vs (c,l) =
    (Append c (List [Add_RSP (LENGTH vs); Ret]), l + 2)
End

Definition c_exp_def:
  c_exp t l vs fs z =
    (if t then
       case z of
       | Let n x y =>
           (let r1 = c_exp F l vs fs x in
            let r2 = c_exp T (SND r1) (SOME n::vs) fs y in
              (Append (FST r1) (Append (FST r2) (List [])), SND r2))
       | If cmp xs y z =>
           (let r1 = c_exps l vs fs xs in
            let r2 = c_exp T (SND r1 + 4) vs fs z in
            let r3 = c_exp T (SND r2) vs fs y in
              c_if T cmp r1 r2 r3)
       | Call n xs =>
           (c_call T vs (lookup n fs) xs (c_exps l vs fs xs))
       | _ => make_ret vs (c_exp F l vs fs z)
     else
       case z of
       | Let n x y =>
           (let r1 = c_exp F l vs fs x in
            let r2 = c_exp F (SND r1) (SOME n::vs) fs y in
              (Append (FST r1) (Append (FST r2) (List [Add_RSP 1])),SND r2+1))
       | If cmp xs y z =>
           (let r1 = c_exps l vs fs xs in
            let r2 = c_exp F (SND r1 + 4) vs fs z in
            let r3 = c_exp F (SND r2 + 1) vs fs y in
              c_if F cmp r1 r2 r3)
       | Call n xs =>
           (c_call F vs (lookup n fs) xs (c_exps l vs fs xs))
       | Const n => c_const l n vs
       | Var n => c_var l n vs
       | Op op xs =>
           (let r1 = c_exps l vs fs xs in
            let insts = c_op op vs (SND r1) in
              (Append (FST r1) (List insts), SND r1 + LENGTH insts))) ∧
  c_exps l vs fs zs =
    case zs of
    | [] => (List [],l)
    | (x::xs) => (let res1 = c_exp F l vs fs x in
                  let res2 = c_exps (SND res1) (NONE::vs) fs xs in
                    (Append (FST res1) (FST res2), SND res2))
Termination
  WF_REL_TAC ‘inv_image (measure I LEX measure I)
    (λx. case x of INL (t,l,vs,fs,x) => (exp_size x,if t then 1 else 0)
                 | INR (l,vs,fs,xs) => (exp1_size xs,0))’
End

Definition c_exp'_def: (* rephrasing that is better for proofs *)
  c_exp' t l vs fs (Let n x y) =
    (let (c1,l') = c_exp' F l vs fs x in
     let (c2,l'') = c_exp' t l' (SOME n::vs) fs y in
       (Append c1 (Append c2 (List (if t then [] else [Add_RSP 1]))),
        if t then l'' else l'' + 1)) ∧
  c_exp' t l vs fs (If test xs y z) =
    (let (c1,l1) = c_exps' l vs fs xs in
     let (c2,l2) = c_exp' t (l1 + 4) vs fs z in
     let (c3,l3) = c_exp' t (l2 + if t then 0 else 1) vs fs y in
       c_if t test (c1,l1) (c2,l2) (c3,l3)) ∧
  c_exp' t l vs fs (Call n xs) =
    c_call t vs (lookup n fs) xs (c_exps' l vs fs xs) ∧
  c_exp' F l vs fs (Const n) = c_const l n vs ∧
  c_exp' F l vs fs (Var n) = c_var l n vs ∧
  c_exp' F l vs fs (Op op xs) =
    (let (c,l0) = c_exps' l vs fs xs in
     let insts = c_op op vs l0 in
       (Append c (List insts),l0 + LENGTH insts)) ∧
  c_exp' T l vs fs (Const v10) = make_ret vs (c_exp' F l vs fs (Const v10)) ∧
  c_exp' T l vs fs (Var v11) = make_ret vs (c_exp' F l vs fs (Var v11)) ∧
  c_exp' T l vs fs (Op op xs) = make_ret vs (c_exp' F l vs fs (Op op xs)) ∧
  c_exps' l vs fs [] = (List [],l) ∧
  c_exps' l vs fs (x::xs) =
    (let (c1,l') = c_exp' F l vs fs x in
     let (c2,l'') = c_exps' l' (NONE::vs) fs xs in
      (Append c1 c2,l''))
Termination
  WF_REL_TAC ‘inv_image (measure I LEX measure I)
    (λx. case x of INL (t,l,vs,fs,x) => (exp_size x,if t then 1 else 0)
                 | INR (l,vs,fs,xs) => (exp1_size xs,0))’
End

Theorem c_exp'[simp]:
  c_exp' = c_exp ∧ c_exps' = c_exps
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [FUN_EQ_THM] \\ ho_match_mp_tac c_exp'_ind \\ rw []
  \\ fs [c_exp'_def] \\ rw [Once c_exp_def] \\ rpt (pairarg_tac \\ fs [])
QED

Theorem c_exp_alt = c_exp'_def |> SIMP_RULE (srw_ss()) []
Theorem c_exp_ind_alt = c_exp'_ind |> SIMP_RULE (srw_ss()) []

Definition c_defun_def:
  c_defun l (fs:(num # num) list) (Defun n vs body) =
    let (c0,vs0,l0) = c_pushes vs l in
    let (c1,l1) = c_exp T l0 vs0 fs body in
      (Append c0 c1,l1)
End

Definition name_of_def:
  name_of (Defun n _ _) = n
End

Definition name2str_def:
  name2str n acc =
    if n = 0 then acc else name2str (n DIV 256) (CHR (n MOD 256) :: acc)
End

Definition c_decs_def:
  c_decs l fs [] = (List [],[],l) ∧
  c_decs l fs (d::ds) =
    let fname = name_of d in
    let comment = List [Comment (name2str fname [])] in
    let r1 = c_defun (l+1) fs d in
    let r2 = c_decs (SND r1) fs ds in
      (Append comment (Append (FST r1) (FST r2)),
       (fname,l+1)::(FST (SND r2)),
       SND (SND r2))
End

Definition codegen_def:
  codegen (Program funs main) =
    let init_l = LENGTH (init 0) in
    let (_,fs,k) = c_decs init_l [] funs in
    let (c,fs,_) = c_decs init_l fs (funs ++ [Defun (name "main") [] main]) in
      flatten (Append (List (init (k+1))) c) []
End

Definition compiler_def:
  compiler input =
    asm2str (codegen (parser (lexer input)))
End

val _ = export_theory();
