open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_compiler";
val _ = ParseExtras.temp_loose_equality()

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory pairTheory;

open lisp_bytecodeTheory;
open lisp_sexpTheory lisp_semanticsTheory lisp_alt_semanticsTheory

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val bool_ss = bool_ss -* ["lift_disj_eq", "lift_imp_disj"]
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]


(* relation defines translation of programs into bytecode *)

val _ = Hol_datatype`
  stack_slot = ssTEMP
             | ssVAR of string`;

val stack_slot_11 = fetch "-" "stack_slot_11"
val stack_slot_distinct = fetch "-" "stack_slot_distinct"
val stack_slot = simpLib.type_ssfrag ``:stack_slot``

val _ = Hol_datatype `
  bc_state = <| code : num -> bc_inst_type option ;
                code_end : num;
                compiled : (string # (num # num)) list ; (* this is an alist *)
                instr_length : bc_inst_type -> num ;
                consts : SExp list ;
                io_out : string ;
                ok : bool |>`;

val iLENGTH_def = Define `
  (iLENGTH il [] = 0) /\
  (iLENGTH il (x::xs) = il (x:bc_inst_type) + iLENGTH il xs)`;

val iLENGTH_APPEND = prove(
  ``!xs ys il. iLENGTH il (xs ++ ys) = iLENGTH il xs + iLENGTH il ys``,
  Induct \\ SRW_TAC [] [iLENGTH_def,ADD_ASSOC]);

val var_lookup_def = Define `
  (var_lookup n v [] = NONE) /\
  (var_lookup n v (x::xs) = if x = ssVAR v then SOME n else var_lookup (n+1:num) v xs)`;

val gen_pops_def = Define `
  gen_pops n = if n = 0 then [] else [iPOPS n]`;

val gen_popn_def = Define `
  gen_popn n = if n = 0 then [] else gen_pops (n-1) ++ [iPOP]`;

val n_times_def = Define `
  (n_times 0 x = []) /\
  (n_times (SUC n) x = x::n_times n x)`;

val BC_return_code_def = Define `
  (BC_return_code F a = []) /\
  (BC_return_code T a = gen_pops (LENGTH a - 1) ++ [iRETURN])`;

val BC_return_def = Define `
  BC_return ret (code,a:stack_slot list,q,bc) =
    (code ++ BC_return_code ret a,a,
     q + iLENGTH bc.instr_length (code ++ BC_return_code ret a),bc)`;

val BC_call_aux_def = Define `
  (BC_call_aux F (fc,n,SOME pos) = [iCALL pos]) /\
  (BC_call_aux T (fc,n,SOME pos) = [iJUMP pos]) /\
  (BC_call_aux F (fc,n,NONE) = [iCONST_NUM n; iCONST_SYM fc; iCALL_SYM]) /\
  (BC_call_aux T (fc,n,NONE) = [iCONST_NUM n; iCONST_SYM fc; iJUMP_SYM])`;

val BC_call_def = Define `
  (BC_call b (fc,n,NONE) = BC_call_aux b (fc,n,NONE)) /\
  (BC_call b (fc,n,SOME (pos,m)) = if m = n then BC_call_aux b (fc,n,SOME pos)
                                            else BC_call_aux b (fc,n,NONE))`;

val BC_ADD_CONST_def = Define `
  BC_ADD_CONST bc x = bc with consts := (bc.consts ++ [x])`;

val BC_FAIL_def = Define `
  BC_FAIL bc = bc with ok := F`;

val FUN_LOOKUP_def = Define `
  (FUN_LOOKUP [] name = NONE) /\
  (FUN_LOOKUP ((x,y)::xs) name = if x = name then SOME y else FUN_LOOKUP xs name)`;

val (BC_ev_rules,BC_ev_ind,BC_ev_cases) = Hol_reln `
  (* constant *)
  (!s a ret q bc.
    BC_ev ret (Const s,a,q,bc)
      (BC_return ret (if isVal s then [iCONST_NUM (getVal s)] else
                      if isSym s then [iCONST_SYM (getSym s)] else
                        [iCONST_NUM (LENGTH (bc.consts));iCONST_LOOKUP] ,ssTEMP::a,q,
         if isDot s then BC_ADD_CONST bc s else bc)))
  /\
  (* variable lookup *)
  (!v a ret q bc.
    BC_ev ret (Var v,a,q,bc)
      (BC_return ret (if var_lookup 0 v a = NONE then [iFAIL] else
                        [iLOAD (THE (var_lookup 0 v a))],ssTEMP::a,q,bc)))
  /\
  (* function application *)
  (!xs a q code1 a1 q1 code2 a2 q2 bc bc1 bc2 fc ret.
    BC_evl (xs,a,q,bc) (code1,a1,q1,bc1) /\ ~(isFun fc) /\
    BC_ap ret (fc,LENGTH xs,a1,q1,bc1) (code2,a2,q2,bc2) ==>
    BC_ev ret (App fc xs,a,q,bc) (code1 ++ code2,a2,q2,bc2))
  /\
  (* application of built-in function *)
  (!fc a ret f n1 n2 q bc.
    (EVAL_DATA_OP fc = (f,n1)) ==>
    BC_ap ret (PrimitiveFun fc,n2,a,q,bc)
      (BC_return ret ([if n1 = n2 then iDATA fc else iFAIL],ssTEMP::DROP n2 a,q,bc)))
  /\
  (* normal proc call -- no tail call optimisation possible *)
  (!fc xs a code a2 q q2 bc bc2.
    BC_evl (xs,a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev F (App (Fun fc) xs,a,q,bc)
       (code ++ BC_call F (fc,LENGTH xs,FUN_LOOKUP bc.compiled fc),
        ssTEMP::DROP (LENGTH xs) a2,
        q2 + iLENGTH bc.instr_length (BC_call F (fc,LENGTH xs,FUN_LOOKUP bc.compiled fc)),bc2))
  /\
  (* normal proc call -- with tail call optimisation *)
  (!fc xs a code a2 padding q q2 bc bc2.
    BC_evl (xs,n_times padding ssTEMP ++ a,q + iLENGTH bc.instr_length (n_times padding (iCONST_SYM "NIL")),bc) (code,a2,q2,bc2) /\
    (padding = LENGTH xs - LENGTH a) ==>
    BC_ev T (App (Fun fc) xs,a,q,bc)
      (n_times padding (iCONST_SYM "NIL") ++ code ++
       n_times (LENGTH xs) (iSTORE (LENGTH a + padding - 1)) ++
       gen_popn (LENGTH a - LENGTH xs) ++ BC_call T (fc,LENGTH xs,FUN_LOOKUP bc.compiled fc),[],
       q2 + iLENGTH bc.instr_length (n_times (LENGTH xs) (iSTORE (LENGTH a + padding - 1)) ++
       gen_popn (LENGTH a - LENGTH xs) ++ BC_call T (fc,LENGTH xs,FUN_LOOKUP bc.compiled fc)),bc2))
  /\
  (* if then else *)
  (!a x y z x_code y_code z_code a1 a2 a3 ret q q1 q2 q3 bc bc1 bc2 bc3.
    BC_ev F (x,a,q,bc) (x_code,a1,q1,bc1) /\
    BC_ev ret (y,a,q1+bc.instr_length(iJNIL (q2+bc.instr_length(iJUMP q3))),bc1) (y_code,a2,q2,bc2) /\
    BC_ev ret (z,a,q2+bc.instr_length(iJUMP q3),bc2) (z_code,a3,q3,bc3) ==>
    BC_ev ret (If x y z,a,q,bc) (x_code ++ [iJNIL (q2+bc.instr_length(iJUMP q3))] ++
                                  y_code ++ [iJUMP q3] ++
                                  z_code,ssTEMP::a,q3,bc3))
  /\
  (* or -- base case *)
  (!ret a q bc code a2 q2 bc2.
    BC_ev ret (Const (Sym "NIL"),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (Or [],a,q,bc) (code,a2,q2,bc2))
  /\
  (* or -- step case *)
  (!a x_code z_code a1 a3 ret q q1 q3 bc bc1 bc3 t ts addr.
    BC_ev F (t,a,q,bc) (x_code,a1,q1,bc1) /\
    (addr = iLENGTH bc.instr_length (x_code ++ [iLOAD 0; iJNIL (q+addr)] ++
                                     BC_return_code ret (ssTEMP::a) ++ [iJUMP q3])) /\
    BC_ev ret (Or ts,a,q1 + iLENGTH bc.instr_length ([iLOAD 0; iJNIL (q+addr)] ++ BC_return_code ret (ssTEMP::a) ++ [iJUMP q3; iPOP]),bc1) (z_code,a3,q3,bc3) ==>
    BC_ev ret (Or (t::ts),a,q,bc) (x_code ++ [iLOAD 0; iJNIL (q+addr)] ++
                                   BC_return_code ret (ssTEMP::a) ++ [iJUMP q3; iPOP] ++
                                   z_code,ssTEMP::a,q3,bc3))
  /\
  (* let *)
  (!a x xs ys code1 code2 a1 a2 ret q q1 q2 bc bc1 bc2.
    BC_evl (ys,a,q,bc) (code1,a1,q1,bc1) /\
    BC_ev ret (x,MAP (ssVAR) (REVERSE xs) ++ DROP (LENGTH xs) a1,q1,bc1) (code2,a2,q2,bc2) ==>
    BC_ev ret (LamApp xs x ys,a,q,bc)
      (code1 ++ code2 ++ if ret then [] else [iPOPS (LENGTH xs)],ssTEMP::a,
                         if ret then q2 else q2+bc.instr_length(iPOPS (LENGTH xs)),bc2))
  /\
  (* print *)
  (!a ret n q bc.
    BC_ap ret (Print,n,a,q,bc)
      (BC_return ret ([iCONST_SYM "NIL"] ++ n_times n (iDATA opCONS) ++
                      [iCONST_SYM "PRINT"; iLOAD 1; iDATA opCONS; iPRINT; iCONST_SYM "NIL"; iPOPS 2],ssTEMP::DROP n a,q,bc)))
  /\
  (* error *)
  (!a ret n q bc.
    BC_ap ret (Error,n,a,q,bc)
      (BC_return ret ([iCONST_SYM "NIL"] ++ n_times n (iDATA opCONS) ++
                      [iCONST_SYM "ERROR"; iLOAD 1; iDATA opCONS; iPRINT; iFAIL],ssTEMP::DROP n a,q,bc)))
  /\
  (* define *)
  (!a ret n q bc.
    BC_ap ret (Define,n,a,q,bc)
      (BC_return ret ([iCOMPILE],ssTEMP::DROP n a,q,bc)))
  /\
  (* funcall *)
  (!a ret n q bc.
    BC_ap ret (Funcall,n,a,q,bc)
      (BC_return ret ([iCONST_NUM (n-1); iLOAD n; iCALL_SYM; iPOPS 1],ssTEMP::DROP n a,q,bc)))
  /\
  (* list, base case *)
  (!a q bc.
    BC_evl ([],a,q,bc) ([],a,q,bc))
  /\
  (* list, step case *)
  (!a x xs q q2 q3 a2 a3 code code2 bc bc2 bc3.
    BC_ev F (x,a,q,bc) (code,a2,q2,bc2) /\
    BC_evl (xs,a2,q2,bc2) (code2,a3,q3,bc3) ==>
    BC_evl (x::xs,a,q,bc) (code ++ code2,a3,q3,bc3))
  /\

  (* only macros below *)

  (!ret e a q bc code a2 q2 bc2.
    BC_ev ret (App (PrimitiveFun opCAR) [e],a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (First e,a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret e a q bc code a2 q2 bc2.
    BC_ev ret (First (App (PrimitiveFun opCDR) [e]),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (Second e,a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret e a q bc code a2 q2 bc2.
    BC_ev ret (Second (App (PrimitiveFun opCDR) [e]),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (Third e,a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret e a q bc code a2 q2 bc2.
    BC_ev ret (Third (App (PrimitiveFun opCDR) [e]),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (Fourth e,a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret e a q bc code a2 q2 bc2.
    BC_ev ret (Fourth (App (PrimitiveFun opCDR) [e]),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (Fifth e,a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret zs x a q bc code a2 q2 bc2.
    BC_ev ret (LamApp (MAP FST zs) x (MAP SND zs),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (Let zs x,a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret x a q bc code a2 q2 bc2.
    BC_ev ret (x,a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (LetStar [] x,a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret z zs x a q bc code a2 q2 bc2.
    BC_ev ret (Let [z] (LetStar zs x),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (LetStar (z::zs) x,a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret a q bc code a2 q2 bc2.
    BC_ev ret (Const (Sym "NIL"),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (Cond [],a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret x1 x2 qs a q bc code a2 q2 bc2.
    BC_ev ret (If x1 x2 (Cond qs),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (Cond ((x1,x2)::qs),a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret a q bc code a2 q2 bc2.
    BC_ev ret (Const (Sym "T"),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (And [],a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret a q bc code a2 q2 bc2.
    BC_ev ret (Const (Sym "NIL"),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (List [],a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret t a q bc code a2 q2 bc2.
    BC_ev ret (t,a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (And [t],a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret t1 t2 ts a q bc code a2 q2 bc2.
    BC_ev ret (If t1 (And (t2::ts)) (Const (Sym "NIL")),a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (And (t1::t2::ts),a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret t ts a q bc code a2 q2 bc2.
    BC_ev ret (App (PrimitiveFun opCONS) [t;List ts],a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (List (t::ts),a,q,bc) (code,a2,q2,bc2))
  /\
  (!ret code fname ps body a q bc a2 q2 bc2.
    BC_ev ret (App Define [Const (Sym fname); Const (list2sexp (MAP Sym ps)); Const body],a,q,bc) (code,a2,q2,bc2) ==>
    BC_ev ret (Defun fname ps body,a,q,bc) (code,a2,q2,bc2))`;


val PULL_EXISTS_IMP = METIS_PROVE [] ``((?x. P x) ==> Q) = (!x. P x ==> Q)``;
val PULL_FORALL_IMP = METIS_PROVE [] ``(Q ==> !x. P x) = (!x. Q ==> P x)``;

val BC_JUMPS_OK_def = Define `
  BC_JUMPS_OK bc =
    (!a. bc.instr_length (iJUMP a) = bc.instr_length (iJUMP 0)) /\
    (!a. bc.instr_length (iJNIL a) = bc.instr_length (iJNIL 0))`;

val BC_CODE_OK_def = Define `
  BC_CODE_OK bc =
    (!h. 0 < bc.instr_length h) /\
    (!a. bc.instr_length (iJUMP a) = bc.instr_length (iJUMP 0)) /\
    (!a. bc.instr_length (iJNIL a) = bc.instr_length (iJNIL 0)) /\
    !i. bc.code_end <= i ==> (bc.code i = NONE)`;

val NOT_isFun = prove(
  ``!fc. ~isFun fc = !f. ~(fc = Fun f)``,
  Cases \\ SIMP_TAC (srw_ss()) [isFun_def]);

val BC_JUMPS_OK_BC_ADD_CONST = prove(
  ``!bc s. BC_JUMPS_OK (BC_ADD_CONST bc s) = BC_JUMPS_OK bc``,
  EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

fun STRIP_NOT_CONJ_TAC (h,goal) =
  if not (is_conj goal) then STRIP_TAC (h,goal) else NO_TAC (h,goal)

val DET_TAC =
    FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_NOT_CONJ_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) [BC_return_def]
    \\ REPEAT STRIP_NOT_CONJ_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss []

val DET2_TAC =
    FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_NOT_CONJ_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) [BC_return_def]
    \\ FULL_SIMP_TAC std_ss [NOT_isFun] \\ METIS_TAC [BC_JUMPS_OK_BC_ADD_CONST]

local
  val BC_ev_DET_ind = BC_ev_ind
    |> Q.SPEC `\ret (x1,x2,x3,x4,bc) z. !z1 z2 z3 z4. BC_JUMPS_OK bc /\ BC_ap ret (x1,x2,x3,x4,bc) (z1,z2,z3,z4) ==> (z = (z1,z2,z3,z4)) /\ BC_JUMPS_OK z4`
    |> Q.SPEC `\(x1,x2,x3,bc) z. !z1 z2 z3 z4. BC_JUMPS_OK bc /\ BC_evl (x1,x2,x3,bc) (z1,z2,z3,z4) ==> (z = (z1,z2,z3,z4)) /\ BC_JUMPS_OK z4`
    |> Q.SPEC `\ret (x1,x2,x3,bc) z. !z1 z2 z3 z4. BC_JUMPS_OK bc /\ BC_ev ret (x1,x2,x3,bc) (z1,z2,z3,z4) ==> (z = (z1,z2,z3,z4)) /\ BC_JUMPS_OK z4`
  val goal = BC_ev_DET_ind |> concl |> dest_imp |> snd;
  val BC_ev_DET_lemma = prove(goal,
  MATCH_MP_TAC BC_ev_DET_ind
  \\ STRIP_TAC THEN1 DET2_TAC
  \\ STRIP_TAC THEN1 DET_TAC
  \\ STRIP_TAC THEN1 DET2_TAC
  \\ STRIP_TAC THEN1 DET2_TAC
  \\ STRIP_TAC THEN1 DET2_TAC
  \\ STRIP_TAC THEN1 DET2_TAC
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_NOT_CONJ_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) [BC_return_def]
    \\ Q.PAT_X_ASSUM `BC_JUMPS_OK bc` (fn th =>
         ASSUME_TAC th THEN ASSUME_TAC (RW [BC_JUMPS_OK_def] th))
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ STRIP_TAC THEN1 DET2_TAC
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_NOT_CONJ_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) [BC_return_def]
    \\ Q.PAT_X_ASSUM `BC_JUMPS_OK bc` (fn th =>
         ASSUME_TAC th THEN ASSUME_TAC (RW [BC_JUMPS_OK_def] th))
    \\ FULL_SIMP_TAC std_ss [iLENGTH_def,iLENGTH_APPEND]
    \\ REPEAT STRIP_NOT_CONJ_TAC \\ FULL_SIMP_TAC std_ss []
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [ADD_ASSOC] \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ REPEAT (STRIP_TAC THEN1 DET_TAC))
in
  val BC_ev_DETERMINISTIC = store_thm("BC_ev_DETERMINISTIC",
    ``!t a q bc y z.
        BC_CODE_OK bc ==>
        BC_ev T (t,a,q,bc) y /\ BC_ev T (t,a,q,bc) z ==> (y = z)``,
    FULL_SIMP_TAC std_ss [FORALL_PROD] \\ REPEAT STRIP_NOT_CONJ_TAC
    \\ `BC_JUMPS_OK bc` by FULL_SIMP_TAC std_ss [BC_JUMPS_OK_def,BC_CODE_OK_def]
    \\ IMP_RES_TAC (SIMP_RULE std_ss [FORALL_PROD] BC_ev_DET_lemma)
    \\ METIS_TAC [])
end;



val SUM_def = Define `
  (SUM [] = 0) /\
  (SUM (x::xs) = x + SUM xs)`;

val MEM_term_size5 = prove(
  ``!ts a. MEM a ts ==> term_size a < term5_size ts``,
  Induct \\ SIMP_TAC std_ss [MEM,term_size_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val MEM_term_size3 = prove(
  ``!ts a b. MEM (a,b) ts ==> term_size a < term3_size ts /\
                              term_size b < term3_size ts``,
  Induct \\ SIMP_TAC std_ss [MEM,term_size_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [term_size_def] \\ DECIDE_TAC);

val MEM_term_size1 = prove(
  ``!ts a b. MEM (a,b) ts ==> term_size b < term1_size ts``,
  Induct \\ SIMP_TAC std_ss [MEM,term_size_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [term_size_def] \\ DECIDE_TAC);

val term_depth_def = tDefine "term_depth" `
  (term_depth (Const _) = 1) /\
  (term_depth (Var _) = 1) /\
  (term_depth (App _ xs) = 1 + SUM (MAP term_depth xs)) /\
  (term_depth (If x y z) = 1 + term_depth x + term_depth y + term_depth z) /\
  (term_depth (LamApp _ y xs) = 1 + term_depth y + SUM (MAP term_depth xs)) /\
  (term_depth (Let ys x) = 10 + term_depth x + SUM (MAP (\(x,y). term_depth y) ys)) /\
  (term_depth (LetStar ys x) = 10 + term_depth x + SUM (MAP (\(x,y). term_depth y) ys) + 100 * LENGTH ys) /\
  (term_depth (Cond qs) = 10 + LENGTH qs + SUM (MAP (\(x,y). term_depth x + term_depth y) qs) + 20 * LENGTH qs) /\
  (term_depth (Or ts) = 10 + SUM (MAP term_depth ts)) /\
  (term_depth (And ts) = 10 + SUM (MAP term_depth ts)) /\
  (term_depth (List ts) = 10 + SUM (MAP term_depth ts) + 10 * LENGTH ts) /\
  (term_depth (First x) = 10 + term_depth x) /\
  (term_depth (Second x) = 20 + term_depth x) /\
  (term_depth (Third x) = 30 + term_depth x) /\
  (term_depth (Fourth x) = 40 + term_depth x) /\
  (term_depth (Fifth x) = 50 + term_depth x) /\
  (term_depth (Defun _ _ _) = 10)`
 (WF_REL_TAC `measure (term_size)` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC MEM_term_size5 \\ IMP_RES_TAC MEM_term_size1
  \\ IMP_RES_TAC MEM_term_size3 \\ REPEAT DECIDE_TAC);

val ZERO_LT_term_depth = prove(
  ``!x. 0 < term_depth x``,
  Cases \\ EVAL_TAC \\ DECIDE_TAC);

val IMP_BC_evl_EXISTS = prove(
  ``!l a q bc.
      (!t ret a q bc.
        MEM t l /\ BC_JUMPS_OK bc ==>
        ?y1 y2 y3 bc1.
          BC_ev ret (t,a,q,bc) (y1,y2,y3,bc1) /\ BC_JUMPS_OK bc1) /\
      BC_JUMPS_OK bc ==>
      ?y1 y2 y3 bc1.
          BC_evl (l,a,q,bc) (y1,y2,y3,bc1) /\ BC_JUMPS_OK bc1``,
  Induct \\ FULL_SIMP_TAC std_ss [FORALL_PROD] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [MEM] \\ FULL_SIMP_TAC std_ss [EXISTS_PROD]
  \\ METIS_TAC []);

val MEM_SUM_MAP = prove(
  ``!xs x. MEM x xs ==> term_depth x <= SUM (MAP (\a. term_depth a) xs)``,
  Induct \\ SIMP_TAC std_ss [MEM] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [SUM_def,MAP] \\ DECIDE_TAC);

val BC_ap_cases = BC_ev_cases |> CONJUNCTS |> el 1;

val PULL_EXISTS_CONJ = METIS_PROVE []
  ``((?x. Q x) /\ P = (?x. Q x /\ P)) /\ (P /\ (?x. Q x) = (?x. P /\ Q x))``

val BC_ev_TOTAL_LEMMA = prove(
  ``!ret t a q bc.
      BC_JUMPS_OK bc ==>
      ?y1 y2 y3 bc1. BC_ev ret (t,a,q,bc) (y1,y2,y3,bc1) /\ BC_JUMPS_OK bc1``,
  completeInduct_on `term_depth t`
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO] \\ Cases_on `t`
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) [BC_return_def]
         \\ METIS_TAC [BC_JUMPS_OK_BC_ADD_CONST])
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) [BC_return_def])
  THEN1 (`!a q. ?y1 y2 y3 bc1.
            BC_evl (l,a,q,bc) (y1,y2,y3,bc1) /\ BC_JUMPS_OK bc1` by
          (REPEAT STRIP_TAC \\ MATCH_MP_TAC IMP_BC_evl_EXISTS \\ ASM_SIMP_TAC std_ss []
           \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!tttt.bbb` MATCH_MP_TAC
           \\ ASM_SIMP_TAC std_ss [term_depth_def]
           \\ IMP_RES_TAC MEM_SUM_MAP \\ DECIDE_TAC)
         \\ Cases_on `isFun f` THEN1
          (Cases_on `f` \\ FULL_SIMP_TAC std_ss [isFun_def] \\ Cases_on `ret`
           \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) [isFun_def]
           \\ FULL_SIMP_TAC std_ss [FORALL_PROD,EXISTS_PROD] \\ METIS_TAC [])
         \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) [isFun_def]
         \\ Cases_on `f` \\ FULL_SIMP_TAC (srw_ss()) [isFun_def]
         \\ SIMP_TAC (srw_ss()) [Once BC_ap_cases,BC_return_def]
         \\ FULL_SIMP_TAC std_ss [PULL_EXISTS_CONJ]
         \\ Cases_on `EVAL_DATA_OP l'` \\ FULL_SIMP_TAC std_ss []
         \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD,term_depth_def,PULL_EXISTS_CONJ]
         \\ POP_ASSUM (fn th => MP_TAC th THEN ASSUME_TAC (RW [BC_JUMPS_OK_def] th))
         \\ FULL_SIMP_TAC std_ss []
         \\ `term_depth t' < 1 + term_depth t' + term_depth t0 + term_depth t1` by DECIDE_TAC
         \\ `term_depth t0 < 1 + term_depth t' + term_depth t0 + term_depth t1` by DECIDE_TAC
         \\ `term_depth t1 < 1 + term_depth t' + term_depth t0 + term_depth t1` by DECIDE_TAC
         \\ RES_TAC \\ METIS_TAC [])
  THEN1 (`?y1 y2 y3 bc1.
            BC_evl (l,a,q,bc) (y1,y2,y3,bc1) /\ BC_JUMPS_OK bc1` by
          (REPEAT STRIP_TAC \\ MATCH_MP_TAC IMP_BC_evl_EXISTS \\ ASM_SIMP_TAC std_ss []
           \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!tttt.bbb` MATCH_MP_TAC
           \\ ASM_SIMP_TAC std_ss [term_depth_def]
           \\ IMP_RES_TAC MEM_SUM_MAP \\ DECIDE_TAC)
         \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [term_depth_def,PULL_EXISTS_CONJ]
         \\ `term_depth t' < 1 + term_depth t' + SUM (MAP (\a. term_depth a) l)` by DECIDE_TAC
         \\ RES_TAC \\ METIS_TAC [PAIR])
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def]
         \\ `!l. (MAP (\(x':string,y). term_depth y) l) =
                 (MAP (\a. term_depth a) (MAP SND l))` by
          (Induct \\ FULL_SIMP_TAC std_ss [MAP]
           \\ Cases \\ FULL_SIMP_TAC std_ss [MAP])
         \\ FULL_SIMP_TAC std_ss [])
  THEN1 (Cases_on `l` THEN1
          (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
           \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
           \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def] \\ DECIDE_TAC)
         \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def]
         \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1] \\ DECIDE_TAC)
  THEN1 (Cases_on `l` THEN1
          (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
           \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
           \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def] \\ DECIDE_TAC)
         \\ Cases_on `h` \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def,LENGTH,ADD1] \\ DECIDE_TAC)
  THEN1
   (Cases_on `l` THEN1
     (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
      \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def]
    \\ `term_depth h < 10 + (term_depth h + SUM (MAP (\a. term_depth a) t))` by DECIDE_TAC
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [EXISTS_PROD,PULL_EXISTS_CONJ]
    \\ FULL_SIMP_TAC std_ss [iLENGTH_def,iLENGTH_APPEND]
    \\ Q.PAT_X_ASSUM `BC_JUMPS_OK bc` (fn th => ASSUME_TAC th THEN ASSUME_TAC (RW [BC_JUMPS_OK_def] th))
    \\ FULL_SIMP_TAC std_ss []
    \\ `term_depth (Or t) < 10 + (term_depth h + SUM (MAP (\a. term_depth a) t))` by
          (FULL_SIMP_TAC std_ss [term_depth_def,ZERO_LT_term_depth])
    \\ RES_TAC \\ METIS_TAC [])
  THEN1
   (Cases_on `l` THEN1
     (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
      \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
    \\ Cases_on `t` THEN1
     (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def]
      \\ `term_depth h < 10 + term_depth h` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ METIS_TAC [])
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
    \\ `term_depth (And (h'::t')) < term_depth (And (h::h'::t'))` by
         (FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def,ZERO_LT_term_depth])
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
    \\ `term_depth h < term_depth (And (h::h'::t'))` by
         (FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def] \\ DECIDE_TAC)
    \\ `term_depth (Const (Sym "NIL")) < term_depth (And (h::h'::t'))` by
         (FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [PULL_EXISTS_CONJ]
    \\ Q.PAT_X_ASSUM `BC_JUMPS_OK bc` (fn th => ASSUME_TAC th THEN ASSUME_TAC (RW [BC_JUMPS_OK_def] th))
    \\ FULL_SIMP_TAC std_ss []
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def,EXISTS_PROD])
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def] \\ DECIDE_TAC)
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def] \\ DECIDE_TAC)
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def] \\ DECIDE_TAC)
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def] \\ DECIDE_TAC)
  THEN1 (Cases_on `l` THEN1
          (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
           \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
         \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def,LENGTH,ADD1] \\ DECIDE_TAC)
  THEN1 (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ Q.PAT_X_ASSUM `!tt.bbb` MATCH_MP_TAC
         \\ FULL_SIMP_TAC std_ss [term_depth_def,MAP,SUM_def,LENGTH,ADD1] \\ DECIDE_TAC));

val BC_ev_TOTAL = store_thm("BC_ev_TOTAL",
  ``!ret t a q bc. BC_JUMPS_OK bc ==> ?y. BC_ev ret (t,a,q,bc) y``,
  FULL_SIMP_TAC std_ss [EXISTS_PROD] \\ METIS_TAC [BC_ev_TOTAL_LEMMA]);

val WRITE_BYTECODE_def = Define `
   (WRITE_BYTECODE bc p [] = bc) /\
   (WRITE_BYTECODE bc p ((c:bc_inst_type)::cs) =
      (WRITE_BYTECODE (bc with code := ((p =+ SOME c) bc.code)) ((p:num) + bc.instr_length c) cs))`;

val BC_ev_fun_def = Define `
  BC_ev_fun (params,body,bc) =
    @result. if BC_JUMPS_OK bc then BC_ev T (body,MAP ssVAR (REVERSE params),bc.code_end,bc) result
                               else (result = ([],[],bc.code_end,bc))`;

val BC_ev_fun_IMP = prove(
  ``(((BC_ev_fun (params,body,bc) = result)) /\ BC_JUMPS_OK bc ==>
     BC_ev T (body,MAP ssVAR (REVERSE params),bc.code_end,bc) result)``,
  SIMP_TAC std_ss [BC_ev_fun_def] \\ METIS_TAC [BC_ev_TOTAL]);

val BC_ev_fun_thm = prove(
  ``BC_CODE_OK bc ==>
    (((BC_ev_fun (params,body,bc) = result)) =
     BC_ev T (body,MAP ssVAR (REVERSE params),bc.code_end,bc) result)``,
  SIMP_TAC std_ss [BC_ev_fun_def]
  \\ METIS_TAC [BC_ev_DETERMINISTIC,BC_ev_TOTAL,BC_JUMPS_OK_def,BC_CODE_OK_def]);

val BC_PRINT_def = Define `
  BC_PRINT bc x = bc with io_out := (bc.io_out ++ x)`;

val BC_STORE_COMPILED_def = Define `
  BC_STORE_COMPILED bc fc x = bc with compiled := (fc,x)::bc.compiled`;

val BC_ONLY_COMPILE_def = Define `
  BC_ONLY_COMPILE (params,body,bc) =
    let (new_code,a2,q2,bc) = BC_ev_fun (params,body,bc) in
    let bc = WRITE_BYTECODE bc bc.code_end new_code in
    let bc = bc with code_end := bc.code_end + iLENGTH bc.instr_length new_code in
      bc`;

val BC_COMPILE_def = Define `
  BC_COMPILE (fname,params,body,bc) =
    let bc = BC_STORE_COMPILED bc fname (bc.code_end,LENGTH params) in
      BC_ONLY_COMPILE (params,body,bc)`

val BC_COMPILE_thm = RW [BC_ONLY_COMPILE_def] BC_COMPILE_def;


(* semantics *)

val CONTAINS_BYTECODE_def = Define `
  (CONTAINS_BYTECODE bc p [] = T) /\
  (CONTAINS_BYTECODE bc p (c::cs) =
     (bc.code p = SOME c) /\
     CONTAINS_BYTECODE bc (p + bc.instr_length (c:bc_inst_type)) cs)`;

val BC_STEP_def = Define `
  BC_STEP bc p = p + bc.instr_length (THE (bc.code p))`;

val BC_SUBSTATE_def = Define `
  BC_SUBSTATE bc1 bc2 =
    (!i. BC_CODE_OK bc1 /\ ~(bc1.code i = NONE) ==> (bc2.code i = bc1.code i)) /\
    (!i. ~(FUN_LOOKUP bc1.compiled i = NONE) ==> (FUN_LOOKUP bc2.compiled i = FUN_LOOKUP bc1.compiled i)) /\
    (bc2.instr_length = bc1.instr_length) /\
    (BC_CODE_OK bc1 ==> BC_CODE_OK bc2) /\
    ?qs. bc2.consts = bc1.consts ++ qs`;

val (iSTEP_rules,iSTEP_ind,iSTEP_cases) =
 Hol_reln
 `(!bc p xs x rs.
     CONTAINS_BYTECODE bc p [iPOP] ==>
     iSTEP (x::xs,p,rs,bc) (xs,BC_STEP bc p,rs,bc)) /\
  (!bc p xs ys x rs.
     CONTAINS_BYTECODE bc p [iPOPS (LENGTH ys)] ==>
     iSTEP (x::ys++xs,p,rs,bc) (x::xs,BC_STEP bc p,rs,bc)) /\
  (!bc p xs x rs.
     CONTAINS_BYTECODE bc p [iCONST_NUM x] ==>
     iSTEP (xs,p,rs,bc) (Val x::xs,BC_STEP bc p,rs,bc)) /\
  (!bc p xs x rs.
     CONTAINS_BYTECODE bc p [iCONST_SYM x] ==>
     iSTEP (xs,p,rs,bc) (Sym x::xs,BC_STEP bc p,rs,bc)) /\
  (!bc p xs x rs.
     CONTAINS_BYTECODE bc p [iCONST_LOOKUP] /\ x < LENGTH bc.consts ==>
     iSTEP (Val x::xs,p,rs,bc) (EL x bc.consts::xs,BC_STEP bc p,rs,bc)) /\
  (!bc p xs op_name args f rs.
     CONTAINS_BYTECODE bc p [iDATA op_name] /\
     (EVAL_DATA_OP op_name = (f,LENGTH args)) ==>
     iSTEP (REVERSE args ++ xs,p,rs,bc) (f args::xs,BC_STEP bc p,rs,bc)) /\
  (!bc p xs i rs.
     CONTAINS_BYTECODE bc p [iLOAD i] /\ i < LENGTH xs ==>
     iSTEP (xs,p,rs,bc) (EL i xs::xs,BC_STEP bc p,rs,bc)) /\
  (!bc p x xs i rs.
     CONTAINS_BYTECODE bc p [iSTORE i] /\ i < LENGTH xs ==>
     iSTEP (x::xs,p,rs,bc) (UPDATE_NTH i x xs,BC_STEP bc p,rs,bc)) /\
  (!bc p xs i rs.
     CONTAINS_BYTECODE bc p [iJUMP i] ==>
     iSTEP (xs,p,rs,bc) (xs,i,rs,bc)) /\
  (!bc p xs i rs.
     CONTAINS_BYTECODE bc p [iCALL i] ==>
     iSTEP (xs,p,rs,bc) (xs,i,(BC_STEP bc p)::rs,bc)) /\
  (!bc p xs r rs.
     CONTAINS_BYTECODE bc p [iRETURN] ==>
     iSTEP (xs,p,r::rs,bc) (xs,r,rs,bc)) /\
  (!bc p x xs i rs.
     CONTAINS_BYTECODE bc p [iJNIL i] ==>
     iSTEP (x::xs,p,rs,bc) (xs,if x = Sym "NIL" then i else BC_STEP bc p,rs,bc)) /\
  (!bc p fc xs i n rs.
     CONTAINS_BYTECODE bc p [iJUMP_SYM] /\ (FUN_LOOKUP bc.compiled fc = SOME (i,n)) ==>
     iSTEP (Sym fc::Val n::xs,p,rs,bc) (xs,i,rs,bc)) /\
  (!bc p fc xs i n rs.
     CONTAINS_BYTECODE bc p [iCALL_SYM] /\ (FUN_LOOKUP bc.compiled fc = SOME (i,n)) ==>
     iSTEP (Sym fc::Val n::xs,p,rs,bc) (xs,i,(BC_STEP bc p)::rs,bc)) /\
  (!bc p xs rs xs2 p2 rs2.
     CONTAINS_BYTECODE bc p [iFAIL] ==>
     iSTEP (xs,p,rs,bc) (xs2,p2,rs2,BC_FAIL bc)) /\
  (!bc p x xs rs.
     CONTAINS_BYTECODE bc p [iPRINT] ==>
     iSTEP (x::xs,p,rs,bc) (x::xs,(BC_STEP bc p),rs,BC_PRINT bc (sexp2string x ++ "\n"))) /\
  (!bc p xs rs formals body fname bc1.
     CONTAINS_BYTECODE bc p [iCOMPILE] /\ (FUN_LOOKUP bc.compiled (getSym fname) = NONE) /\
     (BC_COMPILE (getSym fname,MAP getSym (sexp2list formals),sexp2term body,bc) = bc1) ==>
     iSTEP (body::formals::fname::xs,p,rs,bc)
           (Sym "NIL"::xs,(BC_STEP bc p),rs,bc1)) /\
  (!bc p xs rs formals body fname.
     CONTAINS_BYTECODE bc p [iCOMPILE] /\ ~(FUN_LOOKUP bc.compiled (getSym fname) = NONE) ==>
     iSTEP (body::formals::fname::xs,p,rs,bc)
           (Sym "NIL"::xs,(BC_STEP bc p),rs,BC_FAIL bc)) /\
  (!bc p xs rs xs2 p2 rs2.
     ~bc.ok ==>
     iSTEP (xs,p,rs,bc) (xs2,p2,rs2,bc))`

val iSTEP_cases_imp =
  SPEC_ALL iSTEP_cases
  |> RW [DISJ_ASSOC]
  |> MATCH_MP (METIS_PROVE [] ``(b = c \/ d) ==> (c ==> b)``)
  |> RW [GSYM DISJ_ASSOC]

val CONTAINS_BYTECODE_APPEND = prove(
  ``!c1 c2 bc p.
      CONTAINS_BYTECODE bc p (c1 ++ c2) =
      CONTAINS_BYTECODE bc p c1 /\
      CONTAINS_BYTECODE bc (p + iLENGTH bc.instr_length c1) c2``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,CONTAINS_BYTECODE_def,
    LENGTH,ADD1,AC ADD_COMM ADD_ASSOC,iLENGTH_def] \\ METIS_TAC []);

val BC_SUBSTATE_BC_ADD_CONST = prove(
  ``BC_SUBSTATE bc (BC_ADD_CONST bc s) /\ BC_SUBSTATE bc (BC_FAIL bc)``,
  SRW_TAC [] [BC_SUBSTATE_def,BC_ADD_CONST_def,BC_CODE_OK_def,BC_FAIL_def]);

val BC_SUBSTATE_REFL = store_thm("BC_SUBSTATE_REFL",
  ``!x. BC_SUBSTATE x x``,
  SIMP_TAC std_ss [BC_SUBSTATE_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `[]` \\ SIMP_TAC std_ss [APPEND_NIL]);

val BC_SUBSTATE_TRANS = prove(
  ``!x y z. BC_SUBSTATE x y /\ BC_SUBSTATE y z ==> BC_SUBSTATE x z``,
  SIMP_TAC std_ss [FORALL_PROD,BC_SUBSTATE_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] \\ METIS_TAC []);

val LENGTH_n_times = prove(
  ``!k n. LENGTH (n_times k n) = k``,
  Induct \\ ASM_SIMP_TAC std_ss [n_times_def,LENGTH]);

val BC_ADD_CONST_LENGTH = prove(
  ``!bc s. (BC_ADD_CONST bc s).instr_length = bc.instr_length``,
  SRW_TAC [] [BC_ADD_CONST_def]);

val BC_ADD_CONST_OK = prove(
  ``(BC_ADD_CONST bc s).ok = bc.ok``,
  SRW_TAC [] [BC_ADD_CONST_def]);

val BC_ev_LENGTH = prove(
  ``(!ret fc_n_a_q_bc code2_a2_q2_bc2. BC_ap ret fc_n_a_q_bc code2_a2_q2_bc2 ==>
       !fc n a q bc code2 a2 q2 bc2.
          (fc_n_a_q_bc = (fc,n,a,q,bc)) /\
          (code2_a2_q2_bc2 = (code2,a2,q2,bc2)) ==>
          BC_SUBSTATE bc bc2 /\
          (bc2.instr_length = bc.instr_length) /\
          (bc2.ok = bc.ok) /\
          (q2 = q + iLENGTH bc.instr_length code2)) /\
    (!xs_a_q_bc code2_a2_q2_bc2. BC_evl xs_a_q_bc code2_a2_q2_bc2 ==>
       !xs a q bc code2 a2 q2 bc2.
          (xs_a_q_bc = (xs,a,q,bc)) /\
          (code2_a2_q2_bc2 = (code2,a2,q2,bc2)) ==>
          BC_SUBSTATE bc bc2 /\
          (bc2.instr_length = bc.instr_length) /\
          (bc2.ok = bc.ok) /\
          (q2 = q + iLENGTH bc.instr_length code2)) /\
    (!ret x_a_q_bc code2_a2_q2_bc2. BC_ev ret x_a_q_bc code2_a2_q2_bc2 ==>
       !x a q bc code2 a2 q2 bc2.
          (x_a_q_bc = (x,a,q,bc)) /\
          (code2_a2_q2_bc2 = (code2,a2,q2,bc2)) ==>
          BC_SUBSTATE bc bc2 /\
          (bc2.instr_length = bc.instr_length) /\
          (bc2.ok = bc.ok) /\
          (q2 = q + iLENGTH bc.instr_length code2))``,
  HO_MATCH_MP_TAC BC_ev_ind \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (MP_TAC o GSYM)
  \\ ASM_SIMP_TAC std_ss [BC_return_def,LENGTH,LENGTH_APPEND,ADD_ASSOC]
  \\ REPEAT STRIP_TAC \\ REPEAT
   (Q.PAT_X_ASSUM `xxx = code2` (MP_TAC o GSYM)
    \\ ASM_SIMP_TAC std_ss [iLENGTH_APPEND,LENGTH,ADD_ASSOC,LENGTH_n_times,iLENGTH_def]
    \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
  \\ SRW_TAC [] [] \\ SIMP_TAC std_ss [iLENGTH_def,BC_ADD_CONST_LENGTH]
  \\ REPEAT (Q.PAT_X_ASSUM `pn = qn + nnn:num` (fn th => SIMP_TAC std_ss [Once th]))
  \\ ASM_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC,iLENGTH_APPEND,iLENGTH_APPEND,
       BC_SUBSTATE_REFL,BC_SUBSTATE_BC_ADD_CONST,BC_ADD_CONST_LENGTH,BC_ADD_CONST_OK]
  \\ IMP_RES_TAC BC_SUBSTATE_TRANS
  \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM]
  \\ Q.PAT_X_ASSUM `addr = xx` (fn th => FULL_SIMP_TAC std_ss [Once th])
  \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM])
  |> SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO];

val WRITE_BYTECODE_SKIP = prove(
  ``!xs a bc.
      ((WRITE_BYTECODE bc a xs).consts = bc.consts) /\
      ((WRITE_BYTECODE bc a xs).code_end = bc.code_end) /\
      ((WRITE_BYTECODE bc a xs).compiled = bc.compiled) /\
      ((WRITE_BYTECODE bc a xs).instr_length = bc.instr_length)``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_def]);

val BC_CODE_OK_SKIP = prove(
  ``(BC_CODE_OK (bc with compiled := x) = BC_CODE_OK bc) /\
    (BC_CODE_OK (bc with io_out := y) = BC_CODE_OK bc)``,
  SIMP_TAC (srw_ss()) [BC_CODE_OK_def]);

val WRITE_BYTECODE_IGNORE1 = prove(
  ``!xs a i bc.
      i < a ==> ((WRITE_BYTECODE bc a xs).code i = bc.code i)``,
  Induct \\ SIMP_TAC std_ss [WRITE_BYTECODE_def,iLENGTH_def] \\ REPEAT STRIP_TAC
  \\ `~(a = i) /\ i < a + bc.instr_length h` by DECIDE_TAC \\ RES_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]);

val WRITE_BYTECODE_IGNORE2 = prove(
  ``!xs a i bc.
      (!h. 0 < bc.instr_length h) /\
      a + iLENGTH bc.instr_length xs <= i ==>
      ((WRITE_BYTECODE bc a xs).code i = bc.code i)``,
  Induct \\ SIMP_TAC std_ss [WRITE_BYTECODE_def,iLENGTH_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ADD_ASSOC] \\ RES_TAC
  \\ `bc.instr_length = (bc with code := (a =+ SOME h) bc.code).instr_length` by SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `0 < bc.instr_length h` by METIS_TAC []
  \\ `~(a = i)` by DECIDE_TAC \\ ASM_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]);

val WRITE_BYTECODE_code_end = store_thm("WRITE_BYTECODE_code_end",
  ``!xs a bc. ((WRITE_BYTECODE bc a xs).code_end = bc.code_end) /\
              ((WRITE_BYTECODE bc a xs).instr_length = bc.instr_length) /\
              ((WRITE_BYTECODE bc a xs).consts = bc.consts) /\
              ((WRITE_BYTECODE bc a xs).compiled = bc.compiled) /\
              ((WRITE_BYTECODE bc a xs).io_out = bc.io_out) /\
              ((WRITE_BYTECODE bc a xs).ok = bc.ok)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_def]);

val BC_SUBSTATE_ONLY_COMPILE = store_thm("BC_SUBSTATE_ONLY_COMPILE",
  ``!bc. BC_SUBSTATE bc (BC_ONLY_COMPILE (params,body,bc))``,
  SIMP_TAC std_ss [BC_ONLY_COMPILE_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ `?x y z bc8. BC_ev_fun (params,body,bc) = (x,y,z,bc8)` by METIS_TAC [PAIR]
  \\ REVERSE (Cases_on `BC_JUMPS_OK bc`) THEN1
   (FULL_SIMP_TAC std_ss [BC_ev_fun_def,WRITE_BYTECODE_def,iLENGTH_def]
    \\ REPEAT (Q.PAT_X_ASSUM `yyy = xxx` (MP_TAC o GSYM)) \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [BC_ev_fun_def,WRITE_BYTECODE_def,iLENGTH_def]
    \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `[]` \\ EVAL_TAC)
  \\ ASM_SIMP_TAC std_ss [] \\ IMP_RES_TAC BC_ev_fun_IMP
  \\ IMP_RES_TAC BC_ev_LENGTH \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC BC_SUBSTATE_TRANS \\ Q.EXISTS_TAC `bc8`
  \\ STRIP_TAC THEN1 METIS_TAC [BC_SUBSTATE_TRANS]
  \\ FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,WRITE_BYTECODE_SKIP,WRITE_BYTECODE_code_end]
  \\ Cases_on `BC_CODE_OK bc8` \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [BC_CODE_OK_def,WRITE_BYTECODE_SKIP]
  \\ Q.PAT_X_ASSUM `bc8.instr_length = bc1.instr_length` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ Q.SPEC_TAC (`bc8.code_end`,`a`) \\ REPEAT STRIP_TAC THEN1
   (MATCH_MP_TAC WRITE_BYTECODE_IGNORE1 \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss [NOT_LESS] \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC WRITE_BYTECODE_IGNORE2 \\ ASM_SIMP_TAC std_ss []
  \\ `a <= i` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []);

val BC_COMPILE_SUBSTATE = prove(
  ``!bc1 bc2.
      (FUN_LOOKUP bc1.compiled fname = NONE) /\ (BC_COMPILE (fname,params,body,bc1) = bc2) ==>
      BC_SUBSTATE bc1 bc2``,
  SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [BC_COMPILE_def,LET_DEF]
  \\ MATCH_MP_TAC BC_SUBSTATE_TRANS
  \\ Q.EXISTS_TAC `BC_STORE_COMPILED bc1 fname (bc1.code_end,LENGTH params)`
  \\ ASM_SIMP_TAC std_ss [BC_SUBSTATE_ONLY_COMPILE]
  \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC THEN1 (METIS_TAC [])
  \\ Q.EXISTS_TAC `[]` \\ EVAL_TAC);

val BC_SUBSTATE_COMPILE = save_thm("BC_SUBSTATE_COMPILE",
  SIMP_RULE std_ss [] BC_COMPILE_SUBSTATE);

val iSTEP_BC_SUBSTATE_LEMMA = prove(
  ``iSTEP (xs1,p1,rs1,bc1) (xs2,p2,rs2,bc2) ==>
    BC_SUBSTATE bc1 bc2``,
  SIMP_TAC std_ss [iSTEP_cases,BC_SUBSTATE_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [APPEND_NIL,BC_PRINT_def,BC_STORE_COMPILED_def]
  \\ IMP_RES_TAC BC_ev_LENGTH \\ IMP_RES_TAC BC_COMPILE_SUBSTATE
  \\ FULL_SIMP_TAC (srw_ss()) [APPEND_NIL,BC_PRINT_def,BC_SUBSTATE_def,
       BC_CODE_OK_SKIP,BC_FAIL_def,BC_CODE_OK_def]);

val iSTEP_BC_SUBSTATE = prove(
  ``!x y. RTC iSTEP x y ==>
     let (xs1,p1,rs1,bc1) = x in
     let (xs2,p2,rs2,bc2) = y in
       BC_SUBSTATE bc1 bc2``,
  HO_MATCH_MP_TAC RTC_INDUCT \\ FULL_SIMP_TAC std_ss [FORALL_PROD,LET_DEF]
  \\ REPEAT STRIP_TAC THEN1 SIMP_TAC std_ss [BC_SUBSTATE_REFL]
  \\ IMP_RES_TAC iSTEP_BC_SUBSTATE_LEMMA
  \\ IMP_RES_TAC BC_SUBSTATE_TRANS)
  |> Q.SPECL [`(xs1,p1,rs1,bc1)`,`(xs2,p2,rs2,bc2)`]
  |> SIMP_RULE std_ss [LET_DEF];


(* prove that translation is semantics preserving *)

val VARS_IN_STACK_def = Define `
  VARS_IN_STACK env stack alist_placement =
    !v. v IN FDOM env ==>
        ?n. (var_lookup 0 v alist_placement = SOME n) /\
            (env ' v = EL n stack) /\
            n < LENGTH stack`;

val STACK_INV_def = Define `
  STACK_INV env stack alist_placement =
    VARS_IN_STACK env stack alist_placement /\
    LENGTH alist_placement <= LENGTH stack`;

val var_lookup_aux_thm = prove(
  ``!a v n k.
      (var_lookup n v a = SOME k) = (var_lookup 0 v a = SOME (k-n)) /\ n <= k``,
  Induct \\ SIMP_TAC std_ss [var_lookup_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `ssVAR v = h` \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
  THEN1 (STRIP_TAC \\ DECIDE_TAC) \\ ONCE_ASM_REWRITE_TAC []
  \\ SIMP_TAC std_ss [DECIDE ``1<=k-n /\ n <= k = n+1<=(k:num)``,GSYM CONJ_ASSOC]
  \\ POP_ASSUM (K ALL_TAC) \\ Cases_on `n+1<=k` \\ ASM_SIMP_TAC std_ss [SUB_PLUS]);

val var_lookup_aux = prove(
  ``!a v n m.
      (var_lookup n v a = SOME k) ==> (var_lookup (n + m) v a = SOME (k + m))``,
  ONCE_REWRITE_TAC [var_lookup_aux_thm] \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val STACK_INV_lemma = prove(
  ``(STACK_INV env (result::stack) (ssTEMP::a) = STACK_INV env stack a)``,
  EQ_TAC THEN1
   (SIMP_TAC std_ss [STACK_INV_def,VARS_IN_STACK_def,LENGTH]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [var_lookup_def,stack_slot_11,stack_slot_distinct]
    \\ Q.PAT_X_ASSUM `bbb = SOME n` (STRIP_ASSUME_TAC o RW1[var_lookup_aux_thm])
    \\ ASM_SIMP_TAC std_ss [] \\ Cases_on `n`
    \\ FULL_SIMP_TAC std_ss [EL,TL,ADD1,LENGTH] \\ DECIDE_TAC)
  \\ SIMP_TAC std_ss [STACK_INV_def,VARS_IN_STACK_def]
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Q.EXISTS_TAC `SUC n` \\ FULL_SIMP_TAC std_ss [var_lookup_def,LENGTH,EL,TL]
  \\ IMP_RES_TAC var_lookup_aux \\ FULL_SIMP_TAC std_ss [ADD1,stack_slot_distinct]);

val STACK_INV_lemma2 = prove(
  ``!result.
      STACK_INV env (result ++ stack) (MAP (\x.ssTEMP) result ++ a) =
      STACK_INV env stack a``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,MAP,STACK_INV_lemma]);

val LENGTH_LESS_EQ_LENGTH_IMP = prove(
  ``!a args. LENGTH args <= LENGTH a ==>
             ?a1 a2. (a = a1 ++ a2) /\ (LENGTH args = LENGTH a1)``,
  Induct THEN1 (SIMP_TAC std_ss [LENGTH] \\ METIS_TAC [APPEND,LENGTH])
  \\ REPEAT STRIP_TAC \\ Cases_on `args` THEN1 METIS_TAC [APPEND,LENGTH]
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ METIS_TAC [APPEND,LENGTH]);

val IMP_MAP_NONE = prove(
  ``(LENGTH args = LENGTH a1) /\ EVERY (\x. x = ssTEMP) a1 ==>
    (a1 = MAP (\x. ssTEMP) (REVERSE args))``,
  ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE] \\ Q.SPEC_TAC (`REVERSE args`,`xs`)
  \\ SIMP_TAC std_ss [LENGTH_REVERSE] \\ Q.SPEC_TAC (`a1`,`ys`) \\ Induct
  \\ Cases_on `xs` \\ ASM_SIMP_TAC std_ss [CONS_11,LENGTH,MAP,ADD1,EVERY_DEF]);

val STACK_INV_FUPDATE = prove(
  ``STACK_INV env stack a ==>
    STACK_INV (env |+ (v,x')) (x'::stack) (ssVAR v::a)``,
  SIMP_TAC std_ss [STACK_INV_def,VARS_IN_STACK_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,FDOM_FUPDATE]
  \\ Cases_on `v' = v` \\ FULL_SIMP_TAC std_ss [var_lookup_def,EL,HD,LENGTH]
  \\ FULL_SIMP_TAC std_ss [IN_INSERT,stack_slot_11] \\ RES_TAC
  \\ ONCE_REWRITE_TAC [var_lookup_aux_thm]
  \\ Q.EXISTS_TAC `SUC n` \\ SIMP_TAC std_ss [EL,TL]
  \\ ASM_SIMP_TAC std_ss [ADD1]);

val FDOM_VarBindAux = prove(
  ``!xs ys v. (LENGTH xs = LENGTH ys) ==> (v IN FDOM (VarBindAux xs ys) = MEM v xs)``,
  Induct \\ SIMP_TAC std_ss [VarBindAux_def,MEM,FDOM_FEMPTY,NOT_IN_EMPTY]
  \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH,ADD1,VarBindAux_def]
  \\ SIMP_TAC std_ss [FDOM_FUPDATE,IN_INSERT] \\ METIS_TAC []);

val IN_UNION_LEMMA = prove(
  ``x IN (s UNION t) = x IN s \/ (~(x IN s) /\ x IN t)``,
  SIMP_TAC std_ss [IN_UNION] \\ METIS_TAC []);

val EL_LENGTH_APPEND = prove(
  ``!xs n ys. EL (LENGTH xs + n) (xs ++ ys) = EL n ys``,
  Induct \\ ASM_SIMP_TAC std_ss [LENGTH,APPEND,EL,TL,ADD_CLAUSES]);

val VARS_IN_STACK_VarBind_THM = prove(
  ``!params args.
      VARS_IN_STACK a stack xs /\
      (LENGTH (params:string list) = LENGTH (args:SExp list)) ==>
      VARS_IN_STACK (FUNION (VarBind params args) a) (REVERSE args ++ stack)
        (MAP ssVAR (REVERSE params) ++ xs)``,
  SIMP_TAC std_ss [VarBind_def] \\ NTAC 2 STRIP_TAC
  \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ Q.SPEC_TAC (`REVERSE args`,`ys`)
  \\ Q.SPEC_TAC (`REVERSE params:string list`,`xss`)
  \\ SIMP_TAC std_ss [VARS_IN_STACK_def,FDOM_VarBindAux,FUNION_DEF,IN_UNION_LEMMA]
  \\ SIMP_TAC std_ss [METIS_PROVE [] ``b \/ (~b /\ c) = (~b ==> c)``]
  \\ Induct \\ SIMP_TAC std_ss [MEM,MAP,APPEND,LENGTH] THEN1
   (REPEAT STRIP_TAC \\ `ys = []` by METIS_TAC [LENGTH_NIL]
    \\ FULL_SIMP_TAC std_ss [APPEND])
  \\ REPEAT STRIP_TAC
  \\ Cases_on `v = h` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ Q.EXISTS_TAC `0` \\ SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_APPEND]
    \\ FULL_SIMP_TAC std_ss [VarBindAux_def,FAPPLY_FUPDATE_THM,EL,HD,APPEND,
         var_lookup_def] \\ DECIDE_TAC)
  \\ Cases_on `MEM v xss` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ FULL_SIMP_TAC (srw_ss()) [VarBindAux_def,FAPPLY_FUPDATE_THM,EL,HD,APPEND,
         var_lookup_def] \\ Q.PAT_X_ASSUM `!ys.bb` MP_TAC
    \\ Q.PAT_X_ASSUM `!ys.bb` (MP_TAC o Q.SPEC `v` o RW [] o Q.SPEC `t`)
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `SUC n` \\ FULL_SIMP_TAC std_ss [EL,TL]
    \\ ONCE_REWRITE_TAC [var_lookup_aux_thm]
    \\ ASM_SIMP_TAC std_ss [ADD1] \\ DECIDE_TAC)
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ Q.PAT_X_ASSUM `!ys.bb` MP_TAC
  \\ Q.PAT_X_ASSUM `!ys.bb` (MP_TAC o Q.SPEC `v` o RW [] o Q.SPEC `t`)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `SUC n` \\ FULL_SIMP_TAC std_ss [EL,TL,APPEND]
  \\ ASM_SIMP_TAC (srw_ss()) [var_lookup_def]
  \\ ONCE_REWRITE_TAC [var_lookup_aux_thm]
  \\ ASM_SIMP_TAC std_ss [ADD1] \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)

val VARS_IN_STACK_VarBind = prove(
  ``!params args.
      (LENGTH (params:string list) = LENGTH (args:SExp list)) ==>
      VARS_IN_STACK (VarBind params args) (REVERSE args ++ stack)
        (MAP ssVAR (REVERSE params))``,
  NTAC 2 STRIP_TAC
  \\ MATCH_MP_TAC (RW [APPEND_NIL,FUNION_FEMPTY_2,GSYM AND_IMP_INTRO]
    (Q.INST [`a`|->`FEMPTY`,`xs`|->`[]`] VARS_IN_STACK_VarBind_THM))
  \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val STACK_INV_VarBind_2 = prove(
  ``!params args p stack.
      STACK_INV a stack xs /\
      (LENGTH (params:string list) = LENGTH (args:SExp list)) ==>
      STACK_INV (FUNION (VarBind params args) a) (REVERSE args ++ stack)
        (MAP ssVAR (REVERSE params) ++ xs)``,
  SIMP_TAC std_ss [STACK_INV_def,VARS_IN_STACK_VarBind_THM,
     LENGTH_APPEND,LENGTH_MAP,LENGTH_REVERSE]);

val STACK_INV_VarBind = prove(
  ``!params args p stack.
      (LENGTH (params:string list) = LENGTH (args:SExp list)) ==>
      STACK_INV (VarBind params args) (REVERSE args ++ stack)
        (MAP ssVAR (REVERSE params))``,
  SIMP_TAC std_ss [STACK_INV_def,STACK_INV_lemma,APPEND,VARS_IN_STACK_VarBind,
    isVal_def,LENGTH,LENGTH_APPEND,LENGTH_REVERSE,LENGTH_MAP]);

val BC_FNS_ASSUM_def = Define `
  BC_FNS_ASSUM fns bc =
    !fc params exp.
       fc IN FDOM fns /\ (fns ' fc = (params,exp)) ==>
       ?p pcode a5 bc4 bc5.
         CONTAINS_BYTECODE bc p pcode /\
         (FUN_LOOKUP bc.compiled fc = SOME (p,LENGTH params)) /\
         BC_ev T (exp,MAP ssVAR (REVERSE params),p,bc4)
                 (pcode,a5,p + iLENGTH bc.instr_length pcode,bc5) /\
         BC_SUBSTATE bc5 bc`;

val BC_REFINES_def = Define `
  BC_REFINES (fns,io) bc =
    BC_FNS_ASSUM fns bc /\ (bc.io_out = io) /\ BC_CODE_OK bc /\
    ({ j |j| ~(FUN_LOOKUP bc.compiled j = NONE)} = FDOM fns) /\
    !j. bc.code_end <= j ==> (bc.code j = NONE)`;

val iSTEP_ret_state_def = Define `
  iSTEP_ret_state a2 (result,stack,r,rs,bc) =
    (result::DROP (LENGTH a2) stack,r,rs,bc)`;

val gen_pops_thm = prove(
  ``CONTAINS_BYTECODE bc p (gen_pops (LENGTH xs)) ==>
    RTC iSTEP (a::xs++stack,p,rs,bc)
              (a::stack,p + iLENGTH bc.instr_length (gen_pops (LENGTH xs)),rs,bc)``,
  SRW_TAC [] [gen_pops_def,LENGTH_NIL,iLENGTH_def]
  \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
  \\ MATCH_MP_TAC iSTEP_cases_imp
  \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,CONTAINS_BYTECODE_def,
       LENGTH,CONS_11,STACK_INV_lemma,LENGTH_APPEND,APPEND,iLENGTH_def,BC_STEP_def]
  \\ METIS_TAC []);

val gen_popn_thm = prove(
  ``CONTAINS_BYTECODE bc p (gen_popn (LENGTH xs)) ==>
    RTC iSTEP (xs++stack,p,rs,bc)
              (stack,p+iLENGTH bc.instr_length (gen_popn (LENGTH xs)),rs,bc)``,
  SRW_TAC [] [gen_popn_def,LENGTH_NIL,CONTAINS_BYTECODE_def,iLENGTH_def,iLENGTH_APPEND]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND]
  \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `(h::stack,p + iLENGTH bc.instr_length (gen_pops (LENGTH t)),rs,bc)`
  \\ IMP_RES_TAC gen_pops_thm \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
  \\ MATCH_MP_TAC iSTEP_cases_imp
  \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_def]
  \\ ASM_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,CONTAINS_BYTECODE_def,
         LENGTH,CONS_11,STACK_INV_lemma,LENGTH_APPEND,APPEND,NOT_CONS_NIL,BC_STEP_def]);

val BC_return_code_thm = prove(
  ``CONTAINS_BYTECODE bc p (BC_return_code T (ssTEMP::a2)) /\
    STACK_INV a stack a2 ==>
    RTC iSTEP (result::stack,p,r::rs,bc) (iSTEP_ret_state a2 (result,stack,r,rs,bc))``,
  SIMP_TAC std_ss [BC_return_code_def,LENGTH,ADD1,ADD_SUB]
  \\ SIMP_TAC std_ss [iSTEP_ret_state_def]
  \\ SIMP_TAC std_ss [STACK_INV_def,CONTAINS_BYTECODE_APPEND]
  \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `(result::DROP (LENGTH a2)stack,(p + iLENGTH bc.instr_length (gen_pops (LENGTH a2))),r::rs,bc)`
  \\ REVERSE STRIP_TAC THEN1
   (REPEAT (MATCH_MP_TAC RTC_SINGLE)
    \\ MATCH_MP_TAC iSTEP_cases_imp
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_def]
    \\ ASM_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,CONTAINS_BYTECODE_def,
         LENGTH,CONS_11,STACK_INV_lemma,LENGTH_APPEND,APPEND,NOT_CONS_NIL,BC_STEP_def])
  \\ IMP_RES_TAC LENGTH_LESS_EQ_LENGTH_IMP
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.BUTFIRSTN_LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND]
  \\ MATCH_MP_TAC gen_pops_thm \\ ASM_SIMP_TAC std_ss []);

val DROP_LENGTH_ADD = prove(
  ``!xs ys n. DROP (LENGTH xs + n) (xs ++ ys) = DROP n ys``,
  Induct \\ SIMP_TAC std_ss [LENGTH,APPEND,DROP_def,ADD1]
  \\ REPEAT STRIP_TAC \\ `LENGTH xs + 1 + n - 1 = LENGTH xs + n` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []);

val iSTEP_ret_state_APPEND_MAP = prove(
  ``(LENGTH ys = LENGTH xs) ==>
    (iSTEP_ret_state (MAP f (REVERSE xs) ++ a2)
                     (result,REVERSE ys ++ stack,r,rs,bc) =
     iSTEP_ret_state a2 (result,stack,r,rs,bc))``,
  SIMP_TAC std_ss [iSTEP_ret_state_def,LENGTH_APPEND,LENGTH_MAP,LENGTH_REVERSE]
  \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE] \\ METIS_TAC [DROP_LENGTH_ADD]);

val n_times_iSTORE = prove(
  ``!ys args xs bc p stack rs.
      (LENGTH ys = LENGTH args) /\
      CONTAINS_BYTECODE bc p (n_times (LENGTH args) (iSTORE (LENGTH (args++xs)-1))) ==>
      RTC iSTEP (args++xs++ys++stack,p,rs,bc)
                (xs++args++stack,p+iLENGTH bc.instr_length (n_times (LENGTH args) (iSTORE (LENGTH (args++xs)-1))),rs,bc)``,
  Induct \\ Cases_on `args`
  \\ SIMP_TAC std_ss [APPEND,APPEND_NIL,RTC_REFL,LENGTH,ADD1]
  \\ SIMP_TAC std_ss [GSYM ADD1,n_times_def,CONTAINS_BYTECODE_def,iLENGTH_def]
  \\ ASM_SIMP_TAC std_ss [RTC_REFL]
  \\ SIMP_TAC std_ss [ADD1] \\ NTAC 7 STRIP_TAC
  \\ Q.PAT_X_ASSUM `!args.bbb` (MP_TAC o Q.SPECL [`t`,`xs++[h]`,`bc`,`p+bc.instr_length (iSTORE (LENGTH (t:SExp list) + LENGTH (xs:SExp list)))`,`stack`,`rs`])
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,ADD_ASSOC]
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
  \\ Q.EXISTS_TAC `(t ++ (xs ++ [h]) ++ ys ++ stack,p + bc.instr_length (iSTORE (LENGTH t + LENGTH xs)),rs,bc)`
  \\ REVERSE STRIP_TAC \\ RES_TAC
  THEN1 (FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,AC ADD_ASSOC ADD_COMM])
  \\ MATCH_MP_TAC RTC_SINGLE
  \\ MATCH_MP_TAC iSTEP_cases_imp
  \\ ASM_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,CONTAINS_BYTECODE_def,
           LENGTH,CONS_11,STACK_INV_lemma,LENGTH_APPEND,BC_STEP_def]
  \\ REVERSE STRIP_TAC THEN1 DECIDE_TAC
  \\ SIMP_TAC std_ss [APPEND_ASSOC,GSYM LENGTH_APPEND]
  \\ Q.SPEC_TAC (`t++xs`,`zs`)
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ Q.SPEC_TAC (`ys++stack`,`qss`)
  \\ Induct_on `zs` \\ ASM_SIMP_TAC std_ss [LENGTH,APPEND,UPDATE_NTH_def,CONS_11]);

val n_times_iLOAD = prove(
  ``!xs ys bc p stack.
      CONTAINS_BYTECODE bc p (n_times (LENGTH xs) (iLOAD (LENGTH (xs ++ ys) - 1))) ==>
      RTC iSTEP (ys++xs++stack,p,rs,bc)
                (xs++ys++xs++stack,p+iLENGTH bc.instr_length (n_times (LENGTH xs) (iLOAD (LENGTH (xs ++ ys) - 1))),rs,bc)``,
  HO_MATCH_MP_TAC rich_listTheory.SNOC_INDUCT
  \\ SIMP_TAC std_ss [APPEND_NIL,APPEND,LENGTH,RTC_REFL,n_times_def]
  \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_def,SNOC_APPEND,APPEND_ASSOC,
       LENGTH_APPEND,LENGTH,ADD_CLAUSES,GSYM ADD1,n_times_def,iLENGTH_def,RTC_REFL]
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
  \\ Q.EXISTS_TAC `([x] ++ ys ++ xs ++ [x] ++ stack,p+bc.instr_length(iLOAD (LENGTH xs + LENGTH ys)),rs,bc)`
  \\ REPEAT STRIP_TAC THEN1
   (MATCH_MP_TAC RTC_SINGLE
    \\ MATCH_MP_TAC iSTEP_cases_imp
    \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,CONTAINS_BYTECODE_def,
           LENGTH,CONS_11,STACK_INV_lemma,LENGTH_APPEND,LENGTH_APPEND,BC_STEP_def]
    \\ `LENGTH xs + LENGTH ys = LENGTH ys + LENGTH xs` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11]
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,GSYM APPEND_ASSOC]
    \\ SIMP_TAC std_ss [APPEND,EL,HD] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ `[x] ++ (ys ++ (xs ++ ([x] ++ stack))) = (x::ys) ++ xs ++ (x::stack)` by
         FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ Q.PAT_X_ASSUM `!ys.bbb` (MP_TAC o Q.SPECL [`x::ys`,`bc`,
       `p + bc.instr_length (iLOAD (LENGTH (xs:SExp list) + LENGTH (ys:SExp list)))`,`x::stack`])
  \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,ADD_SUB,ADD_ASSOC]);

val LESS_EQ_IMP_APPEND = prove(
  ``!n ys. n <= LENGTH ys ==> ?ys1 ys2. (ys = ys1 ++ ys2) /\ (LENGTH ys2 = n)``,
  Induct \\ SIMP_TAC std_ss [LENGTH_NIL,APPEND,APPEND_NIL] \\ STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `ys` rich_listTheory.SNOC_CASES)
  \\ ASM_SIMP_TAC std_ss [LENGTH_SNOC,LENGTH,ADD1] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ Q.EXISTS_TAC `ys1` \\ Q.EXISTS_TAC `ys2++[x]`
  \\ ASM_SIMP_TAC std_ss [APPEND,LENGTH,ADD1,LENGTH_SNOC,SNOC_APPEND]
  \\ ASM_SIMP_TAC std_ss [APPEND_ASSOC,LENGTH_APPEND,LENGTH]);

val BC_ev_CONSTS = prove(
  ``(!ret fc_n_a_q_bc code2_a2_q2_bc2. BC_ap ret fc_n_a_q_bc code2_a2_q2_bc2 ==>
       !fc n a q bc code2 a2 q2 bc2.
          (fc_n_a_q_bc = (fc,n,a,q,bc)) /\
          (code2_a2_q2_bc2 = (code2,a2,q2,bc2)) ==>
          (bc2.io_out = bc.io_out) /\
          (bc2.code = bc.code) /\
          (bc2.ok = bc.ok) /\
          (bc2.compiled = bc.compiled) /\
          (bc2.code_end = bc.code_end) /\
          (bc2.instr_length = bc.instr_length)) /\
    (!xs_a_q_bc code2_a2_q2_bc2. BC_evl xs_a_q_bc code2_a2_q2_bc2 ==>
       !xs a q bc code2 a2 q2 bc2.
          (xs_a_q_bc = (xs,a,q,bc)) /\
          (code2_a2_q2_bc2 = (code2,a2,q2,bc2)) ==>
          (bc2.io_out = bc.io_out) /\
          (bc2.code = bc.code) /\
          (bc2.ok = bc.ok) /\
          (bc2.compiled = bc.compiled) /\
          (bc2.code_end = bc.code_end) /\
          (bc2.instr_length = bc.instr_length)) /\
    (!ret x_a_q_bc code2_a2_q2_bc2. BC_ev ret x_a_q_bc code2_a2_q2_bc2 ==>
       !x a q bc code2 a2 q2 bc2.
          (x_a_q_bc = (x,a,q,bc)) /\
          (code2_a2_q2_bc2 = (code2,a2,q2,bc2)) ==>
          (bc2.io_out = bc.io_out) /\
          (bc2.code = bc.code) /\
          (bc2.ok = bc.ok) /\
          (bc2.compiled = bc.compiled) /\
          (bc2.code_end = bc.code_end) /\
          (bc2.instr_length = bc.instr_length))``,
  HO_MATCH_MP_TAC BC_ev_ind \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (MP_TAC o GSYM)
  \\ ASM_SIMP_TAC std_ss [BC_return_def,LENGTH,LENGTH_APPEND,ADD_ASSOC]
  \\ SRW_TAC [] [] \\ SIMP_TAC (srw_ss()) [BC_ADD_CONST_def])
  |> SIMP_RULE std_ss [PULL_FORALL_IMP];

val BC_ev_fun_CONSTS = store_thm("BC_ev_fun_CONSTS",
  ``(BC_ev_fun (params,body,bcA) = (new_code,a2,q2,bcB)) /\ BC_JUMPS_OK bcA ==>
    (bcA.code = bcB.code) /\ (bcA.code_end = bcB.code_end) /\
    (bcA.instr_length = bcB.instr_length) /\ (bcA.io_out = bcB.io_out) /\
    (bcA.compiled = bcB.compiled) /\
    (bcA.ok = bcB.ok)``,
  STRIP_TAC \\ IMP_RES_TAC BC_ev_fun_IMP
  \\ IMP_RES_TAC BC_ev_CONSTS \\ ASM_SIMP_TAC std_ss []);

val WRITE_BYTECODE_io_out = prove(
  ``!xs a bc. ((WRITE_BYTECODE bc a xs).io_out = bc.io_out) /\
              ((WRITE_BYTECODE bc a xs).ok = bc.ok)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_def]);

val BC_ev_fun_io_out = prove(
  ``(BC_ev_fun(params,body,bc) = (z1,z2,z3,bc2)) ==> (bc.io_out = bc2.io_out) /\
                                                     (bc.ok = bc2.ok)``,
  Cases_on `BC_JUMPS_OK bc` THEN1 (METIS_TAC [BC_ev_fun_CONSTS])
  \\ ASM_SIMP_TAC std_ss [BC_ev_fun_def]);

val BC_ONLY_COMPILE_io_out = store_thm("BC_ONLY_COMPILE_io_out",
  ``((BC_ONLY_COMPILE (params,body,bc)).io_out = bc.io_out) /\
    ((BC_ONLY_COMPILE (params,body,bc)).ok = bc.ok)``,
  SIMP_TAC std_ss [BC_ONLY_COMPILE_def,LET_DEF,BC_ev_fun_io_out]
  \\ `?z1 z2 z3 bc2. BC_ev_fun(params,body,bc) = (z1,z2,z3,bc2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC BC_ev_fun_io_out
  \\ FULL_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_io_out]);

val BC_COMPILE_io_out = store_thm("BC_COMPILE_io_out",
  ``((BC_COMPILE (fname,params,body,bc)).io_out = bc.io_out) /\
    ((BC_COMPILE (fname,params,body,bc)).ok = bc.ok)``,
  SIMP_TAC std_ss [BC_COMPILE_def,LET_DEF,BC_ONLY_COMPILE_io_out] \\ EVAL_TAC);

fun MOVE_TAC (gs,tm) = if is_forall tm then STRIP_TAC (gs,tm) else
                       if is_imp tm then STRIP_TAC (gs,tm) else NO_TAC (gs,tm)

val n_times_APPEND = prove(
  ``!k x xs. n_times k x ++ x::xs = n_times (SUC k) x ++ xs``,
  Induct \\ ASM_SIMP_TAC std_ss [n_times_def,APPEND]);

val n_times_iCONST = prove(
  ``!k a stack env bc p.
      CONTAINS_BYTECODE bc p (n_times k (iCONST_SYM "NIL")) /\
      STACK_INV env stack a ==>
      STACK_INV env (n_times k (Sym "NIL") ++ stack) (n_times k ssTEMP ++ a) /\
      RTC iSTEP (stack,p,r::rs,bc) (n_times k (Sym "NIL") ++ stack,p + iLENGTH bc.instr_length (n_times k (iCONST_SYM "NIL")),r::rs,bc)``,
  Induct \\ SIMP_TAC std_ss [n_times_def,APPEND,iLENGTH_def,RTC_REFL]
  \\ REPEAT MOVE_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_def]
  \\ `STACK_INV env (Sym "NIL"::stack) (ssTEMP::a)` by
       ASM_SIMP_TAC std_ss [STACK_INV_lemma,LENGTH,ADD1,AC ADD_ASSOC ADD_COMM]
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss [STACK_INV_lemma,LENGTH,ADD1,AC ADD_ASSOC ADD_COMM]
  \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
  \\ Q.EXISTS_TAC `(Sym "NIL" :: stack,p+bc.instr_length(iCONST_SYM "NIL"),r::rs,bc)` \\ STRIP_TAC THEN1
   (REPEAT (MATCH_MP_TAC RTC_SINGLE)
    \\ MATCH_MP_TAC iSTEP_cases_imp
    \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,CONTAINS_BYTECODE_def,
           LENGTH,CONS_11,STACK_INV_lemma,EL,STACK_INV_def,BC_STEP_def]
    \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,DECIDE ``0<n = ~(n = 0:num)``])
  \\ FULL_SIMP_TAC std_ss [HD,GSYM n_times_def,GSYM APPEND,n_times_APPEND]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM])

val MAP_EQ_GENLIST = prove(
  ``!xs. MAP (\x.b) xs = GENLIST (\x.b) (LENGTH xs)``,
  HO_MATCH_MP_TAC rich_listTheory.SNOC_INDUCT
  \\ SRW_TAC [] [] \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GENLIST,GSYM ADD1,SNOC_APPEND]);

val MAP_CONST_REVERSE = prove(
  ``MAP (\x.b) (REVERSE xs) = MAP (\x.b) xs``,
  FULL_SIMP_TAC std_ss [MAP_EQ_GENLIST,LENGTH_REVERSE]);

val BC_SUBSTATE_IMP = prove(
  ``(bc.code p = SOME x) /\ BC_SUBSTATE bc bc1 /\ BC_REFINES (y1,y2) bc ==>
    (bc1.code p = SOME x)``,
  SIMP_TAC std_ss [BC_SUBSTATE_def,BC_REFINES_def] \\ METIS_TAC []);

val BC_SUBSTATE_BYTECODE = prove(
  ``!code p il ns ns1.
      CONTAINS_BYTECODE bc p code /\ BC_SUBSTATE bc bc1 /\ BC_REFINES (y1,y2) bc ==>
      CONTAINS_BYTECODE bc1 p code``,
  Induct \\ SIMP_TAC std_ss [CONTAINS_BYTECODE_def]
  \\ METIS_TAC [BC_SUBSTATE_IMP,BC_SUBSTATE_def]);

val BC_SUBSTATE_IMP_OK = prove(
  ``(bc.code p = SOME x) /\ BC_SUBSTATE bc bc1 /\ BC_CODE_OK bc ==>
    (bc1.code p = SOME x)``,
  SIMP_TAC std_ss [BC_SUBSTATE_def,BC_CODE_OK_def] \\ METIS_TAC []);

val BC_SUBSTATE_BYTECODE_OK = prove(
  ``!code p il ns ns1.
      CONTAINS_BYTECODE bc p code /\ BC_SUBSTATE bc bc1 /\ BC_CODE_OK bc ==>
      CONTAINS_BYTECODE bc1 p code``,
  Induct \\ SIMP_TAC std_ss [CONTAINS_BYTECODE_def]
  \\ METIS_TAC [BC_SUBSTATE_IMP_OK,BC_SUBSTATE_def]);

val BC_call_thm = prove(
  ``!fc n.
      CONTAINS_BYTECODE bc p (BC_call T (fc,n,NONE)) /\ (FUN_LOOKUP bc.compiled fc = SOME (pos,n)) ==>
      RTC iSTEP (stack,p,rs,bc) (stack,pos,rs,bc)``,
  SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,CONTAINS_BYTECODE_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
  \\ Q.EXISTS_TAC `(Val n::stack,p + bc.instr_length (iCONST_NUM n),rs,bc)`
  \\ STRIP_TAC THEN1
    (REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
     \\ MATCH_MP_TAC iSTEP_cases_imp
     \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,ADD_ASSOC,isVal_def,
         LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,APPEND,iLENGTH_APPEND,
         iLENGTH_def,CONTAINS_BYTECODE_def,BC_STEP_def])
  \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
  \\ Q.EXISTS_TAC `(Sym fc::Val n::stack,p + bc.instr_length (iCONST_NUM n) + bc.instr_length (iCONST_SYM fc),rs,bc)`
  \\ STRIP_TAC THEN1
    (REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
     \\ MATCH_MP_TAC iSTEP_cases_imp
     \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,ADD_ASSOC,
         LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,APPEND,iLENGTH_APPEND,
         iLENGTH_def,CONTAINS_BYTECODE_def,BC_STEP_def])
  THEN1
    (REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
     \\ MATCH_MP_TAC iSTEP_cases_imp
     \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,ADD_ASSOC,
         LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,APPEND,iLENGTH_APPEND,
         iLENGTH_def,CONTAINS_BYTECODE_def,BC_STEP_def]
     \\ METIS_TAC []));

val IMP_IMP = METIS_PROVE [] ``b /\ (c ==> d) ==> ((b ==> c) ==> d)``

val BC_PRINT_CONTAINS_BYTECODE = prove(
  ``!code p bc s.
      CONTAINS_BYTECODE (BC_PRINT bc s) p code = CONTAINS_BYTECODE bc p code``,
  Induct \\ ASM_SIMP_TAC std_ss [CONTAINS_BYTECODE_def]
  \\ SIMP_TAC (srw_ss()) [BC_PRINT_def]);

val BC_FAIL_CONTAINS_BYTECODE = prove(
  ``!code p bc s.
      CONTAINS_BYTECODE (BC_FAIL bc) p code = CONTAINS_BYTECODE bc p code``,
  Induct \\ ASM_SIMP_TAC std_ss [CONTAINS_BYTECODE_def]
  \\ SIMP_TAC (srw_ss()) [BC_FAIL_def]);

val n_times_CONS = prove(
  ``!args p stack.
      CONTAINS_BYTECODE bc p
        ([iCONST_SYM "NIL"] ++ n_times (LENGTH args) (iDATA opCONS)) ==>
      iSTEP^* (REVERSE args ++ stack,p,rs,bc)
              (list2sexp args::stack,p + iLENGTH bc.instr_length ([iCONST_SYM "NIL"] ++ n_times (LENGTH args) (iDATA opCONS)),rs,bc)``,
  Induct (* HO_MATCH_MP_TAC rich_listTheory.SNOC_INDUCT *) \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [REVERSE_DEF,APPEND,n_times_def,LENGTH,list2sexp_def]
    \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
    \\ MATCH_MP_TAC iSTEP_cases_imp
    \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def])
  \\ SIMP_TAC std_ss [REVERSE_DEF,GSYM APPEND_ASSOC,APPEND,LENGTH]
  \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
  \\ FULL_SIMP_TAC std_ss [GSYM (RW [APPEND_NIL] (Q.SPECL [`n`,`x`,`[]`] n_times_APPEND)),LENGTH]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [Once CONTAINS_BYTECODE_APPEND] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `(list2sexp args::h::stack,
           p + iLENGTH bc.instr_length ([iCONST_SYM "NIL"] ++ n_times
           (LENGTH args) (iDATA opCONS)),rs,bc)`
  \\ STRIP_TAC THEN1 (RES_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [list2sexp_def]
  \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
  \\ MATCH_MP_TAC iSTEP_cases_imp
  \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
       LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def]
  \\ FULL_SIMP_TAC std_ss [EVAL_DATA_OP_def,iLENGTH_def,iLENGTH_APPEND,
       AC ADD_COMM ADD_ASSOC] \\ Q.EXISTS_TAC `[h;list2sexp args]`
  \\ FULL_SIMP_TAC std_ss [LISP_CONS_def,EL,HD,TL] \\ EVAL_TAC);

val BC_PRINT_code = prove(
  ``((BC_PRINT bc z).code = bc.code) /\
    ((BC_PRINT bc z).instr_length = bc.instr_length) /\
    ((BC_FAIL bc).code = bc.code) /\
    ((BC_FAIL bc).instr_length = bc.instr_length)``,
  SRW_TAC [] [BC_PRINT_def,BC_FAIL_def]);

val BC_SUBSTATE_TAC =
  FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE
  \\ IMP_RES_TAC BC_ev_LENGTH \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE
  \\ IMP_RES_TAC BC_SUBSTATE_TRANS \\ FULL_SIMP_TAC std_ss []

val EXISTS_LEMMA = METIS_PROVE []
  ``(?y. (?x. P1 x /\ P2 x y) /\ Q y) = ?x. P1 x /\ ?y. P2 x y /\ Q y``

val WRITE_BYTECODE_SKIP = store_thm("WRITE_BYTECODE_SKIP",
  ``!new_code bc n i.
      n + iLENGTH bc.instr_length new_code <= i /\ (!h. 0 < bc.instr_length h) ==>
      ((WRITE_BYTECODE bc n new_code).code i = bc.code i)``,
  Induct \\ SIMP_TAC std_ss [WRITE_BYTECODE_def,iLENGTH_def,ADD_ASSOC]
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!bc n.bbb`
       (MP_TAC o Q.SPEC `(bc with code := (n =+ SOME h) bc.code)`)
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  \\ `0 < bc.instr_length h` by FULL_SIMP_TAC std_ss []
  \\ `~(n = i)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []);

val BC_CODE_OK_BC_ONLY_COMPILE = store_thm("BC_CODE_OK_BC_ONLY_COMPILE",
  ``BC_CODE_OK bc ==> BC_CODE_OK (BC_ONLY_COMPILE (params,body,bc))``,
  SIMP_TAC std_ss [BC_ONLY_COMPILE_def,LET_DEF]
  \\ `?new_code a2 q2 bcB. BC_ev_fun (params,body,bc) = (new_code,a2,q2,bcB)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL]
  \\ STRIP_TAC
  \\ `BC_JUMPS_OK bc` by FULL_SIMP_TAC std_ss [BC_CODE_OK_def,BC_JUMPS_OK_def]
  \\ IMP_RES_TAC BC_ev_fun_CONSTS \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [BC_CODE_OK_def,WRITE_BYTECODE_code_end]
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `!h. 0 < bcB.instr_length h` by METIS_TAC []
  \\ IMP_RES_TAC WRITE_BYTECODE_SKIP
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `bc.code = bcB.code` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ Q.PAT_X_ASSUM `!i. bcB.code_end <= i ==> (bc.code i = NONE)` MATCH_MP_TAC
  \\ DECIDE_TAC);

val BC_CODE_OK_BC_COMPILE = prove(
  ``BC_CODE_OK bc ==> BC_CODE_OK (BC_COMPILE (fname,params,body,bc))``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [BC_COMPILE_def,LET_DEF]
  \\ MATCH_MP_TAC BC_CODE_OK_BC_ONLY_COMPILE
  \\ POP_ASSUM MP_TAC \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val BC_ONLY_COMPILE_compiled_instr_length = prove(
  ``BC_CODE_OK bc ==>
    ((BC_ONLY_COMPILE (syms,body,bc)).compiled = bc.compiled) /\
    ((BC_ONLY_COMPILE (syms,body,bc)).instr_length = bc.instr_length) /\
    ((BC_ONLY_COMPILE (syms,body,bc)).io_out = bc.io_out) /\
    ((BC_ONLY_COMPILE (syms,body,bc)).ok = bc.ok)``,
  STRIP_TAC \\ SIMP_TAC std_ss [BC_ONLY_COMPILE_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ `BC_JUMPS_OK bc` by
       (POP_ASSUM MP_TAC \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ `?new_code a2 q2 bcB. BC_ev_fun (syms,body,bc) = (new_code,a2,q2,bcB)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC BC_ev_fun_CONSTS
  \\ FULL_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_code_end]);

val BC_COMPILE_compiled_instr_length = prove(
  ``BC_CODE_OK bc ==>
    ((BC_COMPILE (fc,syms,body,bc)).compiled =
     (BC_STORE_COMPILED bc fc (bc.code_end,LENGTH syms)).compiled) /\
    ((BC_COMPILE (fc,syms,body,bc)).instr_length = bc.instr_length) /\
    ((BC_COMPILE (fc,syms,body,bc)).io_out = bc.io_out) /\
    ((BC_COMPILE (fc,syms,body,bc)).ok = bc.ok)``,
  STRIP_TAC \\ FULL_SIMP_TAC std_ss [BC_COMPILE_def,LET_DEF]
  \\ `BC_CODE_OK (BC_STORE_COMPILED bc fc (bc.code_end,LENGTH syms))` by
       (POP_ASSUM MP_TAC \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [BC_ONLY_COMPILE_compiled_instr_length] \\ EVAL_TAC);

val WRITE_BYTECODE_SKIP_LESS = store_thm("WRITE_BYTECODE_SKIP_LESS",
  ``!new_code bc n i.
      i < n ==> ((WRITE_BYTECODE bc n new_code).code i = bc.code i)``,
  Induct \\ SIMP_TAC std_ss [WRITE_BYTECODE_def,iLENGTH_def,ADD_ASSOC]
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!bc n.bbb`
       (MP_TAC o Q.SPEC `(bc with code := (n =+ SOME h) bc.code)`)
  \\ `i < (n + bc.instr_length h)` by DECIDE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  \\ `~(n = i)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []);

val CONTAINS_BYTECODE_WRITE_BYTECODE = store_thm("CONTAINS_BYTECODE_WRITE_BYTECODE",
  ``!xs bc a.
      (!h. 0 < bc.instr_length h) ==>
      CONTAINS_BYTECODE (WRITE_BYTECODE bc a xs) a xs``,
  Induct \\ ASM_SIMP_TAC std_ss [CONTAINS_BYTECODE_def,WRITE_BYTECODE_code_end,
    WRITE_BYTECODE_def] \\ REVERSE (REPEAT STRIP_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!bc a. bbb`
      (MP_TAC o Q.SPEC `(bc with code := (a =+ SOME h) bc.code)`)
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ `0 < bc.instr_length h` by FULL_SIMP_TAC std_ss []
  \\ `a < a + bc.instr_length h` by DECIDE_TAC
  \\ IMP_RES_TAC WRITE_BYTECODE_SKIP_LESS \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]);

val CONTAINS_BYTECODE_code_end = prove(
  ``!xs a bc. CONTAINS_BYTECODE (bc with code_end := x) a xs = CONTAINS_BYTECODE bc a xs``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [CONTAINS_BYTECODE_def]);

val BC_REFINES_ONLY_COMPILE = store_thm("BC_REFINES_ONLY_COMPILE",
  ``BC_REFINES (fns,io) bc7 ==>
    BC_REFINES (fns,io) (BC_ONLY_COMPILE (syms,body,bc7))``,
  SIMP_TAC std_ss [BC_REFINES_def] \\ REVERSE (REPEAT STRIP_TAC)
  \\ FULL_SIMP_TAC std_ss [BC_ONLY_COMPILE_io_out,BC_CODE_OK_BC_ONLY_COMPILE]
  \\ IMP_RES_TAC BC_CODE_OK_BC_ONLY_COMPILE
  \\ IMP_RES_TAC BC_ONLY_COMPILE_compiled_instr_length
  THEN1 (FULL_SIMP_TAC std_ss [BC_CODE_OK_def])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [BC_FNS_ASSUM_def,FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`pcode`,`a5`,`bc4`,`bc5`] \\ ASM_SIMP_TAC std_ss []
  \\ REVERSE STRIP_TAC THEN1 (METIS_TAC [BC_SUBSTATE_ONLY_COMPILE,BC_SUBSTATE_TRANS])
  \\ `?new_code a2 q2 bcB. BC_ev_fun (syms,body,bc7) = (new_code,a2,q2,bcB)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [BC_ONLY_COMPILE_def,LET_DEF,WRITE_BYTECODE_code_end]
  \\ MATCH_MP_TAC (GEN_ALL BC_SUBSTATE_BYTECODE_OK) \\ Q.EXISTS_TAC `bc7`
  \\ ASM_SIMP_TAC std_ss []
  \\ `BC_SUBSTATE bc7 (BC_ONLY_COMPILE (syms,body,bc7))` by
        ASM_SIMP_TAC std_ss [BC_SUBSTATE_ONLY_COMPILE]
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [BC_ONLY_COMPILE_def,LET_DEF,WRITE_BYTECODE_code_end]);

val BC_REFINES_COMPILE = store_thm("BC_REFINES_COMPILE",
  ``fc NOTIN FDOM fns /\ BC_REFINES (fns,io) bc7 ==>
    BC_REFINES (fns |+ (fc,syms,body),io) (BC_COMPILE (fc,syms,body,bc7))``,
  SIMP_TAC std_ss [BC_REFINES_def] \\ REVERSE (REPEAT STRIP_TAC)
  \\ FULL_SIMP_TAC std_ss [BC_COMPILE_io_out,BC_CODE_OK_BC_COMPILE]
  \\ IMP_RES_TAC BC_CODE_OK_BC_COMPILE
  \\ IMP_RES_TAC BC_COMPILE_compiled_instr_length
  THEN1 (FULL_SIMP_TAC std_ss [BC_CODE_OK_def])
  \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [FUN_LOOKUP_def,FDOM_FUPDATE]
    \\ FULL_SIMP_TAC (srw_ss()) [BC_STORE_COMPILED_def,FUN_LOOKUP_def,LET_DEF]
    \\ FULL_SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INSERT]
    \\ STRIP_TAC \\ Cases_on `fc = x` \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [BC_FNS_ASSUM_def,FAPPLY_FUPDATE_THM,FDOM_FUPDATE,
       IN_INSERT]
  \\ STRIP_TAC \\ REVERSE (Cases_on `fc' = fc`) \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [BC_STORE_COMPILED_def,FUN_LOOKUP_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `BC_CODE_OK bc7` by METIS_TAC [BC_CODE_OK_def]
  \\ `BC_SUBSTATE bc7 (BC_COMPILE (fc,syms,body,bc7))` by
      (MATCH_MP_TAC (SIMP_RULE std_ss [] BC_COMPILE_SUBSTATE)
       \\ Q.PAT_X_ASSUM `zzz = FDOM fns` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
       \\ FULL_SIMP_TAC std_ss [GSPECIFICATION])
  THEN1 (METIS_TAC [BC_SUBSTATE_TRANS,BC_SUBSTATE_BYTECODE_OK])
  \\ `BC_CODE_OK (BC_COMPILE (fc,syms,body,bc7))` by METIS_TAC [BC_CODE_OK_BC_COMPILE]
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [BC_COMPILE_thm]
  \\ Q.PAT_ABBREV_TAC `bcA = BC_STORE_COMPILED bc fc zzz`
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ `?new_code a2 q2 bcB. BC_ev_fun (syms,body,bcA) = (new_code,a2,q2,bcB)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC (srw_ss()) [NOT_CONS_NIL,WRITE_BYTECODE_code_end]
  \\ REPEAT STRIP_TAC \\ `BC_JUMPS_OK bcA` by
   (Q.UNABBREV_TAC `bcA`
    \\ FULL_SIMP_TAC (srw_ss()) [BC_JUMPS_OK_def,BC_STORE_COMPILED_def,BC_CODE_OK_def])
  \\ IMP_RES_TAC BC_ev_fun_IMP
  \\ Q.LIST_EXISTS_TAC [`new_code`,`a2`,`bcA`,`bcB`]
  \\ IMP_RES_TAC BC_ev_LENGTH \\ FULL_SIMP_TAC std_ss []
  \\ `(bc7.code_end = bcA.code_end) /\ (bc7.instr_length = bcA.instr_length)` by
      (Q.UNABBREV_TAC `bcA` \\ FULL_SIMP_TAC (srw_ss()) [BC_STORE_COMPILED_def])
  \\ IMP_RES_TAC BC_ev_CONSTS \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC THEN1
   (SIMP_TAC std_ss [CONTAINS_BYTECODE_code_end]
    \\ MATCH_MP_TAC CONTAINS_BYTECODE_WRITE_BYTECODE
    \\ FULL_SIMP_TAC std_ss [BC_CODE_OK_def])
  \\ SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,WRITE_BYTECODE_code_end]
  \\ Cases_on `BC_CODE_OK bcB` \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [BC_CODE_OK_def,NOT_LESS,WRITE_BYTECODE_SKIP_LESS]);

val BC_CODE_OK_PRINT = prove(
  ``BC_CODE_OK (BC_PRINT bc str) = BC_CODE_OK bc``,
  SIMP_TAC (srw_ss()) [BC_PRINT_def,BC_CODE_OK_def]);

val BC_CODE_OK_FAIL = prove(
  ``BC_CODE_OK (BC_FAIL bc) = BC_CODE_OK bc``,
  SIMP_TAC (srw_ss()) [BC_FAIL_def,BC_CODE_OK_def]);

val lemma = BC_ev_ind
  |> Q.SPEC `\ret x y.
       let (fc,n,a1,q1,bc1) = x in
       let (code,a2,p2,bc0) = y in
         (~ret ==> (a2 = ssTEMP::DROP n a1))`
  |> Q.SPEC `\x y.
       let (xs,a1,q1,bc1) = x in
       let (code,a2,p2,bc0) = y in
         (a2 = MAP (\x.ssTEMP) xs ++ a1)`
  |> Q.SPEC `\ret x y.
       let (xs,a1,q1,bc1) = x in
       let (code,a2,p2,bc0) = y in
         (~ret ==> (a2 = ssTEMP :: a1))`

val drop_map =
  RW [LENGTH_MAP] (Q.SPEC `MAP f xs` rich_listTheory.BUTFIRSTN_LENGTH_APPEND)

val BC_ev_lemma_ret = prove(lemma |> concl |> rand,
  MATCH_MP_TAC lemma \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ TRY (Cases_on `ret`) \\ SIMP_TAC std_ss [BC_return_def,drop_map,MAP,APPEND]
  \\ Induct_on `xs` \\ ASM_SIMP_TAC std_ss [MAP,APPEND,CONS_11])

val BC_ev_NOT_RET_LEMMA = prove(
  ``BC_ev ret (exp,a,p,bc) (code,a2,p2,bc0) ==>
    (~ret ==> (a2 = ssTEMP::a))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC BC_ev_lemma_ret
  \\ FULL_SIMP_TAC std_ss [LET_DEF]);

val add_def_NOP = prove(
  ``!x y fns. x IN FDOM fns ==> (add_def fns (x,y) = fns)``,
  SIMP_TAC std_ss [add_def_def,FUNION_DEF,fmap_EXT]
  \\ SRW_TAC [] [EXTENSION] \\ METIS_TAC []);

val add_def_FUPDATE = prove(
  ``!x y fns. ~(x IN FDOM fns) ==> (add_def fns (x,y) = fns |+ (x,y))``,
  SIMP_TAC std_ss [add_def_def,FUNION_DEF,fmap_EXT,FAPPLY_FUPDATE_THM]
  \\ SRW_TAC [] [EXTENSION] \\ METIS_TAC []);

val lemma = RR_ev_ind
  |> Q.SPEC `\fc_args_env_fns_io_ok result_fns8_io8_ok8.
        !fc args a code a2 env stack p r rs fns fns8 io io8 ret p2 bc bc0 bc7 result ok ok8.
          (fc_args_env_fns_io_ok = (fc,args,env,fns,io,ok)) /\
          (result_fns8_io8_ok8 = (result,fns8,io8,ok8)) /\
          BC_REFINES (fns,io) bc7 /\ BC_SUBSTATE bc0 bc7 /\
          BC_ap ret (fc,LENGTH args,MAP (\x.ssTEMP) args ++ a,p,bc) (code,a2,p2,bc0) /\
          CONTAINS_BYTECODE bc7 p code /\
          STACK_INV env stack a /\ (bc7.ok = ok) ==>
          ?bc8.
            RTC iSTEP (REVERSE args ++ stack,p,r::rs,bc7)
              (if ret then iSTEP_ret_state a (result,stack,r,rs,bc8)
                      else (result::stack,p+iLENGTH bc.instr_length code,r::rs,bc8)) /\
            BC_REFINES (fns8,io8) bc8 /\ (bc8.ok = ok8) /\
            (~ret ==> (a2 = ssTEMP::a)) /\ fns SUBMAP fns8`
  |> Q.SPEC `\cs_env_fns_io_ok result_fns8_io8_ok8.
        !cs a code a2 env stack p ns r rs fns fns8 io io8 p2 bc bc0 bc7 result ok ok8.
          (cs_env_fns_io_ok = (cs,env,fns,io,ok)) /\
          (result_fns8_io8_ok8 = (result,fns8,io8,ok8)) /\
          BC_REFINES (fns,io) bc7 /\ BC_SUBSTATE bc0 bc7 /\
          BC_evl (cs,a,p,bc) (code,a2,p2,bc0) /\
          CONTAINS_BYTECODE bc7 p code /\
          STACK_INV env stack a /\ (bc7.ok = ok) ==>
          ?bc8.
            RTC iSTEP (stack,p,r::rs,bc7) (REVERSE result++stack,p+iLENGTH bc.instr_length code,r::rs,bc8) /\
            BC_REFINES (fns8,io8) bc8 /\ (bc8.ok = ok8) /\
            (a2 = MAP (\x.ssTEMP) (REVERSE result) ++ a) /\
            (LENGTH result = LENGTH cs) /\ fns SUBMAP fns8`
  |> Q.SPEC `\c_env_fns_io_ok result_fns8_io8_ok8.
        !c a code a2 env stack p r rs fns fns8 io io8 ret p2 bc bc0 bc7 result ok ok8.
          (c_env_fns_io_ok = (c,env,fns,io,ok)) /\
          (result_fns8_io8_ok8 = (result,fns8,io8,ok8)) /\
          BC_REFINES (fns,io) bc7 /\ BC_SUBSTATE bc0 bc7 /\
          BC_ev ret (c,a,p,bc) (code,a2,p2,bc0) /\
          CONTAINS_BYTECODE bc7 p code /\
          STACK_INV env stack a /\ (bc7.ok = ok) ==>
          ?bc8.
            RTC iSTEP (stack,p,r::rs,bc7)
              (if ret then iSTEP_ret_state a (result,stack,r,rs,bc8)
                      else (result::stack,p+iLENGTH bc.instr_length code,r::rs,bc8)) /\
            BC_REFINES (fns8,io8) bc8 /\ (bc8.ok = ok8) /\
            (~ret ==> (a2 = ssTEMP::a)) /\ fns SUBMAP fns8`

val goal = lemma |> concl |> rand

(*
  set_goal([],goal)
*)

val BC_ev_lemma = prove(goal,

  MATCH_MP_TAC lemma \\ SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 (* constant *)
   (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ SIMP_TAC std_ss [term_distinct,term_11,CONTAINS_BYTECODE_def,
          CONTAINS_BYTECODE_APPEND,SUBMAP_REFL]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [BC_return_code_def,APPEND_NIL,LENGTH]
    \\ SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,ADD_ASSOC]
    \\ Q.EXISTS_TAC `bc7` \\ ASM_SIMP_TAC std_ss []
    \\ Q.ABBREV_TAC `bc_insts =
        (if isVal s then
           [iCONST_NUM (getVal s)]
         else if isSym s then
           [iCONST_SYM (getSym s)]
         else
           [iCONST_NUM (LENGTH bc.consts); iCONST_LOOKUP])`
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s::stack,p + iLENGTH bc.instr_length bc_insts,r::rs,bc7)`
    \\ REVERSE STRIP_TAC THEN1
     (REVERSE (Cases_on `ret`)
      \\ FULL_SIMP_TAC std_ss [RTC_REFL,iLENGTH_def,BC_return_code_def,APPEND_NIL]
      \\ MATCH_MP_TAC BC_return_code_thm \\ ASM_SIMP_TAC std_ss [BC_return_code_def]
      \\ `bc.instr_length = bc7.instr_length` by (Cases_on `isDot s`
            \\ FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,BC_ADD_CONST_def])
      \\ METIS_TAC [BC_return_code_thm])
    \\ Q.UNABBREV_TAC `bc_insts`
    \\ Cases_on `isVal s` \\ FULL_SIMP_TAC std_ss [iLENGTH_def] THEN1
     (REPEAT (MATCH_MP_TAC RTC_SINGLE)
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def]
      \\ Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) [getVal_def,isVal_def]
      \\ FULL_SIMP_TAC std_ss [isDot_def,BC_SUBSTATE_def])
    \\ Cases_on `isSym s` \\ FULL_SIMP_TAC std_ss [iLENGTH_def] THEN1
     (REPEAT (MATCH_MP_TAC RTC_SINGLE)
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def]
      \\ Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) [getSym_def,isSym_def]
      \\ FULL_SIMP_TAC std_ss [isDot_def,BC_SUBSTATE_def])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(Val (LENGTH bc.consts)::stack,p + bc7.instr_length (iCONST_NUM (LENGTH bc.consts)),r::rs,bc7)`
    \\ STRIP_TAC THEN1
     (REPEAT (MATCH_MP_TAC RTC_SINGLE)
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def])
    THEN1
     (REPEAT (MATCH_MP_TAC RTC_SINGLE)
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def]
      \\ `isDot s` by (Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) [isVal_def,isSym_def,isDot_def])
      \\ FULL_SIMP_TAC std_ss [BC_SUBSTATE_def,GSYM APPEND_ASSOC,BC_ADD_CONST_def]
      \\ SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC std_ss [BC_SUBSTATE_def,GSYM APPEND_ASSOC,BC_ADD_CONST_def]
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,rich_listTheory.EL_APPEND2,EL,HD]
      \\ FULL_SIMP_TAC std_ss [APPEND,HD] \\ DECIDE_TAC))
  \\ STRIP_TAC THEN1 (* var lookup *)
   (ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ SIMP_TAC std_ss [term_distinct,term_11]
    \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO,PULL_EXISTS_IMP,CONTAINS_BYTECODE_def,
          CONTAINS_BYTECODE_APPEND,SUBMAP_REFL]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [BC_return_code_def,APPEND_NIL,LENGTH]
    \\ `VARS_IN_STACK a stack a'` by METIS_TAC [STACK_INV_def]
    \\ FULL_SIMP_TAC std_ss [VARS_IN_STACK_def] \\ RES_TAC
    \\ Q.EXISTS_TAC `bc7` \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(a ' x::stack,p + bc.instr_length (iLOAD n),r::rs,bc7)` \\ STRIP_TAC THEN1
     (REPEAT (MATCH_MP_TAC RTC_SINGLE)
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def]
      \\ FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
      \\ METIS_TAC [STACK_INV_def,SOME_11,VARS_IN_STACK_def])
    \\ REVERSE (Cases_on `ret`) \\ FULL_SIMP_TAC std_ss [RTC_REFL,iLENGTH_def]
    \\ METIS_TAC [BC_return_code_thm,BC_SUBSTATE_def])
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC (* Or [] *)
    \\ Q.PAT_X_ASSUM `BC_ev ret xxx yyy` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases]
    \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,NOT_CONS_NIL,CONS_11]
    \\ METIS_TAC [])
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `BC_ev xxx (Or e1,pppp) qqq` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,LENGTH_REVERSE,LENGTH,NOT_CONS_NIL,CONS_11]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL,NOT_CONS_NIL,CONS_11]
    \\ Q.PAT_X_ASSUM `!env.bbb` (MP_TAC o
         Q.SPECL [`a'`,`x_code`,`a1`,`stack`,`p`,`r`,`rs`,`F`,`q1`,`bc`,`bc1`,`bc7`])
    \\ ASM_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1 (METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_TRANS])
    \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `jump = iJUMP p2`
    \\ Q.ABBREV_TAC `jnil = iJNIL (p+addr)`
    \\ Q.EXISTS_TAC `bc8` \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1::stack,p + iLENGTH bc.instr_length x_code,r::rs,bc8)`
    \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1::s1::stack,p + iLENGTH bc.instr_length (x_code ++ [iLOAD 0]),r::rs,bc8)`
    \\ STRIP_TAC THEN1
     (MATCH_MP_TAC RTC_SINGLE
      \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def,isTrue_def]
      \\ FULL_SIMP_TAC std_ss [iLENGTH_def,iLENGTH_APPEND,EL,HD,ADD_ASSOC])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1::stack,p + iLENGTH bc.instr_length (x_code ++ [iLOAD 0; jnil]),r::rs,bc8)`
    \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1
     (MATCH_MP_TAC RTC_SINGLE
      \\ Q.UNABBREV_TAC `jnil`
      \\ FULL_SIMP_TAC std_ss [iLENGTH_def,iLENGTH_APPEND,AC ADD_ASSOC ADD_COMM]
      \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ `BC_SUBSTATE bc7 bc8` by
       (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
        \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
        \\ FULL_SIMP_TAC std_ss [])
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_def,AC ADD_COMM ADD_ASSOC]
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def,isTrue_def]
      \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM])
    \\ REVERSE (Cases_on `ret`) \\ FULL_SIMP_TAC std_ss [BC_return_code_def,APPEND] THEN1
     (Q.UNABBREV_TAC `jump`
      \\ FULL_SIMP_TAC std_ss [iLENGTH_def,iLENGTH_APPEND,AC ADD_ASSOC ADD_COMM]
      \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ MATCH_MP_TAC RTC_SINGLE
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def,isTrue_def]
      \\ FULL_SIMP_TAC std_ss [iLENGTH_def,iLENGTH_APPEND,EL,HD,ADD_ASSOC]
      \\ Q.PAT_X_ASSUM `p2 = xxx` (fn th => SIMP_TAC std_ss [Once th])
      \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM])
    \\ MATCH_MP_TAC BC_return_code_thm \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [BC_return_code_def,LENGTH,ADD1]
    \\ `BC_SUBSTATE bc7 bc8` by METIS_TAC [iSTEP_BC_SUBSTATE]
    \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
    \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss [])
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `BC_ev xxx (Or e1,pppp) qqq` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,LENGTH_REVERSE,LENGTH,NOT_CONS_NIL,CONS_11]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL,NOT_CONS_NIL,CONS_11]
    \\ Q.PAT_X_ASSUM `!env.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!env.bbb` (MP_TAC o
         Q.SPECL [`a'`,`x_code`,`a1`,`stack`,`p`,`r`,`rs`,`F`,`q1`,`bc`,`bc1`,`bc7`])
    \\ ASM_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1 (METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_TRANS])
    \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `jump = iJUMP p2`
    \\ Q.ABBREV_TAC `jnil = iJNIL (p+addr)`
    \\ Q.PAT_X_ASSUM `!env.bbb` (MP_TAC o
         Q.SPECL [`a'`,`z_code`,`a3`,`stack`,`p + addr + bc.instr_length iPOP`,`r`,`rs`,`ret`,`p2`,`bc1`,`bc0`,`bc8`])
    \\ ASM_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1
     (IMP_RES_TAC BC_ev_LENGTH
      \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM]
      \\ IMP_RES_TAC iSTEP_BC_SUBSTATE
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ ASM_SIMP_TAC std_ss []
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_SUBSTATE_def,BC_SUBSTATE_TRANS]
      \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM]
      \\ METIS_TAC [BC_SUBSTATE_TRANS,BC_SUBSTATE_BYTECODE])
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `bc8'` \\ ASM_SIMP_TAC std_ss []
    \\ `fns SUBMAP fns2` by METIS_TAC [SUBMAP_TRANS] \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1::stack,p + iLENGTH bc.instr_length x_code,r::rs,bc8)`
    \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(stack,p + addr + bc.instr_length iPOP,r::rs,bc8)`
    \\ ASM_SIMP_TAC std_ss [] \\ REVERSE STRIP_TAC THEN1
     (`bc1.instr_length = bc.instr_length` by METIS_TAC [BC_SUBSTATE_def,BC_ev_LENGTH]
      \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM]
      \\ Q.PAT_X_ASSUM `RTC iSTEP xxx yyy` MP_TAC
      \\ ASM_SIMP_TAC std_ss [ADD_ASSOC])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1::s1::stack,p + iLENGTH bc.instr_length (x_code ++ [iLOAD 0]),r::rs,bc8)`
    \\ STRIP_TAC THEN1
     (MATCH_MP_TAC RTC_SINGLE
      \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def,isTrue_def]
      \\ FULL_SIMP_TAC std_ss [iLENGTH_def,iLENGTH_APPEND,EL,HD,ADD_ASSOC])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1::stack,p + addr,r::rs,bc8)`
    \\ REVERSE STRIP_TAC THEN1
     (MATCH_MP_TAC RTC_SINGLE
      \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def,isTrue_def]
      \\ FULL_SIMP_TAC std_ss [iLENGTH_def,iLENGTH_APPEND,EL,HD,ADD_ASSOC])
    \\ MATCH_MP_TAC RTC_SINGLE
    \\ Q.UNABBREV_TAC `jnil`
    \\ FULL_SIMP_TAC std_ss [iLENGTH_def,iLENGTH_APPEND,AC ADD_ASSOC ADD_COMM]
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
    \\ `BC_SUBSTATE bc7 bc8` by
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ FULL_SIMP_TAC std_ss [])
    \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
    \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_def,AC ADD_COMM ADD_ASSOC]
    \\ MATCH_MP_TAC iSTEP_cases_imp
    \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def,isTrue_def])
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `BC_ev xxx (If e1 e2 e3,pppp) qqq` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,LENGTH_REVERSE,LENGTH]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL]
    \\ Q.PAT_X_ASSUM `!env. bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!env.bbb` (MP_TAC o
         Q.SPECL [`a'`,`x_code`,`a1`,`stack`,`p`,`r`,`rs`,`F`,`q1`,`bc`,`bc1`,`bc7`])
    \\ ASM_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1 METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_TRANS]
    \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `jump = iJUMP p2`
    \\ Q.ABBREV_TAC `jnil = iJNIL (q2 + bc.instr_length jump)`
    \\ Q.PAT_X_ASSUM `!env.bbb` (MP_TAC o
         Q.SPECL [`a'`,`z_code`,`a3`,`stack`,`p + iLENGTH bc.instr_length (x_code ++ [jnil] ++ y_code ++ [jump])`,`r`,`rs`,`ret`,`p2`,`bc2`,`bc0`,`bc8`])
    \\ ASM_SIMP_TAC std_ss []
    \\ `q2 + bc.instr_length jump = p + iLENGTH bc.instr_length (x_code ++ [jnil] ++ y_code ++ [jump])` by
          (IMP_RES_TAC BC_ev_LENGTH
           \\ SIMP_TAC std_ss [iLENGTH_APPEND,iLENGTH_def]
           \\ NTAC 3 (POP_ASSUM MP_TAC)
           \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ IMP_RES_TAC iSTEP_BC_SUBSTATE
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ FULL_SIMP_TAC std_ss [])
    \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `bc8'` \\ ASM_SIMP_TAC std_ss []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1::stack,p + iLENGTH bc.instr_length x_code,r::rs,bc8)`
    \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(stack,p + iLENGTH bc.instr_length (x_code ++ [jnil] ++ y_code ++ [jump]),r::rs,bc8)`
    \\ `bc2.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,ADD_ASSOC]
    \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE
    \\ MATCH_MP_TAC RTC_SINGLE
    \\ MATCH_MP_TAC iSTEP_cases_imp
    \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getSym_def,CONTAINS_BYTECODE_def,isTrue_def])
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `BC_ev xxx (If e1 e2 e3,pppp) qqq` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,LENGTH_REVERSE,LENGTH]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL]
    \\ Q.PAT_X_ASSUM `!env. bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!env.bbb` (MP_TAC o
         Q.SPECL [`a'`,`x_code`,`a1`,`stack`,`p`,`r`,`rs`,`F`,`q1`,`bc`,`bc1`,`bc7`])
    \\ ASM_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1 METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_TRANS]
    \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `jump = iJUMP p2`
    \\ Q.ABBREV_TAC `jnil = iJNIL (q2 + bc.instr_length jump)`
    \\ Q.PAT_X_ASSUM `!env.bbb` (MP_TAC o
         Q.SPECL [`a'`,`y_code`,`a2'`,`stack`,`p + iLENGTH bc.instr_length (x_code ++ [jnil])`,`r`,`rs`,`ret`,`q2`,`bc1`,`bc2`,`bc8`])
    \\ `q1 + bc.instr_length jnil = p + iLENGTH bc.instr_length (x_code ++ [jnil])` by
          (IMP_RES_TAC BC_ev_LENGTH
           \\ ASM_SIMP_TAC std_ss [iLENGTH_APPEND,iLENGTH_def] \\ DECIDE_TAC)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ FULL_SIMP_TAC std_ss [])
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `bc8'` \\ ASM_SIMP_TAC std_ss []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1::stack,p + iLENGTH bc.instr_length x_code,r::rs,bc8)`
    \\ ASM_SIMP_TAC std_ss []
    \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ `BC_SUBSTATE bc7 bc8` by
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ FULL_SIMP_TAC std_ss [])
    \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(stack,p + iLENGTH bc.instr_length (x_code ++ [jnil]),r::rs,bc8)`
    \\ REPEAT STRIP_TAC THEN1
     (MATCH_MP_TAC RTC_SINGLE
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE
      \\ Q.UNABBREV_TAC `jnil`
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,iLENGTH_APPEND,BC_STEP_def,
           LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,isTrue_def,iLENGTH_def,ADD_ASSOC])
    \\ Cases_on `ret` \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s::stack,p + iLENGTH bc.instr_length (x_code ++ [jnil] ++ y_code),r::rs,bc8')`
    \\ `bc1.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,ADD_ASSOC]
    \\ `BC_SUBSTATE bc7 bc8'` by
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ FULL_SIMP_TAC std_ss [])
    \\ MATCH_MP_TAC RTC_SINGLE
    \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE
    \\ Q.UNABBREV_TAC `jump`
    \\ MATCH_MP_TAC iSTEP_cases_imp
    \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,isTrue_def]
    \\ IMP_RES_TAC BC_ev_LENGTH
    \\ FULL_SIMP_TAC std_ss [iLENGTH_def]
    \\ Q.PAT_X_ASSUM `bc1.instr_length = bc.instr_length` MP_TAC
    \\ `bc2.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `BC_ev zzz (LamApp xs e ys,aaaa) xzzz` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,LENGTH_REVERSE,LENGTH,NOT_CONS_NIL,CONS_11]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL]
    \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!env. bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!env. bbb`
         (MP_TAC o Q.SPECL [`a'`,`code1`,`a1`,`stack`,`p`,`r`,`rs`,`q1`,`bc`,`bc1`,`bc7`])
    \\ `BC_SUBSTATE bc1 bc7` by
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ FULL_SIMP_TAC std_ss [])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!env. bbb`
         (MP_TAC o Q.SPECL [`MAP (ssVAR) (REVERSE xs) ++ a'`,
            `code2`,`a2'`,`REVERSE sl ++ stack`,`p + iLENGTH bc.instr_length code1`,`r`,`rs`,`ret`,`q2`,`bc1`,`bc0`,`bc8`])
    \\ `BC_SUBSTATE bc0 bc8` by
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ FULL_SIMP_TAC std_ss []) \\ ASM_SIMP_TAC std_ss []
    \\ `BC_SUBSTATE bc7 bc8` by
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ FULL_SIMP_TAC std_ss []) \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1
     (`DROP (LENGTH ys) (MAP (\x. ssTEMP) (REVERSE sl) ++ a') = a'` by
       (`LENGTH ys = LENGTH (MAP (\x. ssTEMP) (REVERSE sl))` by ASM_SIMP_TAC std_ss [LENGTH_MAP,LENGTH_REVERSE]
        \\ METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND])
      \\ IMP_RES_TAC BC_ev_LENGTH \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ FULL_SIMP_TAC std_ss []
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ FULL_SIMP_TAC std_ss []
      \\ ASM_SIMP_TAC std_ss [] \\ MATCH_MP_TAC STACK_INV_VarBind_2
      \\ ASM_SIMP_TAC std_ss [LENGTH_MAP])
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `bc8'` \\ ASM_SIMP_TAC std_ss []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(REVERSE sl ++ stack,p + iLENGTH bc.instr_length code1,r::rs,bc8)`
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LENGTH_MAP,iSTEP_ret_state_APPEND_MAP]
    \\ `LENGTH sl = LENGTH xs` by FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LENGTH_MAP,iSTEP_ret_state_APPEND_MAP]
    \\ Cases_on `ret` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(x::(REVERSE sl ++ stack),
          p + iLENGTH bc.instr_length code1 +
          iLENGTH bc1.instr_length code2,r::rs,bc8')`
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_def,iLENGTH_APPEND,ADD_ASSOC]
    \\ `BC_SUBSTATE bc7 bc8'` by
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ FULL_SIMP_TAC std_ss [])
    \\ IMP_RES_TAC BC_SUBSTATE_IMP
    \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ `bc1.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ `bc8'.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
    \\ MATCH_MP_TAC iSTEP_cases_imp
    \\ ASM_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,
         LENGTH,CONS_11,STACK_INV_lemma,APPEND,BC_STEP_def,CONTAINS_BYTECODE_def]
    \\ Q.EXISTS_TAC `REVERSE sl`
    \\ ASM_SIMP_TAC std_ss [LENGTH_REVERSE,iLENGTH_def])
  \\ STRIP_TAC THEN1
   (REVERSE (REPEAT STRIP_TAC)
    \\ Q.PAT_X_ASSUM `BC_ev xxx (App fc el,yyy) ddd` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,LENGTH_REVERSE,LENGTH]
    \\ `!f. fc <> Fun f` by FULL_SIMP_TAC std_ss [NOT_isFun]
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL]
    \\ Q.PAT_X_ASSUM `!env. bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!env. bbb`
         (MP_TAC o Q.SPECL [`a'`,`code1`,`a1`,`stack`,`p`,`r`,`rs`,`q1`,`bc`,`bc1`,`bc7`])
    \\ `BC_SUBSTATE bc1 bc7` by
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ FULL_SIMP_TAC std_ss [])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!env code. bbb`
         (MP_TAC o Q.SPECL [`a'`,`code2`,`a2`,`stack`,`q1`,`r`,`rs`,`ret`,`p2`,`bc1`,`bc0`,`bc8`])
    \\ `BC_SUBSTATE bc0 bc8` by
     (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
      \\ FULL_SIMP_TAC std_ss [])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [MAP_CONST_REVERSE]
      \\ IMP_RES_TAC BC_ev_LENGTH \\ FULL_SIMP_TAC std_ss []
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ FULL_SIMP_TAC std_ss []
      \\ `BC_SUBSTATE bc7 bc8` by
       (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC iSTEP_BC_SUBSTATE \\ IMP_RES_TAC BC_ev_LENGTH
        \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ IMP_RES_TAC BC_SUBSTATE_TRANS
        \\ FULL_SIMP_TAC std_ss [])
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE \\ FULL_SIMP_TAC std_ss [])
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `bc8'` \\ ASM_SIMP_TAC std_ss []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(REVERSE args ++ stack,q1,r::rs,bc8)` \\ ASM_SIMP_TAC std_ss []
    \\ IMP_RES_TAC BC_ev_LENGTH \\ FULL_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [iLENGTH_APPEND,iLENGTH_def,ADD_ASSOC])
  \\ STRIP_TAC THEN1
   (REVERSE (REPEAT STRIP_TAC)
    \\ Q.PAT_X_ASSUM `BC_ap zzz (PrimitiveFun fc,sdf) szzz` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,func_distinct,term_11,func_11,LENGTH_REVERSE,LENGTH]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL]
    \\ `DROP (LENGTH args) (MAP (\x. ssTEMP) args ++ a') = a'` by (METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND,LENGTH_MAP,LENGTH_REVERSE])
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [BC_return_code_def,LENGTH,iLENGTH_def,APPEND]
    \\ Q.EXISTS_TAC `bc7` \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(f args::stack,p + bc.instr_length (iDATA fc),r::rs,bc7)`
    \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH]
    \\ STRIP_TAC THEN1
     (REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,
           LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,BC_STEP_def]
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ ASM_SIMP_TAC std_ss [APPEND_11] \\ METIS_TAC [])
    \\ REVERSE (Cases_on `ret`) THEN1 (ASM_SIMP_TAC std_ss [RTC_REFL])
    \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ MATCH_MP_TAC (GEN_ALL BC_return_code_thm)
    \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ Q.EXISTS_TAC `a` \\ ASM_SIMP_TAC std_ss []
    \\ METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND,LENGTH_MAP,LENGTH_REVERSE])
  \\ STRIP_TAC THEN1
   (REPEAT MOVE_TAC
    \\ Q.PAT_X_ASSUM `BC_ev zzz (App (Fun xx) yy,xxxx) yyyyyyy` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,LENGTH_REVERSE,LENGTH]
    \\ ASM_SIMP_TAC std_ss [isFun_def,func_11]
    \\ REVERSE (Cases_on `ret`) \\ ASM_SIMP_TAC std_ss [] THEN1
     (REVERSE (REPEAT STRIP_TAC) \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC]
      \\ POP_ASSUM MP_TAC
      \\ SIMP_TAC std_ss [BC_return_def]
      \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,LENGTH_REVERSE,LENGTH]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,BC_return_code_def,APPEND_NIL]
      \\ Q.PAT_X_ASSUM `!env. bbb` MP_TAC
      \\ Q.PAT_X_ASSUM `!env. bbb`
          (MP_TAC o Q.SPECL [`a'`,`code'`,`a2'`,`stack`,`p`,`r`,`rs`,`q2`,`bc`,`bc0`,`bc7`])
      \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND]
      \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `BC_REFINES (fns1,io1) bc8` (fn th =>
           ASSUME_TAC th THEN MP_TAC th)
      \\ SIMP_TAC std_ss [Once BC_FNS_ASSUM_def,Once BC_REFINES_def]
      \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `!fc params.bbb` (MP_TAC o Q.SPECL [`fc`,`params`,`exp`])
      \\ ASM_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [PULL_EXISTS_IMP,PULL_FORALL_IMP,GSYM AND_IMP_INTRO]
      \\ `DROP (LENGTH (el:term list)) (MAP (\x. ssTEMP) (REVERSE args) ++ a') = a'` by (METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND,LENGTH_MAP,LENGTH_REVERSE])
      \\ ASM_SIMP_TAC std_ss [AND_IMP_INTRO]
      (* \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 METIS_TAC [SUBMAP_DEF] *)
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND]
      \\ Q.PAT_X_ASSUM `!a code.bbb` (MP_TAC o
         Q.SPECL [`MAP ssVAR (REVERSE params)`,`pcode`,`a5`,
                  `REVERSE args ++ stack`,`p'`,`(p +
           iLENGTH bc.instr_length (code' ++ BC_call F (fc,LENGTH (el:term list),FUN_LOOKUP bc.compiled fc)))`,`r::rs`,`T`,`p' + iLENGTH bc8.instr_length pcode`,`bc4`,`bc5`,`bc8`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (ASM_SIMP_TAC std_ss [STACK_INV_VarBind,BC_SUBSTATE_REFL])
      \\ REPEAT STRIP_TAC
      \\ Q.EXISTS_TAC `bc8'` \\ ASM_SIMP_TAC std_ss []
      \\ IMP_RES_TAC SUBMAP_TRANS \\ ASM_SIMP_TAC std_ss []
      \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
      \\ Q.EXISTS_TAC `(REVERSE args ++ stack,p',(p +
           iLENGTH bc.instr_length (code' ++ BC_call F (fc,LENGTH el,FUN_LOOKUP bc.compiled fc)))::r::rs,bc8)`
      \\ REVERSE STRIP_TAC THEN1
       (FULL_SIMP_TAC std_ss [iSTEP_ret_state_def,HD,getVal_def,APPEND,BC_call_def,BC_call_aux_def,BC_call_aux_def]
        \\ `DROP (LENGTH params) (REVERSE args ++ stack) = stack` by
             METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND,LENGTH_MAP,LENGTH_REVERSE]
        \\ FULL_SIMP_TAC std_ss [LENGTH_MAP,LENGTH_REVERSE])
      \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
      \\ Q.EXISTS_TAC `(REVERSE args ++ stack,p + iLENGTH bc.instr_length code',r::rs,bc8)`
      \\ ASM_SIMP_TAC std_ss []
      \\ REVERSE (Cases_on `FUN_LOOKUP bc.compiled fc`) THEN1
         (`BC_SUBSTATE bc bc7` by BC_SUBSTATE_TAC
          \\ `BC_SUBSTATE bc bc8` by BC_SUBSTATE_TAC
          \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
          \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
          \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
          \\ `FUN_LOOKUP bc8.compiled fc = FUN_LOOKUP bc.compiled fc` by (METIS_TAC [BC_SUBSTATE_def,NOT_SOME_NONE])
          \\ FULL_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,CONTAINS_BYTECODE_def]
          \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC BC_SUBSTATE_IMP
          \\ REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
          \\ MATCH_MP_TAC iSTEP_cases_imp
          \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,ADD_ASSOC,BC_STEP_def,
               LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,APPEND,iLENGTH_APPEND,iLENGTH_def])
      \\ FULL_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,CONTAINS_BYTECODE_def]
      \\ `BC_SUBSTATE bc bc7` by BC_SUBSTATE_TAC
      \\ `BC_SUBSTATE bc bc8` by BC_SUBSTATE_TAC
      \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,CONTAINS_BYTECODE_def]
      \\ IMP_RES_TAC BC_SUBSTATE_IMP
      \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
      \\ Q.EXISTS_TAC `(Val (LENGTH el)::(REVERSE args ++ stack),p + iLENGTH bc.instr_length (code' ++ [iCONST_NUM (LENGTH el)]),r::rs,bc8)`
      \\ STRIP_TAC THEN1
         (REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
          \\ MATCH_MP_TAC iSTEP_cases_imp
          \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,ADD_ASSOC,BC_STEP_def,
               LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,APPEND,iLENGTH_APPEND,iLENGTH_def])
      \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
      \\ Q.EXISTS_TAC `(Sym fc::Val (LENGTH el)::(REVERSE args ++ stack),p + iLENGTH bc.instr_length (code' ++ [iCONST_NUM (LENGTH el);iCONST_SYM fc]),r::rs,bc8)`
      \\ STRIP_TAC THEN1
         (REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
          \\ MATCH_MP_TAC iSTEP_cases_imp
          \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,ADD_ASSOC,BC_STEP_def,
               LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,APPEND,iLENGTH_APPEND,iLENGTH_def])
      THEN1
         (REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
          \\ MATCH_MP_TAC iSTEP_cases_imp
          \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,ADD_ASSOC,
               LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,APPEND,iLENGTH_APPEND,iLENGTH_def]
          \\ FULL_SIMP_TAC (srw_ss()) [BC_STEP_def]))
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC]
    \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `padding = LENGTH el - LENGTH a'`
    \\ Q.ABBREV_TAC `a9 = n_times padding ssTEMP ++ a'`
    \\ Q.ABBREV_TAC `stack9 = n_times padding (Sym "NIL") ++ stack`
    \\ `STACK_INV a stack9 a9` by
       (Q.UNABBREV_TAC `stack9` \\ Q.UNABBREV_TAC `a9` \\ IMP_RES_TAC n_times_iCONST)
    \\ MP_TAC (Q.SPECL [`padding`,`a'`,`stack`,`a`,`bc7`,`p`] n_times_iCONST)
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ SIMP_TAC std_ss [EXISTS_LEMMA]
    \\ Q.EXISTS_TAC `(stack9,p + iLENGTH bc.instr_length (n_times padding (iCONST_SYM "NIL")),r::rs,bc7)`
    \\ `BC_SUBSTATE bc bc7` by BC_SUBSTATE_TAC
    \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!env. bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!env. bbb`
       (MP_TAC o Q.SPECL [`a9`,`code'`,`a2'`,`stack9`,`p + iLENGTH bc.instr_length (n_times padding (iCONST_SYM "NIL"))`,`r`,`rs`,`q2`,`bc`,`bc0`,`bc7`])
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC BC_ev_LENGTH
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND]
    \\ Q.PAT_X_ASSUM `BC_REFINES (fns1,io1) bc8` (fn th =>
         ASSUME_TAC th THEN MP_TAC th)
    \\ SIMP_TAC std_ss [Once BC_FNS_ASSUM_def,Once BC_REFINES_def]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!fc params. bbb` (MP_TAC o Q.SPECL [`fc`,`params`,`exp`])
    \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ `BC_SUBSTATE bc bc8` by BC_SUBSTATE_TAC
    \\ `bc.instr_length = bc8.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ SIMP_TAC std_ss [EXISTS_LEMMA]
    \\ Q.EXISTS_TAC `(REVERSE args ++ stack9,p + iLENGTH bc.instr_length (n_times padding (iCONST_SYM "NIL") ++ code'),r::rs,bc8)`
    \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [iLENGTH_APPEND,ADD_ASSOC])
    \\ Q.PAT_X_ASSUM `!a b.bbb` (MP_TAC o Q.SPECL
         [`MAP ssVAR (REVERSE params)`,`pcode`,`a5`,`REVERSE args++DROP (LENGTH (a':stack_slot list)) stack`,`p'`,`r`,`rs`,`T`,`p' + iLENGTH bc.instr_length pcode`,`bc4`,`bc5`,`bc8`])
    \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1
     (ASM_SIMP_TAC std_ss [STACK_INV_VarBind,iSTEP_ret_state_APPEND_MAP])
    \\ REPEAT STRIP_TAC
    \\ `fns SUBMAP fns2` by METIS_TAC [SUBMAP_TRANS]
    \\ Q.EXISTS_TAC `bc8'` \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(REVERSE args ++ DROP (LENGTH a') stack,p',r::rs,bc8)`
    \\ ASM_SIMP_TAC std_ss []
    \\ REVERSE STRIP_TAC THEN1
     (Q.PAT_X_ASSUM `RTC iSTEP xxx yyy` MP_TAC
      \\ ASM_SIMP_TAC std_ss [(RW[APPEND_NIL](Q.INST [`a2`|->`[]`] iSTEP_ret_state_APPEND_MAP))]
      \\ ASM_SIMP_TAC std_ss [iSTEP_ret_state_def,LENGTH,DROP_0])
    \\ Q.UNABBREV_TAC `a9` \\ Q.UNABBREV_TAC `stack9`
    \\ `?stack1 stack2. (LENGTH a' = LENGTH stack1) /\
                        (stack = stack1 ++ stack2)` by
          METIS_TAC [LENGTH_LESS_EQ_LENGTH_IMP,STACK_INV_def]
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.BUTFIRSTN_LENGTH_APPEND]
    \\ SIMP_TAC std_ss [APPEND_ASSOC]
    \\ REVERSE (Cases_on `padding = 0`) THEN1
     (`LENGTH stack1 <= LENGTH el /\
       (padding + LENGTH stack1 = LENGTH el)` by
         (Q.UNABBREV_TAC `padding` \\ POP_ASSUM MP_TAC
          \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ DECIDE_TAC)
      \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
      \\ Q.EXISTS_TAC `(REVERSE args ++ stack2,
                        p + iLENGTH bc.instr_length (n_times padding (iCONST_SYM "NIL")) + iLENGTH bc.instr_length code' + iLENGTH bc.instr_length (n_times (LENGTH (REVERSE args)) (iSTORE (LENGTH (REVERSE args) - 1))),r::rs,bc8)`
      \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC std_ss [iLENGTH_APPEND,ADD_ASSOC]
        \\ `BC_SUBSTATE bc bc8` by BC_SUBSTATE_TAC
        \\ `bc.instr_length = bc8.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC (RW [APPEND,APPEND_NIL,APPEND_ASSOC]
          (Q.SPECL [`xs1++xs2`,`REVERSE args`,`[]`,`bc8`,`q`,`stack2`] n_times_iSTORE))
        \\ ASM_SIMP_TAC std_ss [LENGTH_n_times,LENGTH_REVERSE,LENGTH_APPEND]
        \\ Q.PAT_X_ASSUM `padding + LENGTH stack1 = LENGTH el` (MP_TAC o GSYM)
        \\ `~(padding + LENGTH stack1 <= LENGTH stack1)` by DECIDE_TAC
        \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC,iLENGTH_APPEND]
        \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
        \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC (GEN_ALL BC_SUBSTATE_BYTECODE)
        \\ FULL_SIMP_TAC std_ss []
        \\ Q.LIST_EXISTS_TAC [`io`,`fns`,`bc7`]
        \\ FULL_SIMP_TAC std_ss [])
      \\ `LENGTH stack1 - LENGTH el = 0` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [gen_popn_def,APPEND_NIL,LENGTH]
      \\ REVERSE (Cases_on `FUN_LOOKUP bc.compiled fc`) THEN1
         (`BC_SUBSTATE bc bc7` by BC_SUBSTATE_TAC
          \\ `BC_SUBSTATE bc bc8` by BC_SUBSTATE_TAC
          \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
          \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
          \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
          \\ `FUN_LOOKUP bc8.compiled fc = FUN_LOOKUP bc.compiled fc` by METIS_TAC [BC_SUBSTATE_def,NOT_SOME_NONE]
          \\ FULL_SIMP_TAC std_ss []
          \\ FULL_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,CONTAINS_BYTECODE_def]
          \\ IMP_RES_TAC BC_SUBSTATE_IMP
          \\ `LENGTH el = LENGTH args` by DECIDE_TAC
          \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,AC ADD_ASSOC ADD_COMM,LENGTH_REVERSE]
          \\ Q.PAT_X_ASSUM `padding + LENGTH stack1 = LENGTH args` ASSUME_TAC
          \\ FULL_SIMP_TAC std_ss []
          \\ REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
          \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,LENGTH_REVERSE]
          \\ MATCH_MP_TAC iSTEP_cases_imp
          \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,
               LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,APPEND,
               AC ADD_ASSOC ADD_COMM,LENGTH_REVERSE,iLENGTH_APPEND])
      \\ MATCH_MP_TAC (GEN_ALL BC_call_thm)
      \\ Q.EXISTS_TAC `fc` \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE]
      \\ FULL_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,CONTAINS_BYTECODE_def]
      \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
      \\ `FUN_LOOKUP bc8.compiled fc = FUN_LOOKUP bc8.compiled fc` by METIS_TAC [BC_SUBSTATE_def,NOT_SOME_NONE]
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC BC_SUBSTATE_IMP
      \\ `LENGTH el = LENGTH args` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,iLENGTH_APPEND]
      \\ Q.PAT_X_ASSUM `padding + LENGTH stack1 = LENGTH args` ASSUME_TAC
      \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [n_times_def,APPEND_NIL,APPEND]
    \\ `LENGTH args <= LENGTH stack1` by METIS_TAC [markerTheory.Abbrev_def]
    \\ `?stack1A stack1B. (stack1 = stack1A ++ stack1B) /\ (LENGTH stack1B = LENGTH args)`
         by METIS_TAC [LESS_EQ_IMP_APPEND]
    \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,iLENGTH_def]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(stack1A ++ REVERSE args ++ stack2,p + iLENGTH  bc.instr_length code' + iLENGTH  bc.instr_length (n_times (LENGTH (REVERSE args)) (iSTORE (LENGTH (REVERSE args ++ stack1A) - 1))),r::rs,bc8)`
    \\ STRIP_TAC THEN1
     (`BC_SUBSTATE bc bc8` by BC_SUBSTATE_TAC
      \\ `bc.instr_length = bc8.instr_length` by METIS_TAC [BC_SUBSTATE_def]
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC n_times_iSTORE
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REVERSE,LENGTH_n_times]
      \\ Q.PAT_X_ASSUM `LENGTH args = LENGTH el` ASSUME_TAC
      \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,iLENGTH_APPEND,iLENGTH_def]
      \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
      \\ METIS_TAC [BC_SUBSTATE_BYTECODE,ADD_ASSOC,iLENGTH_APPEND])
    \\ ASM_SIMP_TAC std_ss [LENGTH_REVERSE]
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ Q.PAT_X_ASSUM `LENGTH args = LENGTH el` ASSUME_TAC
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(REVERSE args ++ stack2,p + iLENGTH bc.instr_length code' +
         iLENGTH bc.instr_length (n_times (LENGTH el) (iSTORE (LENGTH (REVERSE args) + LENGTH stack1A - 1)) ++ gen_popn (LENGTH stack1A)),r::rs,bc8)`
    \\ STRIP_TAC THEN1
      (`BC_SUBSTATE bc bc8` by BC_SUBSTATE_TAC
       \\ `bc.instr_length = bc8.instr_length` by METIS_TAC [BC_SUBSTATE_def]
       \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,iLENGTH_APPEND,ADD_ASSOC]
       \\ MATCH_MP_TAC gen_popn_thm
       \\ FULL_SIMP_TAC std_ss [iLENGTH_def,AC ADD_ASSOC ADD_COMM,LENGTH_REVERSE]
       \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
       \\ METIS_TAC [BC_SUBSTATE_BYTECODE,ADD_ASSOC,iLENGTH_APPEND])
    \\ REVERSE (Cases_on `FUN_LOOKUP bc.compiled fc`) THEN1
       (`BC_SUBSTATE bc bc7` by BC_SUBSTATE_TAC
        \\ `BC_SUBSTATE bc bc8` by BC_SUBSTATE_TAC
        \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
        \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
        \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
        \\ `FUN_LOOKUP bc8.compiled fc = FUN_LOOKUP bc.compiled fc` by METIS_TAC [BC_SUBSTATE_def,NOT_SOME_NONE]
        \\ FULL_SIMP_TAC std_ss []
        \\ FULL_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,CONTAINS_BYTECODE_def]
        \\ IMP_RES_TAC BC_SUBSTATE_IMP
        \\ `LENGTH el = LENGTH args` by DECIDE_TAC
        \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,AC ADD_ASSOC ADD_COMM,LENGTH_REVERSE]
        \\ FULL_SIMP_TAC std_ss []
        \\ REPEAT STRIP_TAC \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
        \\ FULL_SIMP_TAC std_ss [iLENGTH_APPEND,LENGTH_REVERSE]
        \\ MATCH_MP_TAC iSTEP_cases_imp
        \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,
             LENGTH,CONS_11,STACK_INV_lemma,CONTAINS_BYTECODE_def,APPEND,
             AC ADD_ASSOC ADD_COMM,LENGTH_REVERSE,iLENGTH_APPEND])
    \\ MATCH_MP_TAC (GEN_ALL BC_call_thm)
    \\ Q.EXISTS_TAC `fc` \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE]
    \\ FULL_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,CONTAINS_BYTECODE_def]
    \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
    \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ `bc8.instr_length = bc.instr_length` by METIS_TAC [BC_ev_LENGTH,BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC BC_SUBSTATE_IMP
    \\ `LENGTH el = LENGTH args` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,iLENGTH_APPEND]
    \\ Q.PAT_X_ASSUM `padding + LENGTH stack1 = LENGTH args` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [])
  \\ STRIP_TAC THEN1
   (REVERSE (REPEAT STRIP_TAC)
    \\ Q.PAT_X_ASSUM `BC_ap zzz (Print,xxx) szzz` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,func_distinct,term_11,func_11,LENGTH_REVERSE,LENGTH]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL]
    \\ `DROP (LENGTH args) (MAP (\x. ssTEMP) args ++ a') = a'` by
         (METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND,LENGTH_MAP,LENGTH_REVERSE])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `BC_PRINT bc7 (sexp2string (list2sexp (Sym "PRINT"::args)) ++ "\n")`
    \\ REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [BC_REFINES_def,BC_CODE_OK_PRINT] \\ REVERSE STRIP_TAC
      THEN1 (FULL_SIMP_TAC (srw_ss()) [BC_PRINT_def])
      \\ Q.PAT_X_ASSUM `BC_FNS_ASSUM fns bc7` MP_TAC
      \\ SIMP_TAC std_ss [BC_FNS_ASSUM_def,BC_PRINT_CONTAINS_BYTECODE]
      \\ FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,BC_CODE_OK_PRINT]
      \\ FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,BC_PRINT_def] \\ METIS_TAC [])
    \\ Q.ABBREV_TAC `ys = [iCONST_SYM "NIL"] ++ n_times (LENGTH args) (iDATA opCONS)`
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(list2sexp args :: stack,p + iLENGTH bc.instr_length ys,r::rs,bc7)`
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND] \\ Q.UNABBREV_TAC `ys`
      \\ `bc7.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
      \\ IMP_RES_TAC n_times_CONS  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
    \\ `bc7.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,CONTAINS_BYTECODE_def]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(Sym "PRINT" :: list2sexp args :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "PRINT"]),r::rs,bc7)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(list2sexp args :: Sym "PRINT" :: list2sexp args :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "PRINT"; iLOAD 1]),r::rs,bc7)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def]
       \\ EVAL_TAC \\ DECIDE_TAC)
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(list2sexp (Sym "PRINT"::args) :: list2sexp args :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "PRINT"; iLOAD 1; iDATA opCONS]),r::rs,bc7)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def]
       \\ Q.EXISTS_TAC `[Sym "PRINT";list2sexp args]` \\ EVAL_TAC)
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(list2sexp (Sym "PRINT"::args) :: list2sexp args :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "PRINT"; iLOAD 1; iDATA opCONS; iPRINT]),r::rs,BC_PRINT bc7 (sexp2string (list2sexp (Sym "PRINT"::args)) ++ "\n"))`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(Sym "NIL" :: list2sexp (Sym "PRINT"::args) :: list2sexp args :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "PRINT"; iLOAD 1; iDATA opCONS; iPRINT; iCONST_SYM "NIL"]),r::rs,BC_PRINT bc7 (sexp2string (list2sexp (Sym "PRINT"::args)) ++ "\n"))`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def,BC_PRINT_code])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(Sym "NIL" :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "PRINT"; iLOAD 1; iDATA opCONS; iPRINT; iCONST_SYM "NIL"; iPOPS 2]),r::rs,BC_PRINT bc7 (sexp2string (list2sexp (Sym "PRINT"::args)) ++ "\n"))`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def,BC_PRINT_code]
       \\ Q.EXISTS_TAC `list2sexp (Sym "PRINT"::args)::list2sexp args::[]` \\ EVAL_TAC)
    THEN
     (REVERSE (Cases_on `ret`)
      \\ FULL_SIMP_TAC std_ss [RTC_REFL,iLENGTH_def,BC_return_code_def,APPEND_NIL]
      \\ MATCH_MP_TAC BC_return_code_thm
      \\ FULL_SIMP_TAC std_ss [BC_return_code_def,BC_PRINT_CONTAINS_BYTECODE]))
  \\ STRIP_TAC THEN1
   (REVERSE (REPEAT STRIP_TAC)
    \\ Q.PAT_X_ASSUM `BC_ap zzz (Error,xxx) szzz` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,func_distinct,term_11,func_11,LENGTH_REVERSE,LENGTH]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL]
    \\ `DROP (LENGTH args) (MAP (\x. ssTEMP) args ++ a') = a'` by
         (METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND,LENGTH_MAP,LENGTH_REVERSE])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `BC_FAIL (BC_PRINT bc7 (sexp2string (list2sexp (Sym "ERROR"::args)) ++ "\n"))`
    \\ REVERSE STRIP_TAC THEN1
     (REVERSE STRIP_TAC THEN1 EVAL_TAC
      \\ FULL_SIMP_TAC std_ss [BC_REFINES_def,BC_CODE_OK_PRINT,BC_CODE_OK_FAIL]
      \\ REVERSE STRIP_TAC
      THEN1 (FULL_SIMP_TAC (srw_ss()) [BC_PRINT_def,BC_FAIL_def])
      \\ Q.PAT_X_ASSUM `BC_FNS_ASSUM fns bc7` MP_TAC
      \\ SIMP_TAC std_ss [BC_FNS_ASSUM_def,BC_PRINT_CONTAINS_BYTECODE,BC_FAIL_CONTAINS_BYTECODE]
      \\ FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,BC_CODE_OK_PRINT,BC_CODE_OK_FAIL]
      \\ FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,BC_PRINT_def,BC_FAIL_def]
      \\ METIS_TAC [])
    \\ Q.ABBREV_TAC `ys = [iCONST_SYM "NIL"] ++ n_times (LENGTH args) (iDATA opCONS)`
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(list2sexp args :: stack,p + iLENGTH bc.instr_length ys,r::rs,bc7)`
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND] \\ Q.UNABBREV_TAC `ys`
      \\ `bc7.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
      \\ IMP_RES_TAC n_times_CONS  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
    \\ `bc7.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,CONTAINS_BYTECODE_def]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(Sym "ERROR" :: list2sexp args :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "ERROR"]),r::rs,bc7)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(list2sexp args :: Sym "ERROR" :: list2sexp args :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "ERROR"; iLOAD 1]),r::rs,bc7)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def]
       \\ EVAL_TAC \\ DECIDE_TAC)
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(list2sexp (Sym "ERROR"::args) :: list2sexp args :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "ERROR"; iLOAD 1; iDATA opCONS]),r::rs,bc7)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def]
       \\ Q.EXISTS_TAC `[Sym "ERROR";list2sexp args]` \\ EVAL_TAC)
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(list2sexp (Sym "ERROR"::args) :: list2sexp args :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "ERROR"; iLOAD 1; iDATA opCONS; iPRINT]),r::rs,BC_PRINT bc7 (sexp2string (list2sexp (Sym "ERROR"::args)) ++ "\n"))`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(anything :: stack,p + iLENGTH bc.instr_length (ys ++ [iCONST_SYM "ERROR"; iLOAD 1; iDATA opCONS; iPRINT; iFAIL]),r::rs,BC_FAIL (BC_PRINT bc7 (sexp2string (list2sexp (Sym "ERROR"::args)) ++ "\n")))`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def,BC_PRINT_code])
    THEN
     (REVERSE (Cases_on `ret`)
      \\ FULL_SIMP_TAC std_ss [RTC_REFL,iLENGTH_def,BC_return_code_def,APPEND_NIL]
      \\ MATCH_MP_TAC BC_return_code_thm
      \\ FULL_SIMP_TAC std_ss [BC_return_code_def,BC_PRINT_CONTAINS_BYTECODE,
                               BC_FAIL_CONTAINS_BYTECODE]))

  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `BC_ap zzz (Define,xxx) szzz` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,func_distinct,term_11,func_11,LENGTH_REVERSE,LENGTH]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL,MAP]
    \\ `DROP 3 ([ssTEMP; ssTEMP; ssTEMP] ++ a') = a'` by FULL_SIMP_TAC std_ss [DROP_def,APPEND,DROP_0]
    \\ FULL_SIMP_TAC std_ss [REVERSE_DEF,APPEND]
    \\ REVERSE (Cases_on `getSym fc NOTIN FDOM fns`)
    \\ FULL_SIMP_TAC std_ss [add_def_NOP,SUBMAP_REFL] THEN1
     (Q.EXISTS_TAC `BC_FAIL bc7`
      \\ REVERSE STRIP_TAC THEN1
       (REVERSE STRIP_TAC THEN1 EVAL_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [BC_REFINES_def]
        \\ Q.PAT_X_ASSUM `BC_FNS_ASSUM fns bc7` MP_TAC
        \\ FULL_SIMP_TAC std_ss [BC_FNS_ASSUM_def,BC_FAIL_CONTAINS_BYTECODE]
        \\ FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,BC_CODE_OK_FAIL]
        \\ FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,BC_FAIL_def] \\ METIS_TAC [])
      \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
      \\ Q.EXISTS_TAC `(Sym "NIL"::stack,p + iLENGTH bc.instr_length [iCOMPILE],r::rs,BC_FAIL bc7)`
      \\ STRIP_TAC THEN1
       (REPEAT (MATCH_MP_TAC RTC_SINGLE)
        \\ MATCH_MP_TAC iSTEP_cases_imp
        \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
          LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
          iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def,BC_PRINT_code]
        \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_SUBSTATE_def]
        \\ FULL_SIMP_TAC std_ss [BC_REFINES_def]
        \\ FULL_SIMP_TAC std_ss [GSPECIFICATION,EXTENSION])
      \\ ASSUME_TAC (EVAL ``(BC_FAIL bc7).ok``) \\ FULL_SIMP_TAC std_ss []
      \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
      \\ Cases_on `ret`
      \\ ONCE_REWRITE_TAC [iSTEP_cases]
      \\ FULL_SIMP_TAC std_ss [iSTEP_ret_state_def])
    \\ FULL_SIMP_TAC std_ss [add_def_FUPDATE]
    \\ `?bc5. BC_COMPILE (getSym fc,MAP getSym (sexp2list formals),sexp2term body,bc7) = bc5` by METIS_TAC []
    \\ Q.EXISTS_TAC `bc5`
    \\ `fns SUBMAP fns |+ (getSym fc,MAP getSym (sexp2list formals),sexp2term body)` by
         (FULL_SIMP_TAC std_ss [SUBMAP_DEF,FDOM_FUPDATE,FAPPLY_FUPDATE_THM,IN_INSERT]
          \\ METIS_TAC []) \\ ASM_SIMP_TAC std_ss []
    \\ REVERSE (REPEAT STRIP_TAC) THEN1
     (POP_ASSUM (K ALL_TAC)
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [GSYM th])
      \\ FULL_SIMP_TAC std_ss [BC_COMPILE_compiled_instr_length,BC_REFINES_def])
    THEN1
      (Q.PAT_X_ASSUM `xxx = bc5` (fn th => SIMP_TAC std_ss [GSYM th])
       \\ METIS_TAC [BC_REFINES_COMPILE])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(Sym "NIL"::stack,p + iLENGTH bc.instr_length [iCOMPILE],r::rs,bc5)`
    \\ STRIP_TAC THEN1
     (REPEAT (MATCH_MP_TAC RTC_SINGLE)
      \\ MATCH_MP_TAC iSTEP_cases_imp
      \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
        LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
        iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def,BC_PRINT_code]
      \\ `bc7.instr_length = bc.instr_length` by METIS_TAC [BC_SUBSTATE_def]
      \\ FULL_SIMP_TAC std_ss [BC_REFINES_def]
      \\ Q.PAT_X_ASSUM `xxx = FDOM fns` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
      \\ FULL_SIMP_TAC std_ss [GSPECIFICATION])
    \\ REVERSE (Cases_on `ret`)
    \\ FULL_SIMP_TAC std_ss [RTC_REFL,iLENGTH_def,BC_return_code_def,APPEND_NIL]
    \\ MATCH_MP_TAC BC_return_code_thm \\ ASM_SIMP_TAC std_ss []
    \\ `BC_SUBSTATE bc7 bc5` by
      (FULL_SIMP_TAC std_ss [BC_REFINES_def]
       \\ Q.PAT_X_ASSUM `xxx = FDOM fns` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
       \\ FULL_SIMP_TAC std_ss [GSPECIFICATION]
       \\ IMP_RES_TAC BC_COMPILE_SUBSTATE)
    \\ `BC_SUBSTATE bc bc5` by BC_SUBSTATE_TAC
    \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE
    \\ `bc5.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
    \\ `bc7.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss [BC_return_code_def])

  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `BC_ap zzz (Funcall,xxx) szzz` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,func_distinct,term_11,func_11,LENGTH_REVERSE,LENGTH]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND,
         LENGTH,LENGTH_APPEND,ADD_ASSOC,SUBMAP_REFL,MAP]
    \\ Q.PAT_X_ASSUM `BC_REFINES (fns1,io1) bc8` (fn th =>
           ASSUME_TAC th THEN MP_TAC th)
    \\ SIMP_TAC std_ss [Once BC_FNS_ASSUM_def,Once BC_REFINES_def]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!fc params.bbb` (MP_TAC o Q.SPECL [`fname`,`params`,`exp`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ `BC_SUBSTATE bc bc7`by BC_SUBSTATE_TAC
    \\ `bc7.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!a code.bbb` (MP_TAC o
         Q.SPECL [`MAP ssVAR (REVERSE params)`,`pcode`,`a5`,
                  `REVERSE args ++ [Sym fname] ++ stack`,`p'`,`(p +
           iLENGTH bc.instr_length [iCONST_NUM (LENGTH (args:SExp list)); iLOAD (SUC (LENGTH args)); iCALL_SYM])`,`r::rs`,`T`,`p' + iLENGTH bc.instr_length pcode`,`bc4`,`bc5`,`bc7`])
    \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ MATCH_MP_TAC STACK_INV_VarBind \\ ASM_SIMP_TAC std_ss [])
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `bc8` \\ ASM_SIMP_TAC std_ss []
    \\ REVERSE STRIP_TAC THEN1
     (`LENGTH (ssTEMP::MAP (\x. ssTEMP) (args:SExp list)) = SUC (LENGTH args)` by
           FULL_SIMP_TAC std_ss [LENGTH,LENGTH_MAP]
      \\ METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND])
    \\ FULL_SIMP_TAC std_ss [iSTEP_ret_state_def]
    \\ `BC_SUBSTATE bc7 bc8` by METIS_TAC [iSTEP_BC_SUBSTATE]
    \\ `BC_SUBSTATE bc0 bc8` by BC_SUBSTATE_TAC
    \\ `bc8.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(Val (LENGTH args) :: (REVERSE (Sym fname::args) ++ stack),p + iLENGTH bc.instr_length [iCONST_NUM ((LENGTH args))],r::rs,bc7)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def,BC_PRINT_code])
    \\ FULL_SIMP_TAC std_ss [REVERSE_DEF]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(Sym fname::(Val (LENGTH args)::(REVERSE args ++ [Sym fname] ++ stack)),
                      p + iLENGTH bc.instr_length [iCONST_NUM (LENGTH args); iLOAD (SUC(LENGTH args))],r::rs,bc7)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def,BC_PRINT_code]
       \\ FULL_SIMP_TAC std_ss [EL,TL,GSYM APPEND_ASSOC,APPEND,LENGTH_APPEND,
            LENGTH_REVERSE,LENGTH] \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
       \\ SIMP_TAC std_ss [RW [LESS_EQ_REFL] (Q.SPECL [`xs`,`LENGTH xs`]
             rich_listTheory.EL_APPEND2),EL,HD] \\ DECIDE_TAC)
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(REVERSE args ++ [Sym fname] ++ stack,p',
          p + iLENGTH bc.instr_length
          [iCONST_NUM (LENGTH args); iLOAD (SUC (LENGTH args)); iCALL_SYM]::r::rs,bc7)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def,BC_PRINT_code]
       \\ Q.EXISTS_TAC `fname` \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(iSTEP_ret_state (MAP ssVAR (REVERSE params))
            (x,REVERSE args ++ [Sym fname] ++ stack,
             p +
             iLENGTH bc.instr_length
               [iCONST_NUM (LENGTH args); iLOAD (SUC (LENGTH args));
                iCALL_SYM],r::rs,bc8))` \\ ASM_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [iSTEP_ret_state_def]
    \\ `DROP (LENGTH (MAP ssVAR (REVERSE params)))
         (REVERSE args ++ [Sym fname] ++ stack) = [Sym fname] ++ stack` by
     (`(LENGTH (MAP ssVAR (REVERSE params))) = LENGTH (REVERSE args)` by
         FULL_SIMP_TAC std_ss [LENGTH_MAP,LENGTH_REVERSE]
      \\ METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND,APPEND_ASSOC])
    \\ ASM_SIMP_TAC std_ss [] \\ ASM_SIMP_TAC std_ss [APPEND]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(x::stack,
         p + iLENGTH bc.instr_length
          [iCONST_NUM (LENGTH args); iLOAD (SUC (LENGTH args)); iCALL_SYM; iPOPS 1],
         r::rs,bc8)`
    \\ STRIP_TAC THEN1
      (REPEAT (MATCH_MP_TAC RTC_SINGLE)
       \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE
       \\ Q.PAT_X_ASSUM `bc8.instr_length = bc.instr_length` ASSUME_TAC
       \\ MATCH_MP_TAC iSTEP_cases_imp
       \\ FULL_SIMP_TAC std_ss [bc_inst_type_distinct,bc_inst_type_11,BC_STEP_def,
         LENGTH,CONS_11,STACK_INV_lemma,getVal_def,CONTAINS_BYTECODE_def,iLENGTH_def,
         iLENGTH_APPEND,iLENGTH_def,AC ADD_ASSOC ADD_COMM,EVAL_DATA_OP_def,BC_PRINT_code]
       \\ Q.EXISTS_TAC `[Sym fname]` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH])
    \\ Cases_on `ret` \\ ASM_SIMP_TAC std_ss [BC_return_code_def,RTC_REFL]
    \\ MATCH_MP_TAC (SIMP_RULE std_ss [iSTEP_ret_state_def] BC_return_code_thm)
    \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE
    \\ Q.PAT_X_ASSUM `bc8.instr_length = bc.instr_length` ASSUME_TAC
    \\ `DROP (SUC (LENGTH args))
                   (ssTEMP::MAP (\x. ssTEMP) args ++ a') = a'` by
     (`LENGTH (ssTEMP::MAP (\x. ssTEMP) (args:SExp list)) = SUC (LENGTH args)` by
           FULL_SIMP_TAC std_ss [LENGTH,LENGTH_MAP]
      \\ METIS_TAC [rich_listTheory.BUTFIRSTN_LENGTH_APPEND])
    \\ FULL_SIMP_TAC std_ss [])
  \\ STRIP_TAC THEN1
   (REVERSE (REPEAT STRIP_TAC)
    \\ Q.PAT_X_ASSUM `BC_ap zzz xxx szzz` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,func_distinct,term_11,func_11,LENGTH_REVERSE,LENGTH])
  \\ STRIP_TAC THEN1
   (REVERSE (REPEAT STRIP_TAC)
    \\ Q.PAT_X_ASSUM `BC_ap zzz xxx szzz` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases] \\ SIMP_TAC std_ss [BC_return_def]
    \\ ASM_SIMP_TAC std_ss [term_distinct,func_distinct,term_11,func_11,LENGTH_REVERSE,LENGTH]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [CONS_11,SUBMAP_REFL,
         RW [LENGTH_MAP] (Q.SPEC `MAP f xs` rich_listTheory.BUTFIRSTN_LENGTH_APPEND)]
    \\ Q.EXISTS_TAC `bc7` \\ FULL_SIMP_TAC std_ss [iSTEP_ret_state_def]
    \\ Cases_on `ret` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
    \\ ONCE_REWRITE_TAC [iSTEP_cases] \\ FULL_SIMP_TAC std_ss [])

  \\ STRIP_TAC THEN1
   (REVERSE (REPEAT STRIP_TAC)
    \\ IMP_RES_TAC BC_ev_NOT_RET_LEMMA
    \\ FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `bc7`
    \\ ASM_SIMP_TAC std_ss [CONS_11,SUBMAP_REFL]
    \\ FULL_SIMP_TAC std_ss [iSTEP_ret_state_def]
    \\ Cases_on `ret` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT (MATCH_MP_TAC RTC_SINGLE)
    \\ ONCE_REWRITE_TAC [iSTEP_cases] \\ FULL_SIMP_TAC std_ss [])

  \\ STRIP_TAC THEN1
   (ONCE_REWRITE_TAC [BC_ev_cases]
    \\ SIMP_TAC std_ss [NOT_CONS_NIL,CONS_11,MAP,APPEND,LENGTH,
         CONTAINS_BYTECODE_def,RTC_REFL,REVERSE_DEF,iLENGTH_def,SUBMAP_REFL]
    \\ METIS_TAC [RTC_REFL])
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `BC_evl (e::el,xxx) yyy` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases]
    \\ SIMP_TAC std_ss [NOT_CONS_NIL,CONS_11,MAP,APPEND,LENGTH,
         CONTAINS_BYTECODE_def,RTC_REFL] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_APPEND]
    \\ Q.PAT_X_ASSUM `!env. bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!env. bbb` (MP_TAC o
         Q.SPECL [`a'`,`code'`,`a2'`,`stack`,`p`,`r`,`rs`,`F`,`q2`,`bc`,`bc2`,`bc7`])
    \\ `BC_SUBSTATE bc2 bc7` by BC_SUBSTATE_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!env. bbb` (MP_TAC o
         Q.SPECL [`a2'`,`code2`,`a2`,`s::stack`,`p+iLENGTH bc.instr_length (code')`,`r`,`rs`,`p2`,`bc2`,`bc0`,`bc8`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (IMP_RES_TAC BC_ev_LENGTH \\ FULL_SIMP_TAC std_ss [STACK_INV_lemma]
      \\ `BC_SUBSTATE bc7 bc8` by BC_SUBSTATE_TAC
      \\ IMP_RES_TAC BC_SUBSTATE_BYTECODE
      \\ `bc7.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC BC_SUBSTATE_TRANS)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `bc8'` \\ ASM_SIMP_TAC std_ss [REVERSE_DEF]
    \\ SIMP_TAC std_ss [MAP_APPEND,MAP,GSYM APPEND_ASSOC,APPEND]
    \\ IMP_RES_TAC SUBMAP_TRANS \\ ASM_SIMP_TAC std_ss []
    \\ `BC_SUBSTATE bc bc2` by IMP_RES_TAC BC_ev_LENGTH
    \\ `bc2.instr_length = bc.instr_length` by FULL_SIMP_TAC std_ss [BC_SUBSTATE_def]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s::stack,p + iLENGTH bc.instr_length code',r::rs,bc8)`
    \\ FULL_SIMP_TAC std_ss [REVERSE_DEF,GSYM APPEND_ASSOC,APPEND,
         iLENGTH_APPEND,AC ADD_COMM ADD_ASSOC,MAP_APPEND,MAP])
  (* deal with all macros with a single tactic *)
  \\ REPEAT STRIP_TAC THEN
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `BC_ev ret xxx yyy` MP_TAC
    \\ ONCE_REWRITE_TAC [BC_ev_cases]
    \\ ASM_SIMP_TAC std_ss [term_distinct,term_11,NOT_CONS_NIL,CONS_11]
    \\ METIS_TAC []));

val BC_ev_thm = BC_ev_lemma
  |> CONJUNCTS |> el 3 |> SPEC_ALL
  |> (fn th => MATCH_MP th (R_ev_IMP_RR_ev |> SPEC_ALL |> UNDISCH_ALL)) |> DISCH_ALL
  |> SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO] |> Q.INST [`ret`|->`T`]
  |> GEN_ALL |> SIMP_RULE std_ss [iSTEP_ret_state_def]

val _ = save_thm("BC_ev_thm",BC_ev_thm);


(* translation: term2sexp *)

val prim2sym_def = Define `
  (prim2sym opCONS = "CONS") /\
  (prim2sym opEQUAL = "EQUAL") /\
  (prim2sym opLESS = "<") /\
  (prim2sym opSYMBOL_LESS = "SYMBOL-<") /\
  (prim2sym opADD = "+") /\
  (prim2sym opSUB = "-") /\
  (prim2sym opCONSP = "CONSP") /\
  (prim2sym opNATP = "NATP") /\
  (prim2sym opSYMBOLP = "SYMBOLP") /\
  (prim2sym opCAR = "CAR") /\
  (prim2sym opCDR = "CDR")`;

val macro_names_def = Define `
  macro_names =
    ["LET";"LET*";"COND";"AND";"FIRST";"SECOND";
     "THIRD";"FOURTH";"FIFTH";"LIST";"DEFUN"]`;

val reserved_names_def = Define `
  reserved_names =
    ["QUOTE";"IF";"OR";"DEFINE";"PRINT";"ERROR";"FUNCALL";
     "CAR";"CDR";"SYMBOLP";"NATP";"CONSP";"+";"-";
     "SYMBOL-<";"<";"EQUAL";"CONS"] ++ macro_names`;

val func2sexp_def = Define `
  (func2sexp (PrimitiveFun p) = [Sym (prim2sym p)]) /\
  (func2sexp (Define) = [Sym "DEFINE"]) /\
  (func2sexp (Print) = [Sym "PRINT"]) /\
  (func2sexp (Error) = [Sym "ERROR"]) /\
  (func2sexp (Funcall) = [Sym "FUNCALL"]) /\
  (func2sexp (Fun f) =
     if MEM f reserved_names then [Val 0; Sym f] else [Sym f])`;

val term2sexp_def = tDefine "term2sexp" `
  (term2sexp (Const s) = list2sexp [Sym "QUOTE"; s]) /\
  (term2sexp (Var v) = Sym v) /\
  (term2sexp (App fc vs) = list2sexp (func2sexp fc ++ MAP term2sexp vs)) /\
  (term2sexp (If x y z) = list2sexp [Sym "IF"; term2sexp x; term2sexp y; term2sexp z]) /\
  (term2sexp (LamApp xs z ys) = list2sexp (list2sexp [Sym "LAMBDA"; list2sexp (MAP Sym xs); term2sexp z]::MAP term2sexp ys)) /\
  (term2sexp (Let zs x) = list2sexp [Sym "LET"; list2sexp (MAP (\x. list2sexp [Sym (FST x); term2sexp (SND x)]) zs); term2sexp x]) /\
  (term2sexp (LetStar zs x) = list2sexp [Sym "LET*"; list2sexp (MAP (\x. list2sexp [Sym (FST x); term2sexp (SND x)]) zs); term2sexp x]) /\
  (term2sexp (Cond qs) = list2sexp (Sym "COND":: (MAP (\x. list2sexp [term2sexp (FST x); term2sexp (SND x)]) qs))) /\
  (term2sexp (Or ts) = list2sexp (Sym "OR"::MAP term2sexp ts)) /\
  (term2sexp (And ts) = list2sexp (Sym "AND"::MAP term2sexp ts)) /\
  (term2sexp (List ts) = list2sexp (Sym "LIST"::MAP term2sexp ts)) /\
  (term2sexp (First x) = list2sexp [Sym "FIRST"; term2sexp x]) /\
  (term2sexp (Second x) = list2sexp [Sym "SECOND"; term2sexp x]) /\
  (term2sexp (Third x) = list2sexp [Sym "THIRD"; term2sexp x]) /\
  (term2sexp (Fourth x) = list2sexp [Sym "FOURTH"; term2sexp x]) /\
  (term2sexp (Fifth x) = list2sexp [Sym "FIFTH"; term2sexp x]) /\
  (term2sexp (Defun fname ps s) = list2sexp [Sym "DEFUN"; Sym fname; list2sexp (MAP Sym ps); s])`
 (WF_REL_TAC `measure (term_size)`);

val fun_name_ok_def = Define `
  (fun_name_ok (Fun f) = ~MEM f reserved_names) /\
  (fun_name_ok _ = T)`;

val no_bad_names_def = tDefine "no_bad_names" `
  (no_bad_names (Const s) = T) /\
  (no_bad_names (Var v) = ~(v = "T") /\ ~(v = "NIL")) /\
  (no_bad_names (App fc vs) = fun_name_ok fc /\ EVERY no_bad_names vs) /\
  (no_bad_names (If x y z) = no_bad_names x /\ no_bad_names y /\ no_bad_names z) /\
  (no_bad_names (LamApp xs z ys) = no_bad_names z /\ EVERY no_bad_names ys) /\
  (no_bad_names (Let zs x) = EVERY (\x. no_bad_names (SND x)) zs /\ no_bad_names x) /\
  (no_bad_names (LetStar zs x) = EVERY (\x. no_bad_names (SND x)) zs /\ no_bad_names x) /\
  (no_bad_names (Cond qs) = EVERY (\x. no_bad_names (FST x) /\ no_bad_names (SND x)) qs) /\
  (no_bad_names (Or ts) = EVERY no_bad_names ts) /\
  (no_bad_names (And ts) = EVERY no_bad_names ts) /\
  (no_bad_names (List ts) = EVERY no_bad_names ts) /\
  (no_bad_names (First x) = no_bad_names x) /\
  (no_bad_names (Second x) = no_bad_names x) /\
  (no_bad_names (Third x) = no_bad_names x) /\
  (no_bad_names (Fourth x) = no_bad_names x) /\
  (no_bad_names (Fifth x) = no_bad_names x) /\
  (no_bad_names (Defun fname ps s) = T)`
 (WF_REL_TAC `measure (term_size)`);

val sexp2list_list2sexp = prove(
  ``!x. sexp2list (list2sexp x) = x``,
  Induct \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);

val MAP_EQ_IMP = prove(
  ``!xs f. (!x. MEM x xs ==> (f x = x)) ==> (MAP f xs = xs)``,
  Induct \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val sexp2term_term2sexp = store_thm("sexp2term_term2sexp",
  ``!t. no_bad_names t ==> (sexp2term (term2sexp t) = t)``,
  HO_MATCH_MP_TAC (fetch "-" "term2sexp_ind") \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [no_bad_names_def]
  THEN1 (EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  THEN1 (EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  THEN1
   (SIMP_TAC (srw_ss()) [term2sexp_def,LET_DEF]
    \\ Cases_on `fc` THEN TRY
     (ASM_SIMP_TAC (srw_ss()) [func2sexp_def,list2sexp_def,CAR_def,CDR_def,isVal_def,isSym_def]
      \\ SIMP_TAC (srw_ss()) [Once sexp2term_def,LET_DEF] \\ TRY (Cases_on `l`)
      \\ ASM_SIMP_TAC (srw_ss()) [list2sexp_def,CAR_def,CDR_def,isVal_def,isSym_def,
           getSym_def,prim2sym_def,sym2prim_def,sexp2list_list2sexp,
           MAP_MAP_o,combinTheory.o_DEF,fun_name_ok_def]
      \\ MATCH_MP_TAC MAP_EQ_IMP \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ NO_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [func2sexp_def,fun_name_ok_def]
    \\ FULL_SIMP_TAC (srw_ss()) [reserved_names_def,MEM,APPEND,macro_names_def]
    \\ SIMP_TAC (srw_ss()) [Once sexp2term_def,LET_DEF]
    \\ ASM_SIMP_TAC (srw_ss()) [list2sexp_def,CAR_def,CDR_def,isVal_def,isSym_def,
           getSym_def,prim2sym_def,sym2prim_def,sexp2list_list2sexp,
           MAP_MAP_o,combinTheory.o_DEF]
    \\ MATCH_MP_TAC MAP_EQ_IMP \\ FULL_SIMP_TAC std_ss [EVERY_MEM])
  THEN1
   (SIMP_TAC (srw_ss()) [term2sexp_def,Once sexp2term_def,LET_DEF]
    \\ ASM_SIMP_TAC (srw_ss()) [list2sexp_def,CAR_def,CDR_def,isVal_def,isSym_def])
  THEN
   (SIMP_TAC (srw_ss()) [term2sexp_def,Once sexp2term_def,LET_DEF]
    \\ ASM_SIMP_TAC (srw_ss()) [list2sexp_def,CAR_def,CDR_def,isVal_def,isSym_def,
        getSym_def,sym2prim_def,sexp2list_list2sexp,MAP_MAP_o,combinTheory.o_DEF]
    \\ MATCH_MP_TAC MAP_EQ_IMP \\ FULL_SIMP_TAC std_ss [EVERY_MEM]));

val verified_string_def = Define `
  verified_string xs =
    if ~ALL_DISTINCT (MAP FST xs) then NONE else
    if ~EVERY (\(name,params,body). no_bad_names body) xs then NONE else
      SOME (FLAT (MAP ( \ (name,params,body). sexp2string
        (list2sexp [Sym "DEFUN"; Sym name;
           list2sexp (MAP Sym params); term2sexp body]) ++ "\n") xs))`


(* translation sexp2sexp *)

val sfix_def = Define `sfix x = Sym (getSym x)`;

val IMP_isDot = prove(
  ``!x. ~(isVal x) /\ ~(isSym x) ==> isDot x``,
  Cases THEN EVAL_TAC);

val LSIZE_CAR_LESS = prove(
  ``!x. LSIZE x < SUC n ==> LSIZE (CAR x) < SUC n``,
  Cases \\ FULL_SIMP_TAC std_ss [LSIZE_def,CAR_def,CDR_def] \\ DECIDE_TAC);

val LSIZE_CDR_LESS = prove(
  ``!x. LSIZE x < SUC n ==> LSIZE (CDR x) < SUC n``,
  Cases \\ FULL_SIMP_TAC std_ss [LSIZE_def,CAR_def,CDR_def] \\ DECIDE_TAC);

val MEM_sexp2list = prove(
  ``!a x. MEM x (sexp2list a) ==> LSIZE x < LSIZE a``,
  Induct \\ SIMP_TAC std_ss [sexp2list_def,MEM] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LSIZE_def] \\ RES_TAC \\ DECIDE_TAC);

val sexp2sexp_def = tDefine "sexp2sexp" `
  sexp2sexp x =
    if x = Sym "T" then list2sexp [Sym "QUOTE"; x] else
    if x = Sym "NIL" then list2sexp [Sym "QUOTE"; x] else
    if isVal x then list2sexp [Sym "QUOTE"; x] else
    if isSym x then x else
      let x1 = CAR x in
      let x2 = CAR (CDR x) in
      let x3 = CAR (CDR (CDR x)) in
      let x4 = CAR (CDR (CDR (CDR x))) in
      let xs = list2sexp (MAP sexp2sexp (sexp2list (CDR x))) in
        if x1 = Sym "QUOTE" then list2sexp [Sym "QUOTE"; x2] else
        if x1 = Sym "IF" then
          list2sexp [Sym "IF"; sexp2sexp x2; sexp2sexp x3; sexp2sexp x4] else
        if x1 = Sym "FIRST" then list2sexp [x1; sexp2sexp x2] else
        if x1 = Sym "SECOND" then list2sexp [x1; sexp2sexp x2] else
        if x1 = Sym "THIRD" then list2sexp [x1; sexp2sexp x2] else
        if x1 = Sym "FOURTH" then list2sexp [x1; sexp2sexp x2] else
        if x1 = Sym "FIFTH" then list2sexp [x1; sexp2sexp x2] else
        if x1 = Sym "DEFUN" then
          list2sexp [Sym "DEFUN"; sfix x2;
                     list2sexp (MAP sfix (sexp2list x3)); x4] else
        if CAR x1 = Sym "LAMBDA" then
          let y2 = CAR (CDR x1) in
          let y3 = CAR (CDR (CDR x1)) in
            Dot (list2sexp [Sym "LAMBDA";
                            list2sexp (MAP sfix (sexp2list y2));
                            sexp2sexp y3]) xs else
        if x1 = Sym "COND" then
          Dot (Sym "COND") (list2sexp (MAP
            (\x. list2sexp [sexp2sexp (CAR x); sexp2sexp (CAR (CDR x))])
              (sexp2list (CDR x)))) else
        if x1 = Sym "LET" then
          list2sexp [x1; list2sexp (MAP
            (\x. list2sexp [sfix (CAR x); sexp2sexp (CAR (CDR x))])
              (sexp2list x2)); sexp2sexp x3] else
        if x1 = Sym "LET*" then
          list2sexp [x1; list2sexp (MAP
            (\x. list2sexp [sfix (CAR x); sexp2sexp (CAR (CDR x))])
              (sexp2list x2)); sexp2sexp x3]
        else
          Dot (sfix x1) xs`
 (WF_REL_TAC `measure LSIZE` \\ REPEAT STRIP_TAC \\ IMP_RES_TAC IMP_isDot
  \\ FULL_SIMP_TAC std_ss [isDot_thm,CAR_def,CDR_def,LSIZE_def]
  \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def,LSIZE_def]
  \\ IMP_RES_TAC MEM_sexp2list
  \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS ORELSE MATCH_MP_TAC LSIZE_CDR_LESS)
  \\ REPEAT DECIDE_TAC
  \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def,LSIZE_def]
  \\ DECIDE_TAC);

val PULL_FORALL_IMP = METIS_PROVE [] ``(p ==> !x. q x) = !x. p ==> q x``;

val list2sexp_11 = prove(
  ``!xs ys. (list2sexp xs = list2sexp ys) = (xs = ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [list2sexp_def]);

val MAP_sfix = prove(
  ``!xs. MAP sfix xs = MAP Sym (MAP getSym xs)``,
  Induct \\ FULL_SIMP_TAC std_ss [MAP,sfix_def]);

val sexp2sexp_thm = store_thm("sexp2sexp_thm",
  ``!x. sexp2sexp x = term2sexp (sexp2term x)``,
  REPEAT STRIP_TAC \\ completeInduct_on `LSIZE x` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ ONCE_REWRITE_TAC [sexp2sexp_def]
  \\ Cases_on `x = Sym "T"` \\ ASM_SIMP_TAC std_ss [] THEN1 EVAL_TAC
  \\ Cases_on `x = Sym "NIL"` \\ ASM_SIMP_TAC std_ss [] THEN1 EVAL_TAC
  \\ Cases_on `isVal x` \\ ASM_SIMP_TAC std_ss []
  THEN1 (ASM_SIMP_TAC std_ss [Once sexp2term_def,term2sexp_def])
  \\ Cases_on `isSym x` \\ ASM_SIMP_TAC std_ss []
  THEN1 (ASM_SIMP_TAC std_ss [Once sexp2term_def,term2sexp_def]
         \\ FULL_SIMP_TAC std_ss [isSym_thm,getSym_def])
  \\ ONCE_REWRITE_TAC [sexp2term_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ IMP_RES_TAC IMP_isDot
  \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def,isDot_thm]
  \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def,isDot_thm]
  \\ Cases_on `a = Sym "QUOTE"` \\ ASM_SIMP_TAC std_ss [] THEN1 EVAL_TAC
  \\ Cases_on `a = Sym "IF"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (SIMP_TAC (srw_ss()) [term2sexp_def,list2sexp_11] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [LSIZE_def]
    \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS ORELSE MATCH_MP_TAC LSIZE_CDR_LESS)
    \\ DECIDE_TAC)
  \\ `MAP (\a. sexp2sexp a) (sexp2list b) =
      MAP (\a. term2sexp a) (MAP (\a. sexp2term a) (sexp2list b))` by
   (FULL_SIMP_TAC std_ss [LSIZE_def] \\ Q.PAT_X_ASSUM `!x.bb` MP_TAC
    \\ Q.SPEC_TAC (`b`,`b`) \\ REVERSE Induct
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [sexp2list_def,MAP,CONS_11]
    \\ REPEAT STRIP_TAC THEN1 (POP_ASSUM MATCH_MP_TAC \\ EVAL_TAC \\ DECIDE_TAC)
    \\ Q.PAT_X_ASSUM `(!x.bbb) ==> ccc` MATCH_MP_TAC \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `(!x.bbb)` MATCH_MP_TAC \\ REPEAT STRIP_TAC
    \\ EVAL_TAC \\ DECIDE_TAC)
  \\ REVERSE (Cases_on `sym2prim (getSym a) = NONE`)
  \\ ASM_SIMP_TAC std_ss [] THEN1
   (CCONTR_TAC \\ Q.PAT_X_ASSUM `sym2prim (getSym a) <> NONE` MP_TAC
    \\ FULL_SIMP_TAC std_ss [sym2prim_def] \\ SRW_TAC [] [] \\ Cases_on `a`
    \\ FULL_SIMP_TAC (srw_ss()) [getSym_def,CAR_def,term2sexp_def,func2sexp_def,
         list2sexp_def,prim2sym_def,sfix_def])
  \\ Cases_on `MEM a [Sym "FIRST";Sym "SECOND";Sym "THIRD";Sym "FOURTH";Sym "FIFTH"]`
  \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [MEM]
    \\ SIMP_TAC (srw_ss()) [term2sexp_def,list2sexp_11,CONS_11]
    \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ SIMP_TAC std_ss [LSIZE_def]
    \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS) \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [MEM]
  \\ Cases_on `a = Sym "OR"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def]
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,list2sexp_def,getSym_def,sfix_def]
  \\ Cases_on `a = Sym "AND"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def]
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,list2sexp_def,getSym_def,sfix_def]
  \\ Cases_on `a = Sym "LIST"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def]
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,list2sexp_def,getSym_def,sfix_def]
  \\ Cases_on `a = Sym "DEFINE"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,getSym_def,sfix_def]
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,list2sexp_def,func2sexp_def,APPEND,getSym_def,sfix_def]
  \\ Cases_on `a = Sym "PRINT"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def]
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,list2sexp_def,func2sexp_def,APPEND,getSym_def,sfix_def]
  \\ Cases_on `a = Sym "ERROR"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def]
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,list2sexp_def,func2sexp_def,APPEND,getSym_def,sfix_def]
  \\ Cases_on `a = Sym "FUNCALL"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def]
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,list2sexp_def,func2sexp_def,APPEND,getSym_def,sfix_def]
  \\ Cases_on `a = Sym "DEFUN"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def]
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,list2sexp_def,func2sexp_def,APPEND,getSym_def,sfix_def]
  \\ FULL_SIMP_TAC std_ss [sfix_def,MAP_sfix]
  \\ Cases_on `a = Sym "COND"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def] THEN1
   (FULL_SIMP_TAC (srw_ss()) [term2sexp_def,list2sexp_def,list2sexp_11,LSIZE_def]
    \\ Q.PAT_X_ASSUM `!x.bbb` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ REVERSE (Induct_on `b`)
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss []) THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
    \\ SIMP_TAC std_ss [sexp2list_def,MAP,CONS_11] \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
      \\ POP_ASSUM MATCH_MP_TAC
      \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS ORELSE MATCH_MP_TAC LSIZE_CDR_LESS)
      \\ FULL_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
    \\ Q.PAT_X_ASSUM `(!x.bbb) ==> ccc` MATCH_MP_TAC \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ SIMP_TAC std_ss [LSIZE_def]
    \\ DECIDE_TAC)
  \\ Cases_on `a = Sym "LET"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def] THEN1
   (FULL_SIMP_TAC (srw_ss()) [term2sexp_def,list2sexp_def,list2sexp_11,LSIZE_def]
    \\ REVERSE (REPEAT STRIP_TAC) THEN1
     (Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
      \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS ORELSE MATCH_MP_TAC LSIZE_CDR_LESS)
      \\ FULL_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
    \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [sexp2list_def,CAR_def,MAP,LSIZE_def]
    \\ Q.PAT_X_ASSUM `!x.bbb` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ REVERSE (Induct_on `S'`)
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss []) THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
    \\ SIMP_TAC std_ss [sexp2list_def,MAP,CONS_11] \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
      \\ POP_ASSUM MATCH_MP_TAC
      \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS ORELSE MATCH_MP_TAC LSIZE_CDR_LESS)
      \\ FULL_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
    \\ Q.PAT_X_ASSUM `(!x.bbb) ==> ccc` MATCH_MP_TAC \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
  \\ Cases_on `a = Sym "LET*"` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def] THEN1
   (FULL_SIMP_TAC (srw_ss()) [term2sexp_def,list2sexp_def,list2sexp_11,LSIZE_def]
    \\ REVERSE (REPEAT STRIP_TAC) THEN1
     (Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
      \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS ORELSE MATCH_MP_TAC LSIZE_CDR_LESS)
      \\ FULL_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
    \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [sexp2list_def,CAR_def,MAP,LSIZE_def]
    \\ Q.PAT_X_ASSUM `!x.bbb` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ REVERSE (Induct_on `S'`)
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss []) THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
    \\ SIMP_TAC std_ss [sexp2list_def,MAP,CONS_11] \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
      \\ POP_ASSUM MATCH_MP_TAC
      \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS ORELSE MATCH_MP_TAC LSIZE_CDR_LESS)
      \\ FULL_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
    \\ Q.PAT_X_ASSUM `(!x.bbb) ==> ccc` MATCH_MP_TAC \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
  \\ Cases_on `CAR a = Sym "LAMBDA"` \\ FULL_SIMP_TAC std_ss [] THEN1
   (SIMP_TAC (srw_ss()) [term2sexp_def,list2sexp_def]
    \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ SIMP_TAC std_ss [LSIZE_def]
    \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS ORELSE MATCH_MP_TAC LSIZE_CDR_LESS)
    \\ FULL_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,func2sexp_def,APPEND,list2sexp_def,sfix_def]
  \\ sg `~MEM (getSym a) reserved_names`
  \\ FULL_SIMP_TAC std_ss [term2sexp_def,func2sexp_def,APPEND,list2sexp_def,sfix_def]
  \\ Cases_on `a` THEN1 EVAL_TAC THEN1 EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [getSym_def]
  \\ EVAL_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [sym2prim_def]);

(*

(* bytecode deterministic *)

val LENGTH_APPEND_EQ_IMP = prove(
  ``!xs1 xs2 ys1 ys2.
      (LENGTH xs1 = LENGTH xs2) ==>
      ((xs1 ++ ys1 = xs2 ++ ys2) ==> (xs1 = xs2) /\ (ys1 = ys2))``,
  Induct \\ Cases_on `xs2`
  \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,APPEND,CONS_11] \\ METIS_TAC []);

val LENGTH_REVERSE_APPEND_EQ_IMP = prove(
  ``!xs1 xs2 ys1 ys2.
      (LENGTH xs1 = LENGTH xs2) /\ (REVERSE xs1 ++ ys1 = REVERSE xs2 ++ ys2) ==>
      (xs1 = xs2) /\ (ys1 = ys2)``,
  Induct \\ Cases_on `xs2`
  \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,APPEND,CONS_11,REVERSE_DEF]
  \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] \\ NTAC 4 STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [CONS_11]);

val list2sexp_MAP_Sym_11 = prove(
  ``!xs ys. (list2sexp (MAP Sym xs) = list2sexp (MAP Sym ys)) ==> (xs = ys)``,
  Induct \\ Cases_on `ys` \\ ASM_SIMP_TAC (srw_ss()) [list2sexp_def,MAP]);

val iSTEP_DETERMINISTIC = store_thm("iSTEP_DETERMINISTIC",
  ``!x y1 y2. iSTEP x y1 /\ iSTEP x y2 ==> (y1 = y2)``,
  ONCVE_REWRITE_TAC [iSTEP_cases] \\ REPEAT STRIP_TAC
  \\ REPEAT (Q.PAT_X_ASSUM `CONTAINS_BYTECODE xx yy zz` MP_TAC)
  \\ FULL_SIMP_TAC (srw_ss()) [CONS_11,CONTAINS_BYTECODE_def]
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC [LENGTH_APPEND_EQ_IMP]
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LENGTH_REVERSE_APPEND_EQ_IMP \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `fc' = fc` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ Q.PAT_X_ASSUM `bc' = bc` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ REPEAT (Q.PAT_X_ASSUM `BC_COMPILE xxx = yyy` MP_TAC)
  \\ IMP_RES_TAC list2sexp_MAP_Sym_11 \\ FULL_SIMP_TAC std_ss []);

*)

val _ = export_theory();
