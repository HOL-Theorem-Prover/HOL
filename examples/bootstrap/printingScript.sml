
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory source_syntaxTheory mp_then;

val _ = new_theory "printing";


(* pretty printing v *)

Definition num2str_def:
  num2str n = if n < 10 then [CHR (48 + n)] else
                num2str (n DIV 10) ++ [CHR (48 + (n MOD 10))]
End

Definition num2ascii_def:
  num2ascii n =
    if n = 0 then NONE else
      let k = n MOD 256 in
        if (ORD #"*" ≤ k ∧ k ≤ ORD #"z" ∧ k ≠ ORD #".") then
          if n < 256 then SOME [CHR k] else
            case num2ascii (n DIV 256) of
            | NONE => NONE
            | SOME s => SOME (s ++ [CHR k])
        else NONE
End

Definition ascii_name_def:
  ascii_name n =
    case num2ascii n of
    | NONE => NONE
    | SOME s => let k = ORD (HD s) in
                  if ORD #"0" ≤ k ∧ k ≤ ORD #"9" then NONE else SOME s
End

Definition name2str_def:
  name2str n =
    case ascii_name n of NONE => num2str n | SOME s => s
End

Definition dest_quote_def:
  dest_quote v =
    case v of
    | (Pair x (Pair (Num n) (Num 0))) =>
        (if x = Num (name "'") then SOME ("'" ++ name2str n) else NONE)
    | _ => NONE
End

Definition dest_list_def:
  dest_list (Num n) = ([],Num n) ∧
  dest_list (Pair x y) = let (l,e) = dest_list y in (x::l,e)
End

Theorem dest_list_size:
  ∀v e l.
    (l,e) = dest_list v ⇒
    v_size e ≤ v_size v ∧
    (~isNum v ⇒ v_size e < v_size v) ∧
    ∀x. MEM x l ⇒ v_size x < v_size v
Proof
  Induct_on ‘v’ \\ fs [dest_list_def,isNum_def]
  \\ pairarg_tac \\ fs [] \\ rw [] \\ res_tac \\ fs [v_size_def]
QED

Datatype:
  pretty = Parenthesis pretty
         | Str string | Append pretty bool pretty | Size num pretty
End

Definition newlines_def:
  newlines [] = Str "" ∧
  newlines [x] = x ∧
  newlines (x::xs) = Append x T (newlines xs)
End

Definition v2pretty_def:
  v2pretty v =
    case v of Num n => Str (name2str n) | _ =>
    case dest_quote v of SOME s => Str s | NONE =>
      let (l,e) = dest_list v in
        Parenthesis
          (if e = Num 0 then newlines (MAP v2pretty l) else
             Append (newlines (MAP v2pretty l)) T
               (Append (Str " . ") T (v2pretty e)))
Termination
  WF_REL_TAC ‘measure v_size’ \\ rw []
  \\ imp_res_tac dest_list_size \\ fs [v_size_def,isNum_def]
End

Definition get_size_def:
  get_size (Size n x) = n ∧
  get_size (Append x _ y) = get_size x + get_size y + 1 ∧
  get_size (Parenthesis x) = get_size x + 2 ∧
  get_size _ = 0
End

Definition get_next_size_def:
  get_next_size (Size n x) = n ∧
  get_next_size (Append x _ y) = get_next_size x ∧
  get_next_size (Parenthesis x) = get_next_size x + 2 ∧
  get_next_size _ = 0
End

Definition annotate_def:
  annotate (Str s) = Size (LENGTH s) (Str s) ∧
  annotate (Parenthesis b) =
    (let b = annotate b in
       Size (get_size b + 2) (Parenthesis b)) ∧
  annotate (Append b1 n b2) =
    (let b1 = annotate b1 in
     let b2 = annotate b2 in
       (* Size (get_size b1 + get_size b2 + 1) *) (Append b1 n b2)) ∧
  annotate (Size n b) = annotate b
End

Definition remove_all_def:
  remove_all (Parenthesis v) = Parenthesis (remove_all v) ∧
  remove_all (Str v1) = Str v1 ∧
  remove_all (Append v2 _ v3) = Append (remove_all v2) F (remove_all v3) ∧
  remove_all (Size v4 v5) = remove_all v5
End

Definition smart_remove_def:
  smart_remove i k (Size n b) =
    (if k + n < 70 then remove_all b else smart_remove i k b) ∧
  smart_remove i k (Parenthesis v) = Parenthesis (smart_remove (i+1) (k+1) v) ∧
  smart_remove i k (Str v1) = Str v1 ∧
  smart_remove i k (Append v2 b v3) =
    let n2 = get_size v2 in
    let n3 = get_next_size v3 in
      if k + n2 + n3 < 50 then
        Append (smart_remove i k v2) F (smart_remove i (k+n2) v3)
      else
        Append (smart_remove i k v2) T (smart_remove i i v3)
End

Definition flatten_def:
  flatten indent (Size n p) s = flatten indent p s ∧
  flatten indent (Parenthesis p) s = "(" ++ flatten (indent ++ "   ") p (")" ++ s) ∧
  flatten indent (Str t) s = t ++ s ∧
  flatten indent (Append p1 b p2) s =
    flatten indent p1 ((if b then indent else " ") ++ flatten indent p2 s)
End

Definition v2str_def:
  v2str v = flatten "\n" (smart_remove 0 0 (annotate (v2pretty v))) ""
End

Definition is_comment_def:
  is_comment [] = T ∧
  is_comment (c::cs) =
    if c = CHR 35 then
      (case dropWhile (λx. x ≠ CHR 10) cs of
       | [] => F
       | (c::cs) => is_comment cs)
    else if c = CHR 10 then is_comment cs else F
Termination
  WF_REL_TAC ‘measure LENGTH’ \\ rw []
  \\ rename [‘dropWhile f xs’]
  \\ qspecl_then [‘f’,‘xs’] mp_tac LENGTH_dropWhile_LESS_EQ
  \\ fs []
End

Definition vs2str_def:
  vs2str [] coms = "\n" ∧
  vs2str (x::xs) coms =
    ((case coms of [] => [] | (c::cs) => if is_comment c then c else []) ++
    ("\n" ++ (v2str x ++ ("\n" ++ vs2str xs (case coms of [] => [] | c::cs => cs)))))
End


(* converting prog to v *)

Definition op2str_def:
  op2str Add = "+" ∧
  op2str Sub = "-" ∧
  op2str Div = "div" ∧
  op2str Cons = "cons*" ∧
  op2str Head = "head" ∧
  op2str Tail = "tail" ∧
  op2str Read = "read" ∧
  op2str Write = "write"
End

Definition test2str_def:
  test2str Less = "<" ∧
  test2str Equal = "="
End

Definition protected_names_def:
  protected_names =
    (* does not need to include "defun" *)
    ["'"; "if"; "let"; "call"; "+"; "-"; "div"; "<"; "="; "cons"; "cons*";
     "head"; "tail"; "read"; "write"; "list"; "case"; "var"]
End

Definition dest_cons_chain_def:
  dest_cons_chain (Op Cons [x; y]) =
    (case dest_cons_chain y of
     | NONE => SOME [x; y]
     | SOME xs => SOME (x :: xs)) ∧
  dest_cons_chain _ = NONE
End

Theorem dest_cons_chain_size:
  ∀x vs. dest_cons_chain x = SOME vs ⇒ exp1_size vs + op_size Cons + 1 ≤ exp_size x
Proof
  completeInduct_on ‘exp_size x’ \\ rw [] \\ fs [PULL_FORALL]
  \\ qpat_x_assum ‘dest_cons_chain _ = SOME _’ mp_tac
  \\ once_rewrite_tac [DefnBase.one_line_ify NONE dest_cons_chain_def]
  \\ fs [AllCaseEqs()] \\ rw []
  THEN1 (rw [] \\ fs [] \\ fs [exp_size_def])
  \\ first_assum (first_assum o mp_then Any mp_tac)
  \\ strip_tac \\ fs [exp_size_def]
QED

Definition up_const_def:
  up_const (Const n::_) = (if is_upper n then SOME n else NONE) ∧
  up_const _ = NONE
End

Definition is_Let_def[simp]:
  is_Let (Let _ _ _) = T ∧
  is_Let _ = F
End

Theorem exp_size_non_zero:
  exp_size y ≠ 0
Proof
  Cases_on ‘y’ \\ fs [exp_size_def]
QED

Triviality FRONT_exp1_size:
  ¬NULL v ⇒ exp1_size (FRONT v) ≤ exp1_size v
Proof
  Cases_on ‘v = []’ \\ fs []
  \\ qspec_then ‘v’ mp_tac SNOC_CASES \\ asm_rewrite_tac []
  \\ strip_tac \\ full_simp_tac std_ss [FRONT_SNOC]
  \\ rw [] \\ fs [SNOC_APPEND]
  \\ Induct_on ‘l’ \\ fs [exp_size_def]
QED

Definition dest_case_lets_def:
  dest_case_lets z (Let v x y) =
    (if x ≠ Op Head [z] then ([], Let v x y) else
       let (vs,t) = dest_case_lets (Op Tail [z]) y in
         (v::vs,t)) ∧
  dest_case_lets z r = ([],r)
End

Definition dest_case_tree_def:
  dest_case_tree y (Const n) = (if n = 0 then SOME [] else NONE) ∧
  dest_case_tree y (If Equal [Const k; x] t1 t2) =
    (if x ≠ Op Head [y] then NONE else
       case dest_case_tree y t2 of
       | NONE => NONE
       | SOME rows =>
          let (vars,rhs) = dest_case_lets (Op Tail [y]) t1 in
            SOME ((k,vars,rhs)::rows)) ∧
  dest_case_tree y _ = NONE
End

Definition row2v_def:
  row2v [] = Num 0 ∧
  row2v ((k,vars,v)::rest) = cons (list [list (Num k :: MAP Num vars); v]) (row2v rest)
End

Definition get_Op_Head_def:
  get_Op_Head (Op Head [x]) = x ∧
  get_Op_Head _ = Const 0
End

Definition dest_case_enum_def:
  dest_case_enum y (Const n) = (if n = 0 then SOME [] else NONE) ∧
  dest_case_enum y (If Equal [x; Const k] t1 t2) =
    (if x ≠ y then NONE else
     if k = name "_" then NONE else
       case dest_case_enum y t2 of
       | NONE => NONE
       | SOME rows => SOME ((SOME k,t1)::rows)) ∧
  dest_case_enum y (If Less [Const n; Const m] t1 t2) =
    (if n ≠ 0 ∨ m ≠ 1 then NONE else
       case dest_case_enum y t2 of
       | NONE => NONE
       | SOME rows => SOME ((NONE,t1)::rows)) ∧
  dest_case_enum y _ = NONE
End

Definition enum2v_def:
  enum2v [] = Num 0 ∧
  enum2v ((NONE,v)::rest) = cons (list [Name "_"; v]) (enum2v rest) ∧
  enum2v ((SOME k,v)::rest) =  cons (list [Num k; v]) (enum2v rest)
End

Theorem dest_case_enum_exp_size:
  ∀a x rows t h h' y z.
    dest_case_enum a x = SOME rows ∧
    x = If t [h; h'] y z ⇒
    list_size exp_size (MAP SND rows) <
    exp_size h + exp_size h' + exp_size y + exp_size z
Proof
  ho_match_mp_tac dest_case_enum_ind
  \\ simp [dest_case_enum_def,AllCaseEqs()] \\ rw []
  \\ gvs [list_size_def,exp_size_def]
  \\ qpat_x_assum ‘_ = SOME _’ mp_tac
  \\ simp [Once (oneline dest_case_enum_def), AllCaseEqs()]
  \\ strip_tac \\ gvs [list_size_def,exp_size_def,exp_size_eq]
QED

Theorem dest_case_lets_exp_size:
  ∀x y vars e. dest_case_lets x y = (vars,e) ⇒ exp_size e ≤ exp_size y
Proof
  ho_match_mp_tac dest_case_lets_ind
  \\ fs [dest_case_lets_def]
  \\ rw [] \\ pairarg_tac \\ fs [] \\ rw []
  \\ fs [exp_size_def]
QED

Theorem dest_case_tree_exp_size:
  ∀z a t xs y rows.
    dest_case_tree a (If t xs y z) = SOME rows ⇒
    list_size exp_size (MAP SND (MAP SND rows)) ≤ exp_size y + exp_size z ∧
    exp_size a < exp1_size xs
Proof
  gen_tac \\ completeInduct_on ‘exp_size z’
  \\ gen_tac \\ strip_tac \\ fs [PULL_FORALL]
  \\ simp [Once (DefnBase.one_line_ify NONE dest_case_tree_def), AllCaseEqs()]
  \\ fs [PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ fs []
  \\ rpt BasicProvers.var_eq_tac
  \\ rw [] \\ fs [exp_size_def,list_size_def]
  \\ ‘exp_size z ≠ 0’ by (Cases_on ‘z’ \\ fs [exp_size_def])
  \\ imp_res_tac dest_case_lets_exp_size \\ fs []
  \\ Cases_on ‘z’ \\ fs [dest_case_tree_def]
  \\ rw [] \\ fs [list_size_def,exp_size_def]
  \\ rename [‘If _ _ _ e4’]
  \\ first_x_assum (qspec_then ‘e4’ mp_tac)
  \\ fs [exp_size_def]
  \\ disch_then drule \\ fs []
QED

Definition is_protected_def:
  is_protected n ⇔ MEM n (MAP name protected_names) ∨ is_upper n
End

Definition exp2v_def:
  exp2v (Var v) =
    (if is_upper v then list [Num (name "var"); Num v] else Num v) ∧
  exp2v (Const n) =
    (if is_upper n then Num n else list [Num (name "'"); Num n]) ∧
  exp2v (Op op es) =
    (case dest_cons_chain (Op op es) of
     | SOME es =>
         if ~NULL es ∧ LAST es = Const 0 then
           (case up_const es of
            | NONE => list ([Name "list"] ++ FRONT (exps2v es))
            | SOME k => list (Num k :: FRONT (exps2v (TL es))))
         else list ([Name "cons"] ++ exps2v es)
     | NONE => list ([Name (op2str op)] ++ exps2v es)) ∧
  exp2v (If t xs y z) =
    (if LENGTH xs = 2 then
       let x0 = HD xs in
       let x1 = EL 1 xs in
        (case dest_case_enum x0 (If t xs y z) of
         | SOME rows =>
             let xs = exps2v (MAP SND rows) in
             let ys = ZIP (MAP FST rows, xs) in
               cons (Name "case") (cons (exp2v x0) (enum2v ys))
         | NONE =>
           case dest_case_tree (get_Op_Head x1) (If t xs y z) of
           | SOME rows =>
               let xs = exps2v (MAP SND (MAP SND rows)) in
               let ys = ZIP (MAP FST rows, ZIP (MAP (FST o SND) rows, xs)) in
                 cons (Name "case") (cons (exp2v (get_Op_Head x1)) (row2v ys))
           | NONE =>
              list [Num (name "if");
                    list (Num (name (test2str t)) :: exps2v xs);
                    exp2v y; exp2v z])
     else
       list [Num (name "if");
             list (Num (name (test2str t)) :: exps2v xs);
             exp2v y; exp2v z]) ∧
  exp2v (Let v x y) =
    (cons (Name "let") (lets2v (Let v x y))) ∧
  exp2v (Call n es) =
    (if is_protected n then
       list ([Num (name "call"); Num n] ++ exps2v es)
     else list ([Num n] ++ exps2v es)) ∧
  exps2v [] = [] ∧
  exps2v (v::vs) = exp2v v :: exps2v vs ∧
  lets2v (Let v x y) = (cons (list [Num v; exp2v x])
                             (if is_Let y then lets2v y else list [exp2v y])) ∧
  lets2v _ = Num 0
Termination
  WF_REL_TAC ‘measure (λx. case x of INL v => exp_size v + 1
                                   | INR (INL v) => list_size exp_size v + 1
                                   | INR (INR v) => exp_size v)’ \\ rw []
  \\ gvs [LENGTH_EQ_NUM_compute,list_size_def,exp_size_def,exp_size_eq]
  \\ ‘exp_size x ≠ 0 ∧ exp_size y ≠ 0’ by fs [exp_size_non_zero] \\ fs []
  \\ imp_res_tac dest_case_enum_exp_size \\ fs [exp_size_def]
  \\ imp_res_tac dest_case_tree_exp_size \\ fs [exp_size_def]
  \\ imp_res_tac dest_cons_chain_size \\ gvs [exp_size_eq,exp_size_def]
  \\ TRY (Cases_on ‘op’) \\ fs [dest_cons_chain_def]
  \\ Cases_on ‘v’ \\ gvs [list_size_def]
End

Definition dec2v_def:
  dec2v (Defun n params body) =
    list [Num (name "defun"); Num n; list (MAP Num params); exp2v body]
End

Definition prog2vs_def:
  prog2vs (Program [] main) = [exp2v main] ∧
  prog2vs (Program (d::ds) main) = dec2v d :: prog2vs (Program ds main)
End


(* entire pretty printer *)

Definition prog2str_def:
  prog2str p = vs2str (prog2vs p)
End

val _ = export_theory();
