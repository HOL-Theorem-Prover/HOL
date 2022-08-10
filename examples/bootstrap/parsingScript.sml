
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory source_syntaxTheory;

val _ = new_theory "parsing";


(* lexing *)

Datatype:
  token = OPEN | CLOSE | DOT | NUM num | QUOTE num
End

Definition read_num_def:
  read_num l h f x acc [] = (acc,[]) ∧
  read_num l h f x acc (c::cs) =
    if ORD l ≤ ORD c ∧ ORD c ≤ ORD h then
      read_num l h f x (f * acc + (ORD c - x)) cs
    else (acc,c::cs)
End

Theorem read_num_length:
  ∀l h xs n ys f acc x.
    read_num l h f x acc xs = (n,ys) ⇒
    LENGTH ys ≤ LENGTH xs ∧ (xs ≠ ys ⇒ LENGTH ys < LENGTH xs)
Proof
  Induct_on ‘xs’ \\ rw [read_num_def]
  \\ TRY pairarg_tac \\ fs [] \\ rw [] \\ res_tac \\ fs []
QED

Definition end_line_def:
  end_line [] = [] ∧
  end_line (c::cs) = if c = #"\n" then cs else end_line cs
End

Theorem end_line_length:
  ∀cs. STRLEN (end_line cs) < SUC (STRLEN cs)
Proof
  Induct \\ rw [end_line_def]
QED

Definition lex_def:
  lex q [] acc = acc ∧
  lex q (c::cs) acc =
      if MEM c " \t\n" then lex NUM cs acc else
      if c = #"#" then lex NUM (end_line cs) acc else
      if c = #"." then lex NUM cs (DOT::acc) else
      if c = #"(" then lex NUM cs (OPEN::acc) else
      if c = #")" then lex NUM cs (CLOSE::acc) else
      if c = #"'" then lex QUOTE cs acc else
        let (n,rest) = read_num #"0" #"9" 10 (ORD #"0") 0 (c::cs) in
          if rest ≠ c::cs then lex NUM rest (q n::acc) else
            let (n,rest) = read_num #"*" #"z" 256 0 0 (c::cs) in
              if rest ≠ c::cs then lex NUM rest (q n::acc) else
                lex NUM cs acc
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND)’ \\ rw []
  \\ imp_res_tac (GSYM read_num_length) \\ fs [end_line_length]
End

Definition lexer_def:
  lexer input = lex NUM input []
End


(* parsing *)

Definition quote_def:
  quote n = list [Num (name "'"); Num n]
End

Definition parse_def:
  parse [] x s = x ∧
  parse (CLOSE :: rest) x s = parse rest (Num 0) (x::s) ∧
  parse (OPEN :: rest) x s =
    (case s of [] => parse rest x s
     | (y::ys) => parse rest (Pair x y) ys) ∧
  parse (NUM n :: rest) x s = parse rest (Pair (Num n) x) s ∧
  parse (QUOTE n :: rest) x s = parse rest (Pair (quote n) x) s ∧
  parse (DOT :: rest) x s = parse rest (head x) s
End


(* converting from v to prog *)

Definition v2test_def:
  v2test v = if getNum v = name "<" then Less else Equal
End

Definition v2list_def:
  v2list v = if isNum v then [] else head v :: v2list (tail v)
Termination
  WF_REL_TAC ‘measure v_size’
  \\ rpt conj_tac \\ rw [name_def]
  \\ rpt (goal_term (fn tm => tmCases_on (hd (free_vars (rator tm))) [] \\ fs []))
End

Definition conses_def:
  conses [] = Op Cons [] ∧
  conses [x] = Op Cons [x] ∧
  conses [x;y] = Op Cons [x;y] ∧
  conses (x::xs) = Op Cons [x; conses xs]
End

Definition pat_lets_def:
  pat_lets x v rhs =
    if isNum v then rhs else
      let var = getNum (head v) in
        Let var (Op Head [x])
          (pat_lets (Op Tail [x]) (tail v) rhs)
Termination
  WF_REL_TAC ‘measure (λ(x,v,rhs). v_size v)’ \\ rw []
  \\ rpt (goal_term (fn tm => tmCases_on (find_term is_var (rator tm)) [] \\ fs []))
End

Definition num2exp_def:
  num2exp n = if is_upper n then Const n else Var n
End

fun apply_at_conv p c tm =
  DEPTH_CONV (fn tm => if p tm then c tm else NO_CONV tm
                       handle HOL_ERR _ => NO_CONV tm) tm;

fun apply_at_pat_conv pat = apply_at_conv (can (match_term pat));

Definition v2exp_def:
  v2exp v =
    (if isNum v then num2exp (getNum v) else
       let n = getNum (head v) in
         if n = name "'" then Const (getNum (el1 v)) else
         if n = name "+" then Op Add (v2exps (tail v)) else
         if n = name "-" then Op Sub (v2exps (tail v)) else
         if n = name "div" then Op Div (v2exps (tail v)) else
         if n = name "cons" then conses (v2exps (tail v)) else
         if n = name "cons*" then Op Cons (v2exps (tail v)) else
         if n = name "list" then conses (v2exps (tail v) ++ [Const 0]) else
         if n = name "head" then Op Head (v2exps (tail v)) else
         if n = name "tail" then Op Tail (v2exps (tail v)) else
         if n = name "read" then Op Read (v2exps (tail v)) else
         if n = name "case" then v2case (v2exp (el1 v)) (tail (tail v)) else
         if n = name "write" then Op Write (v2exps (tail v)) else
         if n = name "if" then
           If (v2test (head (el1 v)))
             (v2exps (tail (el1 v))) (v2exp (el2 v)) (v2exp (el3 v)) else
         if n = name "let" then v2lets (tail v) else
         if n = name "var" then Var (getNum (head (tail v))) else
         if n = name "call" then
           Call (getNum (el1 v)) (v2exps (tail (tail v)))
         else otherwise (if is_upper n then
           conses (Const n :: (v2exps (tail v) ++ [Const 0]))
         else Call (getNum (el0 v)) (v2exps (tail v)))) ∧
  v2exps v =
    (if isNil v then [] else v2exp (head v) :: v2exps (tail v)) ∧
  v2lets v =
    (if isNum v then Const 0 else
       Let (getNum (el0 (el0 v))) (v2exp (el1 (el0 v)))
         if isNum (tail (tail v)) then v2exp (el1 v) else v2lets (tail v)) ∧
  v2case x v =
    (if isNum v then Const 0 else
       let row = el0 v in
       let pat = head row in
       let rhs = el1 row in
         if isNum pat then
           if getNum pat = name "_" then
             If Less [Const 0; Const 1] (v2exp rhs) (v2case x (tail v))
           else
             If Equal [x; Const (getNum pat)] (v2exp rhs) (v2case x (tail v))
         else
           If Equal [Const (getNum (head pat)); Op Head [x]]
             (pat_lets (Op Tail [x]) (tail pat) (v2exp rhs)) (v2case x (tail v)))
Termination
  WF_REL_TAC ‘measure (λx. case x of INL v => v_size v
                                   | INR (INL v) => v_size v
                                   | INR (INR (INL v)) => v_size v
                                   | INR (INR (INR (x, v))) => v_size v)’
  \\ CONV_TAC (apply_at_pat_conv “name _” EVAL)
  \\ rpt strip_tac
  \\ Cases_on ‘v’ \\ full_simp_tac std_ss [isNum_def,head_def,tail_def,v_size_def]
  \\ rpt (pop_assum kall_tac) \\ fs []
  \\ rpt (goal_term (fn tm => tmCases_on (find_term is_var (rator tm)) [] \\ fs []))
End

Definition vs2args_def:
  vs2args [] = [] ∧
  vs2args (v::vs) = getNum (el1 v) :: vs2args vs
End

Definition v2dec_def:
  v2dec v = Defun (getNum (el1 v))
                  (vs2args (v2list (el2 v)))
                  (v2exp (el3 v))
End

Definition vs2prog_def:
  vs2prog [] = Program [] (Const 0) ∧
  vs2prog [v] = Program [] (v2exp v) ∧
  vs2prog (v::vs) =
    case vs2prog vs of Program ds m => Program (v2dec v :: ds) m
End

(* entire parser *)

Definition parser_def:
  parser tokens =
    vs2prog (v2list (parse tokens (Num 0) []))
End

val _ = export_theory();
