open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_eval";

open lisp_opsTheory compilerLib;


val _ = let
  val thms = DB.match [] ``SPEC ARM_MODEL``
  val thms = filter (can (find_term (can (match_term ``aLISP``))) o concl) (map (fst o snd) thms)
  val renamer = Q.INST [`x1`|->`exp`,`x2`|->`x`,`x3`|->`y`,`x4`|->`z`,`x5`|->`stack`,`x6`|->`alist`]
  val thms = map renamer thms
  val thms = map (RW [arm_alloc_code,arm_equal_code]) thms
  val _ = add_compiled thms
  in () end;

val _ = let
  val thms = DB.match [] ``SPEC PPC_MODEL``
  val thms = filter (can (find_term (can (match_term ``pLISP``))) o concl) (map (fst o snd) thms)
  val renamer = Q.INST [`x1`|->`exp`,`x2`|->`x`,`x3`|->`y`,`x4`|->`z`,`x5`|->`stack`,`x6`|->`alist`]
  val thms = map renamer thms
  val thms = map (RW [ppc_alloc_code,ppc_equal_code]) thms
  val _ = add_compiled thms
  in () end;

val _ = let
  val thms = DB.match [] ``SPEC X86_MODEL``
  val thms = filter (can (find_term (can (match_term ``xLISP``))) o concl) (map (fst o snd) thms)
  val renamer = Q.INST [`x1`|->`exp`,`x2`|->`x`,`x3`|->`y`,`x4`|->`z`,`x5`|->`stack`,`x6`|->`alist`]
  val thms = map renamer thms
  val thms = map (RW [x86_alloc_code,x86_equal_code]) thms
  val _ = add_compiled thms
  in () end;


fun compile_lisp_eval target = let

val (x,def1,z) = compile target ``
  lookup_loop (exp,x,z) = 
    let x = CAR z in
    let x = CAR x in
      if exp = x then 
        let x = CAR z in
        let x = CDR x in (exp,x,z)
      else 
        let z = CDR z in
          lookup_loop (exp,x,z)``;

val (x,def2,z) = compile target ``
  lookup (exp,x,alist) = 
    let z = alist in
    let (exp,x,z) = lookup_loop (exp,x,z) in
      (exp,x,z,alist)``;

val (x,def3,z) = compile target ``
  lisp_eval_pair(exp,x:SExp,y:SExp,z:SExp,stack:SExp,alist:SExp,limit:num) =
    if x = Sym "quote" then 
      let exp = CAR exp in
      let x = Sym "t" in  (* i.e. mark that the evaluation is complete *)
        (exp,x,y,z,stack,alist,limit)
    else (* all others require the first argument to be evaluated *) 
      let y = CAR exp in
      let exp = CDR exp in
      let exp = Dot exp x in (* make pair of the other args and the func name *)
      let x = stack in
      let stack = Sym "nil" in
      let exp = Dot exp x in
      let stack = exp in (* push the pair onto the stack *)
      let exp = y in
      let x = Sym "nil" in (* i.e. mark that next iteration is to evaluate exp *)
        (exp,x,y,z,stack,alist,limit)``;

val (x,def4,z) = compile target ``
  (* x = function name, y = first arg, exp = second arg *)
  eval_two_arg_func(exp,x:SExp,y:SExp,z:SExp,stack:SExp,alist:SExp,limit:num) =
    if x = Sym "-" then 
      let x = y in
      let exp = LISP_SUB exp x in
      let x = Sym "t" in
        (exp,x,y,z,stack,alist,limit)
    else if x = Sym "+" then 
      let x = y in
      let exp = LISP_ADD exp x in
      let x = Sym "t" in
        (exp,x,y,z,stack,alist,limit)
    else if x = Sym "equal" then 
      let x = y in
      let exp = LISP_EQUAL exp x in
      let x = Sym "t" in
        (exp,x,y,z,stack,alist,limit)
    else if x = Sym "cons" then 
      let x = y in
      let exp = Dot exp x in
      let x = Sym "t" in
        (exp,x,y,z,stack,alist,limit)
    else 
      (exp,x,y,z,stack,alist,limit)`` 

val (x,def4,z) = compile target ``
  (* x = function name, exp = first (and only) arg *)
  eval_consp(exp:SExp) =
    if isDot exp then 
      let exp = Sym "t" in exp
    else 
      let exp = Sym "nil" in exp``

val (x,def4,z) = compile target ``
  (* x = function name, exp = first (and only) arg *)
  eval_symbolp(exp:SExp) =
    if isSym exp then 
      let exp = Sym "t" in exp
    else 
      let exp = Sym "nil" in exp``

val (x,def4,z) = compile target ``
  (* x = function name, exp = first (and only) arg *)
  eval_numberp(exp:SExp) =
    if isSym exp then 
      let exp = Sym "nil" in exp
    else 
      if isDot exp then 
        let exp = Sym "nil" in exp
      else 
        let exp = Sym "t" in exp``

val (x,def4,z) = compile target ``
  (* x = function name, exp = first (and only) arg *)
  eval_one_arg_func(exp:SExp,x:SExp,y:SExp) =
    if x = Sym "car" then 
      let exp = CAR exp in
      let x = Sym "t" in
        (exp,x,y)
    else if x = Sym "cdr" then 
      let exp = CDR exp in
      let x = Sym "t" in
        (exp,x,y)
    else if x = Sym "consp" then 
      let exp = eval_consp exp in
      let x = Sym "t" in
        (exp,x,y)
    else if x = Sym "symbolp" then 
      let exp = eval_symbolp exp in
      let x = Sym "t" in
        (exp,x,y)
    else if x = Sym "numberp" then 
      let exp = eval_numberp exp in
      let x = Sym "t" in
        (exp,x,y)
    else (exp,x,y)``

val (x,def5,z) = compile target ``
  lisp_eval_normal(exp:SExp,x:SExp,y:SExp,z:SExp,stack:SExp,alist:SExp,limit:num) =
    if isDot y then (* if there are unevaluated arguments *)
      let exp = Dot exp x in 
      let x = CDR y in
      let exp = Dot exp x in 
      let x = stack in
      let exp = Dot exp x in 
      let stack = exp in     
      (* make the stack: Dot (Dot (Dot evalaued_arg function_name) (Sym "nil")) old_stack *)
      let exp = CAR y in
      let x = Sym "nil" in 
        (exp,x,y,z,stack,alist,limit)      
    else
      if isDot x then (* if, there are more than one evaluated arg *)
        let y = CDR x in
        let x = CAR x in  
        (* x = function name, y = first arg, exp = second arg *)
        let (exp,x,y,z,stack,alist,limit) = eval_two_arg_func(exp,x,y,z,stack,alist,limit) in
          (exp,x,y,z,stack,alist,limit)
      else (* only one arg *)
        (* x = function name, exp = first (and only) arg *)
        let (exp,x,y) = eval_one_arg_func(exp,x,y) in
          (exp,x,y,z,stack,alist,limit)`` 

val (x,def6,z) = compile target ``
  lisp_eval_if(exp:SExp,x:SExp,y:SExp,z:SExp,stack:SExp,alist:SExp,limit:num) =
      let x = exp in
        if x = Sym "nil" then 
          let y = CDR y in
          let exp = CAR y in  
          let x = Sym "nil" in
            (exp,x,y,z,stack,alist,limit)
        else 
          let exp = CAR y in  
          let x = Sym "nil" in
            (exp,x,y,z,stack,alist,limit)``;

val (x,def6,z) = compile target ``
  lisp_continue(exp:SExp,x:SExp,y:SExp,z:SExp,stack:SExp,alist:SExp,limit:num) =
    if x = Sym "if" then
      let (exp,x,y,z,stack,alist,limit) = lisp_eval_if(exp,x,y,z,stack,alist,limit) in
        (exp,x,y,z,stack,alist,limit)
    else (* if it's not an if-statement *)  
      let (exp,x,y,z,stack,alist,limit) = lisp_eval_normal(exp,x,y,z,stack,alist,limit) in
        (exp,x,y,z,stack,alist,limit)``

val (x,def8,z) = compile target ``
  lisp_eval_atom(exp:SExp,x:SExp,y:SExp,z:SExp,stack:SExp,alist:SExp,limit:num) =
    let x = Sym "t" in
      if isSym exp then 
        let (exp,x,z,alist) = lookup(exp,x,alist) in
          (exp,x,y,z,stack,alist,limit)
      else (* exp is a Num *)
          (exp,x,y,z,stack,alist,limit)``;        

val (x,def7,z) = compile target ``
  lisp_evaluate(exp:SExp,x:SExp,y:SExp,z:SExp,stack:SExp,alist:SExp,limit:num) =
    if isDot exp then 
      let x = CAR exp in
      let exp = CDR exp in
      let (exp,x,y,z,stack,alist,limit) = lisp_eval_pair(exp,x,y,z,stack,alist,limit) in
        (exp,x,y,z,stack,alist,limit)
    else 
      let (exp,x,y,z,stack,alist,limit) = lisp_eval_atom(exp,x,y,z,stack,alist,limit) in
        (exp,x,y,z,stack,alist,limit)``;

val (x,def6,z) = compile target ``
  lisp_eval (exp,x,y,z,stack,alist,limit) = 
    if x = Sym "nil" then (* the task is to evaluate, if x = Sym "nil" *) 
      let (exp,x,y,z,stack,alist,limit) = lisp_evaluate(exp,x,y,z,stack,alist,limit) in
        lisp_eval (exp,x,y,z,stack,alist,limit)
    else (* otherwise, the task is to continue *)   
      if isDot stack then (* if there are items on the to-do list *)
        let y = CAR stack in
        let stack = CDR stack in (* pop an element of the stack *)
        let x = CDR y in
        let y = CAR y in
        let (exp,x,y,z,stack,alist,limit) = lisp_continue(exp,x,y,z,stack,alist,limit) in
          lisp_eval (exp,x,y,z,stack,alist,limit)
      else (* there is nothing left to do, return *)          
        (exp,x,y,z,stack,alist,limit)`` 

in save_thm("lisp_eval_" ^ target, x) end;

val _ = compile_lisp_eval "ARM"
val _ = compile_lisp_eval "PowerPC"
val _ = compile_lisp_eval "x86"
    
val _ = export_theory();

