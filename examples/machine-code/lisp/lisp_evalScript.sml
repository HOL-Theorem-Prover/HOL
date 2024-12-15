open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_eval";

open compilerLib codegenLib decompilerLib;
open lisp_opsTheory;

val _ = let
  val thms = DB.match [] ``SPEC ARM_MODEL``
  val thms = filter (can (find_term (can (match_term ``aLISP``))) o concl)
                    (map (#1 o #2) thms)
  val renamer = Q.INST [‘x1’|->‘exp’,‘x2’|->‘x’,‘x3’|->‘y’,‘x4’|->‘z’,
                        ‘x5’|->‘stack’,‘x6’|->‘alist’] o
                INST [“limit:num”|->“l:num”]
  val thms = map renamer thms
  val _ = add_code_abbrev [arm_alloc_code,arm_equal_code]
  val _ = add_compiled thms
  in () end;

val _ = let
  val thms = DB.match [] ``SPEC PPC_MODEL``
  val thms = filter (can (find_term (can (match_term ``pLISP``))) o concl)
                    (map (#1 o #2) thms)
  val renamer = Q.INST [‘x1’|->‘exp’,‘x2’|->‘x’,‘x3’|->‘y’,‘x4’|->‘z’,
                        ‘x5’|->‘stack’,‘x6’|->‘alist’] o
                INST [“limit:num”|->“l:num”]
  val thms = map renamer thms
  val _ = add_code_abbrev [ppc_alloc_code,ppc_equal_code]
  val _ = add_compiled thms
  in () end;

val _ = let
  val thms = DB.match [] ``SPEC X86_MODEL``
  val thms = filter (can (find_term (can (match_term ``xLISP``))) o concl)
                    (map (#1 o #2) thms)
  val renamer = Q.INST [‘x1’|->‘exp’,‘x2’|->‘x’,‘x3’|->‘y’,‘x4’|->‘z’,
                        ‘x5’|->‘stack’,‘x6’|->‘alist’] o
                INST [“limit:num”|->“l:num”,
                      mk_var("eip",“:word32”) |-> mk_var("p",“:word32”)]
  val thms = map renamer thms
  val _ = add_code_abbrev [x86_alloc_code,x86_equal_code]
  val _ = add_compiled thms
  in () end;

(*
  val _ = print_compiler_grammar()
*)

val STATE = ``(exp:SExp,x:SExp,y:SExp,z:SExp,stack:SExp,alist:SExp,l:num)``


val (thms,_,_) = compile_all ``
 (lookup_aux ^STATE =
    let x = CAR y in
    let x = CAR x in
      if exp = x then
        let x = CAR y in
        let exp = CDR x in
          ^STATE
      else
        let y = CDR y in
          lookup_aux ^STATE)
  /\
 (lisp_lookup ^STATE =
    let y = alist in
    let (exp,x,y,z,stack,alist,l) = lookup_aux ^STATE in
      ^STATE)
 /\
 (zip_yz ^STATE =
    if isDot y then
      let alist = exp in
      let exp = CAR y in
      let x = CAR z in
      let exp = Dot exp x in
      let x = alist in
      let exp = Dot exp x in
      let y = CDR y in
      let z = CDR z in
        zip_yz ^STATE
    else
      ^STATE)
  /\
 (lisp_length ^STATE =
    if isDot x then
      let exp = LISP_ADD exp (Val 1) in
      let x = CDR x in
        lisp_length ^STATE
    else
      ^STATE)
  /\
 (lisp_symbolp ^STATE =
    if isSym exp
    then let exp = Sym "t" in ^STATE
    else let exp = Sym "nil" in ^STATE)
  /\
 (lisp_consp ^STATE =
    if isDot exp
    then let exp = Sym "t" in ^STATE
    else let exp = Sym "nil" in ^STATE)
  /\
 (lisp_less ^STATE =
    if getVal exp < getVal x
    then let exp = Sym "t" in ^STATE
    else let exp = Sym "nil" in ^STATE)
  /\
 (lisp_atomp ^STATE =
    if isDot exp
    then let exp = Sym "nil" in ^STATE
    else let exp = Sym "t" in ^STATE)
  /\
 (lisp_numberp ^STATE =
    if isDot exp
    then let exp = Sym "nil" in ^STATE
    else if isSym exp
    then let exp = Sym "nil" in ^STATE
    else let exp = Sym "t" in ^STATE)
  /\
 (lisp_add ^STATE =
    if isDot y then
      let x = CAR y in
      let y = CDR y in
      let exp = LISP_ADD exp x in
        lisp_add ^STATE
    else
      ^STATE)
  /\
 (lisp_mult ^STATE =
    if isDot z then
      let x = CAR z in
      let z = CDR z in
      let (exp,x,y) = (LISP_MULT exp x,Sym "nil",Sym "nil") in
        lisp_mult ^STATE
    else
      ^STATE)
  /\
 (lisp_find_in_list ^STATE =
    if ~(isDot y) then let exp = Sym "nil" in ^STATE else
      let x = CAR y in
        if exp = x then let exp = Sym "t" in ^STATE else
          let y = CDR y in
            lisp_find_in_list ^STATE)
  /\
 (lisp_reduce_alist_aux ^STATE =
    if (z = Val 0) then ^STATE else
    if ~isDot alist then ^STATE else
      let exp = CAR alist in
      let exp = CAR exp in
      let y = CAR stack in
      let (exp,x,y,z,stack,alist,l) = lisp_find_in_list ^STATE in
        if exp = Sym "nil" then ^STATE else
          let z = LISP_SUB z (Val 1) in
          let alist = CDR alist in
            lisp_reduce_alist_aux ^STATE)
  /\
 (lisp_reduce_alist ^STATE =
    if isDot stack then
      let z = CAR stack in
        if isDot z then ^STATE else
        if isSym z then ^STATE else
          let x = CDR stack in
          let exp = Dot exp x in
          let x = y in
          let y = CAR y in
          let exp = Dot exp x in
          let x = exp in
          let exp = y in
          let exp = Dot exp x in
          let stack = exp in
          let (exp,x,y,z,stack,alist,l) = lisp_reduce_alist_aux ^STATE in
          let stack = CDR stack in
          let y = CDR stack in
          let stack = CAR stack in
          let exp = CAR stack in
          let stack = CDR stack in
            if z = Val 0 then ^STATE else
              let x = z in
              let z = exp in
              let exp = x in
              let x = stack in
              let exp = Dot exp x in
              let stack = exp in
              let exp = z in
                ^STATE
    else ^STATE)
  /\
 (lisp_func ^STATE =
    if isDot x then
      let y = CDR x in
      let x = CAR x in
        if x = Sym "lambda" then
          let x = CAR y in
          let (exp,x,y,z,stack,alist,l) = lisp_reduce_alist ^STATE in
          let z = exp in      (* z hold evaluated args   *)
          let x = exp in
          let exp = Val 0 in
          let (exp,x,y,z,stack,alist,l) = lisp_length ^STATE in
          let x = stack in
          let exp = Dot exp x in
          let x = exp in
          let exp = CDR y in  (* exp := body of lambda *)
          let exp = Dot exp x in
          let stack = exp in
          let y = CAR y in    (* y := parameter names  *)
          let exp = alist in
          let x = y in
          let (exp,x,y,z,stack,alist,l) = zip_yz ^STATE in
          let alist = exp in
          let exp = CAR stack in
          let stack = CDR stack in
          let exp = CAR exp in
          let z = TASK_EVAL in
            ^STATE
        else (* if x = Sym "label" *)
          let z = exp in
          let exp = Val 1 in
          let x = stack in
          let exp = Dot exp x in
          let stack = exp in
          let x = CDR y in
          let exp = CAR y in
          let x = CAR x in
          let exp = Dot exp x in
          let x = alist in
          let exp = Dot exp x in
          let x = CDR y in
          let alist = exp in
          let exp = z in
          let x = CAR x in
          let z = TASK_FUNC in
            lisp_func ^STATE
    else (* x must be a symbol *)
      let z = TASK_CONT in
        if x = Sym "car" then
          let exp = CAR exp in
          let exp = CAR exp in
            ^STATE
        else if x = Sym "cdr" then
          let exp = CAR exp in
          let exp = CDR exp in
            ^STATE
        else if x = Sym "cons" then
          let x = CDR exp in
          let exp = CAR exp in
          let x = CAR x in
          let exp = Dot exp x in
            ^STATE
        else if x = Sym "+" then
          let y = exp in
          let exp = Val 0 in
          let (exp,x,y,z,stack,alist,l) = lisp_add ^STATE in
            ^STATE
        else if (x = Sym "-") then
          let x = CDR exp in
          let exp = CAR exp in
          let x = CAR x in
          let exp = LISP_SUB exp x in
            ^STATE
        else if (x = Sym "*") then
          let z = exp in
          let exp = Val 1 in
          let (exp,x,y,z,stack,alist,l) = lisp_mult ^STATE in
          let z = TASK_CONT in
            ^STATE
        else if (x = Sym "div") then
          let x = CDR exp in
          let exp = CAR exp in
          let x = CAR x in
          let (exp,x,y) = (LISP_DIV exp x,Sym "nil",Sym "nil") in
            ^STATE
        else if (x = Sym "mod") then
          let x = CDR exp in
          let exp = CAR exp in
          let x = CAR x in
          let (exp,x,y) = (LISP_MOD exp x,Sym "nil",Sym "nil") in
            ^STATE
        else if (x = Sym "<") then
          let x = CDR exp in
          let exp = CAR exp in
          let x = CAR x in
          let (exp,x,y,z,stack,alist,l) = lisp_less ^STATE in
            ^STATE
        else if (x = Sym "atomp") then
          let exp = CAR exp in
          let (exp,x,y,z,stack,alist,l) = lisp_atomp ^STATE in
            ^STATE
        else if (x = Sym "consp") then
          let exp = CAR exp in
          let (exp,x,y,z,stack,alist,l) = lisp_consp ^STATE in
            ^STATE
        else if (x = Sym "numberp") then
          let exp = CAR exp in
          let (exp,x,y,z,stack,alist,l) = lisp_numberp ^STATE in
            ^STATE
        else if (x = Sym "symbolp") then
          let exp = CAR exp in
          let (exp,x,y,z,stack,alist,l) = lisp_symbolp ^STATE in
            ^STATE
        else if (x = Sym "equal") then
          let x = CDR exp in
          let exp = CAR exp in
          let x = CAR x in
          let exp = LISP_EQUAL exp x in
            ^STATE
        else (* if none of the above, then lookup in alist and repeat *)
          let z = exp in
          let exp = x in
          let (exp,x,y,z,stack,alist,l) = lisp_lookup ^STATE in
          let x = exp in
          let exp = z in
          let z = TASK_FUNC in
            lisp_func ^STATE)
  /\
 (rev_exp ^STATE =
    if isDot z then
      let x = exp in
      let exp = CAR z in
      let exp = Dot exp x in
      let z = CDR z in
        rev_exp ^STATE
    else
      let x = y in
        ^STATE)
  /\
 (reverse_exp (exp,x,y,z:SExp,stack,alist,l) =
    let z = exp in
    let exp = Sym "nil" in
    let (exp,x,y,z,stack,alist,l) = rev_exp ^STATE in
    let z = TASK_FUNC in
      ^STATE)
  /\
 (repeat_cdr ^STATE =
    if x = Val 0 then ^STATE else
      let alist = CDR alist in
      let x = LISP_SUB x (Val 1) in
        repeat_cdr ^STATE)
  /\
 (lisp_cont ^STATE =
    let x = CAR stack in
    let stack = CDR stack in
      if ~isDot x then (* drop elements from alist *)
        let (exp,x,y,z,stack,alist,l) = repeat_cdr ^STATE in
          ^STATE
      else
        let z = x in
        let x = CAR stack in
          if x = Sym "cond" then (* deal with conditional *)
            let stack = CDR stack in
              if exp = Sym "nil" then (* guard is false *)
                let exp = x in
                let x = CDR z in
                let exp = Dot exp x in
                let z = TASK_EVAL in
                  ^STATE
              else (* guard is true *)
                let exp = CAR z in
                let exp = CDR exp in
                let exp = CAR exp in
                let z = TASK_EVAL in
                  ^STATE
          else
            let y = CAR z in (* list of unevaluated args *)
            let x = CDR z in (* list of evaluated args *)
              if isDot y then (* still args to evaluate *)
                let z = CAR y in
                let exp = Dot exp x in
                let x = exp in
                let exp = CDR y in
                let exp = Dot exp x in
                let x = stack in
                let exp = Dot exp x in
                let stack = exp in
                let exp = z in
                let z = TASK_EVAL in
                  ^STATE
              else
                let y = CAR stack in
                let stack = CDR stack in
                let exp = Dot exp x in
                let (exp,x,y,z,stack,alist,l) = reverse_exp ^STATE in
                  ^STATE)
  /\
 (lisp_app ^STATE =
    if x = Sym "quote" then
      let exp = CAR exp in
        ^STATE
    else if x = Sym "cond" then
      if isDot exp then
        let z = exp in
        let exp = x in
        let x = stack in
        let exp = Dot exp x in
        let x = exp in
        let exp = z in
        let exp = Dot exp x in
        let stack = exp in
        let exp = CAR z in
        let exp = CAR exp in
        let z = TASK_EVAL in
          ^STATE
      else
        ^STATE
    else (* normal function: push function onto stack, push args onto stack *)
      if isDot exp then (* there is at least one arg *)
        let y = CAR exp in
        let z = CDR exp in
        let exp = x in
        let x = stack in
        let exp = Dot exp x in
        let stack = exp in
        let exp = z in
        let x = Sym "nil" in
        let exp = Dot exp x in
        let x = stack in
        let exp = Dot exp x in
        let stack = exp in
        let exp = y in
        let z = TASK_EVAL in
          ^STATE
      else (* there are no args *)
        let z = TASK_FUNC in
          ^STATE)
  /\
 (lisp_eval ^STATE =
    if z = TASK_EVAL then
      let z = TASK_CONT in
      if isSym exp then (* exp is Sym *)
        let (exp,x,y,z,stack,alist,l) = lisp_lookup ^STATE in
          lisp_eval ^STATE
      else if isDot exp then (* exp is Dot *)
        let x = CAR exp in
        let exp = CDR exp in
        let (exp,x,y,z,stack,alist,l) = lisp_app ^STATE in
            lisp_eval ^STATE
      else (* exp is Num *)
        lisp_eval ^STATE
    else if z = TASK_FUNC then (* function=x, args stored as list in exp *)
      let (exp,x,y,z,stack,alist,l) = lisp_func ^STATE in
        lisp_eval ^STATE
    else (* if z = TASK_CONT then *)
      if isDot stack then (* something is still on the to-do list *)
        let (exp,x,y,z,stack,alist,l) = lisp_cont ^STATE in
          lisp_eval ^STATE
      else (* something is still on the to-do list *)
        ^STATE)``;

val _ = map (fn (name,th) =>
  save_thm("SPEC_lisp_eval_" ^ name ^ "_thm",th)) thms

val _ = export_theory();

