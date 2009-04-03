structure codegenLib :> codegenLib =
struct

open HolKernel boolLib bossLib Parse decompilerLib;
open codegen_inputLib helperLib;

(* -- target-specific part begins -- *)

open codegen_armLib codegen_x86Lib codegen_ppcLib;

fun assembler_tools target = 
  if target = "arm" then (arm_encode_instruction, arm_encode_branch) else 
  if target = "x86" then (x86_encode_instruction, x86_encode_branch) else 
  if target = "ppc" then (ppc_encode_instruction, ppc_encode_branch) else hd []

fun conditional_tools target = 
  if target = "arm" then (arm_cond_code, arm_conditionalise, arm_remove_annotations) else 
  if target = "x86" then (x86_cond_code, x86_conditionalise, x86_remove_annotations) else 
  if target = "ppc" then (ppc_cond_code, ppc_conditionalise, ppc_remove_annotations) else hd []

fun generator_tools target = 
  if target = "arm" then (arm_assign2assembly, arm_guard2assembly) else 
  if target = "x86" then (x86_assign2assembly, x86_guard2assembly) else 
  if target = "ppc" then (ppc_assign2assembly, ppc_guard2assembly) else hd []

(* -- target-specific part ends -- *)





(* data-type used inside the code generator *)

datatype asm_type = 
    ASM_ASSIGN of term * term (* lhs, rhs *)
  | ASM_BRANCH of string option * string (* condition option, label name *)
  | ASM_COMPARE of term (* e.g. ``r1 = r2`` *)
  | ASM_INSERT of string * int * (string * string) option 
      (* name in !decompiler_memory, code length, option comparsion result code (true,false) *)
  | ASM_INSTRUCTION of string * string * (string * string) option 
      (* concrete instruction, option comparsion result code (true,false) *)
  | ASM_LABEL of string (* label name *);



(* assembler *)

fun list_append [] = [] | list_append (x::xs) = x @ list_append xs

fun basic_assembler target code3 = let
  val (enc,branch) = assembler_tools target 
  (* translate into machine code *)
  fun extend (s,i) = if size s < 2 * i then extend ("0" ^ s, i) else s
  fun translate (ASM_INSTRUCTION (x,z,y),q) = 
        if x = "" then (ASM_INSTRUCTION (x,z,y),q)
        else (ASM_INSTRUCTION (extend (enc x),z,y),q)
    | translate x = x
  val code4 = map translate code3
  (* replace gotos, first with nothing, then regenerate iteratively until no change *)
  fun dummy_jumps x = (x,"")
  fun jump_length label (((ASM_INSERT (x,y,_),_) ,_)::xs) = y + jump_length label xs
    | jump_length label (((ASM_INSTRUCTION (x,_,_),_) ,_)::xs) = (size(x) div 2) + jump_length label xs
    | jump_length label (((ASM_BRANCH (_,_),_) ,x)::xs) = (size(x) div 2) + jump_length label xs
    | jump_length label (((ASM_LABEL label2,_) ,_)::xs) = if label = label2 then 0 else jump_length label xs
    | jump_length label _ = hd []
  fun generate_jumps xs [] = rev xs
    | generate_jumps xs (((ASM_BRANCH (c,label),s),_) :: ys) = let 
        val jump = branch false (jump_length label xs) c handle e =>
                   branch true  (jump_length label ys) c
        in generate_jumps (((ASM_BRANCH (c,label),s), extend jump) :: xs) ys end
    | generate_jumps xs (y::ys) = generate_jumps (y :: xs) ys
  fun gencode_for_jumps code = generate_jumps [] code 
  fun find_fixpoint f x = let val y = f x in if x = y then x else find_fixpoint f y end
  val code5 = find_fixpoint gencode_for_jumps (map dummy_jumps code4)
  (* pull out the generated machine code *)
  fun get_code ((ASM_INSTRUCTION (x,z,_),s),_) = [(x^z,s)] 
    | get_code ((ASM_INSERT (x,_,_),s),_) = [("insert:"^x,SOME "")]
    | get_code ((ASM_BRANCH (_,_),s),x) = [(x,s)]
    | get_code _ = []
  val code6 = list_append (map get_code code5) 
  fun ff (x,NONE) = (x,"") | ff (x,SOME y) = (x,y) 
  val code7 = map ff code6
  val result = filter (fn x => not (x = "")) (map fst code6)
  val len = jump_length "::" (code5 @ [((ASM_LABEL "::",NONE),"")])
  val result = list_append (map (String.tokens (fn x => x = #" ")) result)
  in (result,len,code7) end

fun quote_to_strings q = let (* turns a quote `...` into a list of strings *)
  fun get_QUOTE (QUOTE t) = t | get_QUOTE _ = hd []
  val xs = explode (get_QUOTE (hd q))
  fun strip_comments l [] = []
    | strip_comments l (x::xs) =
        if x = #"(" then strip_comments (l+1) xs else
        if x = #")" then strip_comments (l-1) xs else
        if 0 < l    then strip_comments l xs else x :: strip_comments l xs
  fun strip_space [] = []
    | strip_space (x::xs) = 
        if mem x [#" ",#"\t",#"\n"] then strip_space xs else x::xs
  fun lines [] [] = [] 
    | lines xs [] = [implode ((rev (strip_space xs)))]
    | lines xs (y::ys) = 
        if mem y [#"\n",#"|"] 
        then implode ((rev (strip_space xs))) :: lines [] ys 
        else lines (y::xs) ys   
  fun delete_empty (""::xs) = delete_empty xs
    | delete_empty xs = xs
  val ys = (strip_comments 0) xs
  in (rev o delete_empty o rev o delete_empty o lines []) ys end;  

fun assemble target code = let
  fun replace_char c str = 
    String.translate (fn x => if x = c then str else implode [x]);
  fun f s = (String.fields (fn x => x = #":") s,s)
  val ys = map f (quote_to_strings code)
  fun space s = replace_char #" " "" s
  fun process ([],s) = hd []
    | process ([x],s) = 
       if (String.substring(x,0,6) = "insert" handle e => false) then
         [(ASM_INSERT(space(String.substring(x,6,size(x)-6)),0,NONE),SOME s)]
       else [(ASM_INSTRUCTION (x,"",NONE),SOME s)]
    | process ((y::x::xs),s) = (ASM_LABEL (space y),NONE) :: process ((x::xs),s)
  val ys = map process ys
  fun spaces [] = 0 | spaces (x::xs) = if x = #" " then 1 + spaces xs else 0
  fun max [] = hd []
    | max [x] = x
    | max (x::y::xs) = let val m = max (y::xs) in if x < m then m else x end
  fun get_spaces NONE = 0 | get_spaces (SOME x) = spaces (explode x)
  val m = max (map (get_spaces o snd o last) ys)
  fun repeatc n c = if n = 0 then [] else c :: repeatc (n-1) c 
  val str = implode (repeatc m #" ")
  fun option_concat s NONE = NONE
    | option_concat s (SOME t) = SOME (t ^ s)
  val ys = list_append ys
  val zs = map (fn (x,y) => (x, option_concat str y)) ys
  fun labels (ASM_LABEL l) = [l] | labels _ = [] 
  val ls = list_append (map (labels o fst) zs)
  fun create_branch x = let
    val ts = String.tokens (fn x => mem x [#" ",#","]) x  
    val _ = if mem (last ts) ls then () else hd []
    in ASM_BRANCH (SOME (hd ts),last ts) end
  fun foo (ASM_INSTRUCTION (x,y,z),s) = ((create_branch x handle _ => ASM_INSTRUCTION (x,y,z)),s)
    | foo qq = qq
  val qs = map foo zs
  fun h (SOME x) = [x] | h _ = [] 
  val n = max (map size (list_append (map (h o snd) qs)))
  fun hh (x,NONE) = (x,NONE) | hh (x,SOME s) = (x, SOME ("(* " ^ s ^ implode (repeatc (n - size(s)) #" ") ^ " *)"))
  val code3 = map hh qs
  val (result,_,xs) = basic_assembler target code3
  val m = max (map (size o fst) xs)
  val ys = map (fn (s,v) => "  " ^ s ^ implode (repeatc (m - size(s)) #" ") ^ "    " ^ v ^ "\n") xs
  val _ = print "\n\n"
  val _ = map print ys
  val _ = print "\n\n"
  in result end  

(*

val _ = assemble "arm" `
      b G
  L:  mul r2,r1,r2
      beq G
      subs r1,r1,#1
      bne L
  G:  add r1,r2,r1`;

val _ = assemble "ppc" `
        b G
L:      add 2,1,2
        beq G
        addi 1,1,-1
        bne L
G:      add 1,2,1`;

val _ = assemble "x86" `
        jmp G
L:      add eax,ebx
        je G
        inc ebx
        jne L
G:      xor eax, 5`;

val _ = assemble "x86" 
val target = "x86"
val code = `
        je G
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
        xor eax, 5000
G:      xor eax, 5000`;

*)


(* methods for loading in theorems for use in compilation *)

val compiler_assignments = ref ([]: (term * term * int * string * string) list);
val compiler_conditionals = ref ([]: (term * term * int * string * string) list);

fun add_compiler_assignment tm1 tm2 name len model_name = 
  (compiler_assignments := (tm1,tm2,len,name,model_name) :: (!compiler_assignments));  

fun print_compiler_grammar () = let
  val xs = !compiler_assignments
  fun f (x,y,_,_,m) = "  " ^ m ^ ":  let "^(term_to_string x)^" = "^(term_to_string y)^" in _\n"
  val assign = map f xs  
  val xs = !compiler_conditionals
  fun f (x,_,_,_,m) = "  " ^ m ^ ":  if "^(term_to_string (repeat dest_neg x))^" then _ else _\n"
  val cond = map f xs  
  val sorter = sort (curry (fn (x:string,y:string) => x <= y))
  val _ = print "\nAssignments:\n\n"
  val _ = map print (sorter assign)
  val _ = print "\nConditionals:\n\n"
  val _ = map print (sorter cond)
  val _ = print "\n"  
  in () end;

fun get_model_name th = let
  val (m,_,_,_) = (dest_spec o concl o UNDISCH_ALL o SPEC_ALL) th
  in fst (dest_const m) end;

fun get_tools th = let
  val s = get_model_name th
  in if s = "PPC_MODEL" then prog_ppcLib.ppc_tools else
     if s = "X86_MODEL" then prog_x86Lib.x86_tools else
     if s = "ARM_MODEL" then prog_armLib.arm_tools else hd [] end

fun add_assignment (tm1,tm2,th,len) = let
  val (_,_,_,pc) = get_tools th
  val th = RW [GSYM progTheory.SPEC_MOVE_COND] (DISCH_ALL th)
  val thx = CONV_RULE (PRE_CONV (SIMP_CONV (std_ss++sep_cond_ss) [])) th
  val thx = UNDISCH_ALL (RW [progTheory.SPEC_MOVE_COND] thx)
  val (m,p,_,q) = (dest_spec o concl o SPEC_ALL) thx
  val m = get_model_name thx
  val name = ("AUTO_"^m^"_ASSIGN_"^(int_to_string (length (!compiler_assignments))))
  val _ = (compiler_assignments := (tm1,tm2,len,name,m) :: (!compiler_assignments))
  val dest_tuple = list_dest pairSyntax.dest_pair
  val ys = zip (dest_tuple tm1) (dest_tuple tm2) handle e => [(tm1,tm2)]
  val ys = filter (fn (x,y) => not (x = y)) ys
  val post = cdr (find_term (can (match_term (mk_comb(pc,genvar(``:word32``))))) q)
  val tm2 = subst [mk_var("p",``:word32``) |-> post] p
  val vs = pairSyntax.list_mk_pair (map fst ys)
  val ws = pairSyntax.list_mk_pair (map snd ys)
  val tm3 = pairSyntax.mk_anylet([(vs,ws)],tm2)
  val lemma = prove(mk_eq(q,tm3),
    SPEC_TAC (ws,genvar(type_of ws))
    THEN SIMP_TAC std_ss [pairTheory.FORALL_PROD,LET_DEF]
    THEN (fn x => hd [])) handle e => TRUTH
  val th = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [lemma])) th
  val _ = add_decompiled (name,th,len,SOME len)
  in () end;

fun add_conditional (tm1,tm2,th,len) = let
  val th = RW [GSYM progTheory.SPEC_MOVE_COND] (DISCH_ALL th)
  val m = get_model_name th
  val name = ("AUTO_"^m^"_COND_"^(int_to_string (length (!compiler_conditionals))))
  val _ = (compiler_conditionals := (tm1,tm2,len,name,m) :: (!compiler_conditionals))
  val _ = add_decompiled (name,th,len,SOME len)
  in () end;

fun extract_ops th = let
  val tools = (get_tools th)
  val (_,_,th1,pc) = tools
  val (x,y) = dest_eq (concl th1)
  val xs = list_dest dest_star x @ list_dest dest_star y
  val xs = map (fn x => dest_sep_hide x handle e => x) xs
  val th = UNDISCH_ALL (SIMP_RULE (std_ss++sep_cond_ss) [progTheory.SPEC_MOVE_COND] th)
  val (m,p,c,q) = dest_spec (concl th)
  val (i,q) = pairSyntax.dest_anylet q handle HOL_ERR _ => ([],q)
  val ps = list_dest dest_star p
  val qs = list_dest dest_star q
  (* length of instruction *)
  val l = (numSyntax.int_of_term o cdr o cdr o cdr o hd) (filter (fn tm => car tm = pc) qs)
  (* calculate update *)
  fun sep_domain tm = dest_sep_hide tm handle _ => car tm
  val ps' = filter (fn tm => not (mem (sep_domain tm) (pc::xs))) ps
  val qs' = filter (fn tm => not (mem (sep_domain tm) (pc::xs))) qs
  fun foo tm [] = hd []
    | foo tm (x::xs) = if sep_domain x = tm then x else foo tm xs  
  val zs = map (fn tm => (cdr tm,cdr (foo (sep_domain tm) qs'))) ps'
  val (tm1,tm2) = hd zs 
  fun goo (tm1,tm2) = let
    val i = fst (match_term tm1 tm2)
    val ys = list_dest pairSyntax.dest_pair tm1
    in zip ys (map (subst i) ys) end
  val ys = foldr (uncurry append) [] (map goo zs) handle e => []
  val ys = filter (fn (t1,t2) => not (t1 = t2)) ys
  val tm1 = pairSyntax.list_mk_pair(map fst ys) handle HOL_ERR e => ``()``
  val tm2 = pairSyntax.list_mk_pair(map snd ys) handle HOL_ERR e => ``()``
  val ((tm1,tm2),ys) = if length i = 0 then ((tm1,tm2),ys) else (hd i,i)
  val len = l
  (* store thm *)
  val _ = if length ys = 0 then () else add_assignment (tm1,tm2,th,l)
  (* possible tests *)
  fun foo tm = optionLib.dest_some tm handle e => tm
  val qs = filter (fn tm => mem (car tm) xs) qs
  val qs = map (fn tm => add_conditional(foo (cdr tm),car tm,th,l)) qs
  in () end;  

fun add_compiled thms = let val _ = map extract_ops thms in () end;

(* code generator *)

fun print_asm code = let
  fun print_cond NONE = ""
    | print_cond (SOME s) = ", if " ^ s
  fun print_cmp NONE = ""
    | print_cmp (SOME (t,f)) = "  ["^t^"|"^f^"]"
  fun print_inst (ASM_ASSIGN (t1,t2)) = 
        "     " ^ term_to_string t1 ^ " := " ^ term_to_string t2
    | print_inst (ASM_BRANCH (c,name)) = 
        "     goto " ^ name ^ print_cond c
    | print_inst (ASM_COMPARE tm) = 
        "     compare " ^ term_to_string tm
    | print_inst (ASM_INSERT (s,i,cmp)) = 
        "     insert '" ^ s ^ "' " ^ int_to_string i ^ print_cmp cmp
    | print_inst (ASM_INSTRUCTION (s,_,cmp)) = 
        "     " ^ s ^ print_cmp cmp
    | print_inst (ASM_LABEL s) = 
        s ^ ":"
  in print "\n\n" ; map (fn s => print (print_inst s ^ "\n")) code ; print "\n\n" end

fun generate_code target model_name print_assembly tm = let
  val (assign2assembly, guard2assembly) = generator_tools target
  val (cond_code, conditionalise, remove_annotations) = conditional_tools target
  (* fold constants *)
  val tm = (cdr o concl o EVAL_ANY_MATCH_CONV word_patterns) tm handle e => tm
  (* generate abstract code *)
  val l = ref 0;
  fun label_name () = let val _ = l := !l + 1 in "L" ^ (int_to_string (!l)) end
  val top_label = label_name()
  fun shared_tail xs ys = let
    fun aux [] ys zs = ([],rev ys,zs)
      | aux xs [] zs = (rev xs,[],zs)
      | aux (x::xs) (y::ys) zs = 
          if x = y then aux xs ys (x::zs) else (rev (x::xs), rev (y::ys), zs)
    in aux (rev xs) (rev ys) [] end
  fun compile (FUN_VAL tm) = 
       if not (pairSyntax.is_pair tm) andalso is_comb tm then [ASM_BRANCH (NONE,top_label)] else []
    | compile (FUN_COND _) = raise (mk_HOL_ERR "compilerLib" "compile" "Structure not supported.")
    | compile (FUN_LET (tm1,tm2,t)) = 
       [ ASM_ASSIGN (tm1,tm2) ] @ compile t
    | compile (FUN_IF (tm,t1,t2)) = 
       if is_neg tm then compile (FUN_IF (dest_neg tm,t2,t1)) else let
         val rest1 = compile t1 
         val rest2 = compile t2
         val label1 = label_name() 
         val (rest1,rest2,rest3) = shared_tail rest1 rest2
         val (rest1,rest2,rest3) = 
           if rest3 = [ASM_BRANCH (NONE,top_label)] 
           then (rest1 @ rest3, rest2 @ rest3,[]) else (rest1, rest2, rest3)
         in if rest1 = [] then 
              [ASM_COMPARE tm, ASM_BRANCH (SOME "true",label1)] @ rest2 @ [ASM_LABEL label1] @ rest3
            else if rest2 = [] then
              [ASM_COMPARE tm, ASM_BRANCH (SOME "false",label1)] @ rest1 @ [ASM_LABEL label1] @ rest3
            else if rest1 = [ASM_BRANCH (NONE,top_label)] then
              [ASM_COMPARE tm, ASM_BRANCH (SOME "true",top_label)] @ rest2 @ rest3
            else if rest2 = [ASM_BRANCH (NONE,top_label)] then
              [ASM_COMPARE tm, ASM_BRANCH (SOME "false",top_label)] @ rest1 @ rest3
            else if last rest1 = ASM_BRANCH (NONE,top_label) then
              [ASM_COMPARE tm, ASM_BRANCH (SOME "false",label1)] @ rest1 @ [ASM_LABEL label1] @ rest2 @ rest3
            else if last rest2 = ASM_BRANCH (NONE,top_label) then
              [ASM_COMPARE tm, ASM_BRANCH (SOME "true",label1)] @ rest2 @ [ASM_LABEL label1] @ rest1 @ rest3
            else let val label2 = label_name() in
              if length rest2 < length rest1 then
                [ASM_COMPARE tm, ASM_BRANCH (SOME "true",label1)] @ rest2 @ [ASM_BRANCH (NONE,label2)] @
                [ASM_LABEL label1] @ rest1 @ [ASM_LABEL label2] @ rest3 
              else
                [ASM_COMPARE tm, ASM_BRANCH (SOME "false",label1)] @ rest1 @ [ASM_BRANCH (NONE,label2)] @
                [ASM_LABEL label1] @ rest2 @ [ASM_LABEL label2] @ rest3 
            end end
  val x = fst (dest_eq tm)
  val t = tm2ftree (snd (dest_eq tm))
  (* remove dead code *)
  fun rem (FUN_VAL tm) = FUN_VAL tm
    | rem (FUN_COND x) = FUN_COND x
    | rem (FUN_IF (tm,t1,t2)) = FUN_IF (tm,rem t1,rem t2)
    | rem (FUN_LET (tm1,tm2,t)) = let
    val t = rem t
    val vs = free_vars tm1
    val ws = free_vars (ftree2tm t)
    in if filter (fn x => mem x ws) vs = [] then t else FUN_LET (tm1,tm2,t) end
  val t = rem t
  (* compile *)
  val name = fst (dest_const (repeat car x)) handle e => fst (dest_var (repeat car x))
  val code1 = [ASM_LABEL top_label] @ compile t
  (* do basic instruction reorderings here *)
  (* ... *)
  (* look up assembly instructions for assignments and comparisions *)
  fun find_assignment (tm1,tm2) [] = hd []
    | find_assignment (tm1,tm2) ((x,y,l,n,m)::xs) = 
        if (tm1 = x) andalso (tm2 = y) andalso (m = model_name)
        then (n,l) else find_assignment (tm1,tm2) xs
  fun find_compiled_assignment (tm1,tm2) = find_assignment (tm1,tm2) (!compiler_assignments)
  fun find_conditional tm [] = hd []
    | find_conditional tm ((x,y,l,n,m)::xs) = 
        if ((tm = x) orelse (mk_neg tm = x)) andalso (m = model_name) 
        then (x,y,l,n) else find_conditional tm xs
  fun find_compiled_conditional tm = find_conditional tm (!compiler_conditionals)
  val to_x86 = subst (to_x86_regs())
  fun compile_inst1 (ASM_ASSIGN (t1,t2)) = let
        val (s,i) = find_compiled_assignment (t1,t2) handle Empty =>
                    find_compiled_assignment (to_x86 t1,to_x86 t2)
        in [ASM_INSERT (s,i,NONE)] end
    | compile_inst1 (ASM_COMPARE tm) = let
        val (t1,t2,i,s) = find_compiled_conditional tm handle Empty =>
                          find_compiled_conditional (to_x86 tm)
        val (t,f) = cond_code t2
        val (t,f) = if is_neg t1 then (f,t) else (t,f)
        in [ASM_INSERT (s,i,SOME (t,f))] end
    | compile_inst1 x = hd []
  fun func_name_annotations t1 t2 = let
    val vs = free_vars t1 @ free_vars t2
    val v = hd (filter (fn v => (type_of v = ``:word32 -> word32``)
                                orelse 
                                (type_of v = ``:word32 -> word8``)) vs)
    in "/" ^ fst (dest_var v) end handle Empty => ""
  fun compile_inst2 (ASM_ASSIGN (t1,t2)) = ((let
        val code = assign2assembly (term2assign t1 t2)
        val s = func_name_annotations t1 t2
        in map (fn x => ASM_INSTRUCTION (x,s,NONE)) code end) handle e => (let val _ = print_term t2 in hd [] end))
    | compile_inst2 (ASM_COMPARE tm) = ((let
        val (code,y) = guard2assembly (term2guard tm)
        val s = func_name_annotations tm T
        in map (fn x => ASM_INSTRUCTION (x,s,SOME y)) code end) handle e => (let val _ = print_term tm in hd [] end))
    | compile_inst2 x = [x]
  fun append_list [] = [] | append_list (x::xs) = x @ append_list xs
  val code2 = append_list (map (fn x => compile_inst1 x handle Empty => compile_inst2 x) code1)
  (* try to produce conditional execution *)
  fun bool2str c = if c then "true" else "false"
  fun conditionally_execute code u (t,f) label = let
    fun find_label [] head  = hd []
      | find_label (x::xs) head =
          if x = ASM_LABEL label then (head,xs) else find_label xs (head @ [x])
    val (code,rest) = find_label code []
    val condition = if u then f else t
    fun force_condition (ASM_INSTRUCTION (c,x,h)) = ASM_INSTRUCTION (conditionalise c condition,x,h)
      | force_condition (ASM_BRANCH (NONE, l2)) = ASM_BRANCH (SOME (bool2str (not u)), l2)
      | force_condition _ = hd []
    in map force_condition code @ rest end
  fun conditionalise [] (t,f) = []
    | conditionalise ((ASM_BRANCH (SOME u,label))::xs) (t,f) = 
        (conditionalise (conditionally_execute xs (u = "true") (t,f) label) (t,f) handle e =>
          (ASM_BRANCH (SOME u,label)) :: conditionalise xs (t,f))
    | conditionalise ((ASM_INSTRUCTION (x,y,SOME cond))::xs) (t,f) = 
        (ASM_INSTRUCTION (x,y,SOME cond)) :: conditionalise xs cond
    | conditionalise ((ASM_INSERT (x,y,SOME cond))::xs) (t,f) = 
        (ASM_INSERT (x,y,SOME cond)) :: conditionalise xs cond
    | conditionalise (zzz::xs) (t,f) = zzz :: conditionalise xs (t,f)
  val code3 = conditionalise code2 ("","")
  (* assign proper branch conditions *)
  fun update_branches [] (t,f) = []
    | update_branches ((ASM_BRANCH (SOME u,label))::xs) (t,f) = 
        (ASM_BRANCH (SOME (if u = "true" then t else (if u = "false" then f else u)),label)) :: update_branches xs (t,f)
    | update_branches ((ASM_INSTRUCTION (x,y,SOME cond))::xs) (t,f) = 
        (ASM_INSTRUCTION (x,y,NONE)) :: update_branches xs cond
    | update_branches ((ASM_INSERT (x,y,SOME cond))::xs) (t,f) = 
        (ASM_INSERT (x,y,NONE)) :: update_branches xs cond
    | update_branches (zzz::xs) (t,f) = zzz :: update_branches xs (t,f)
  val code3 = update_branches code3 ("","")  
  (* remove any annotations that were left in the assembly *)
  fun remove_extra_annotations (ASM_INSTRUCTION (x,z,y)) = ASM_INSTRUCTION (remove_annotations x,z,y)
    | remove_extra_annotations x = x
  val code3 = map remove_extra_annotations code3
  val _ = if print_assembly then print_asm code3 else ()
  (* assembler should start here *)
  val code3 = (map (fn x => (x,(NONE:string option))) code3)
  val (code6,len,_) = basic_assembler target code3
  in (code6,len) end


end;
