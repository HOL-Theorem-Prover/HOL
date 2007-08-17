structure arm_compilerLib :> arm_compilerLib =
struct

(*
  quietdec := true;
  val armDir = concat Globals.HOLDIR "/examples/ARM/v4";
  val yaccDir = concat Globals.HOLDIR "/tools/mlyacc/mlyacclib";
  loadPath := !loadPath @ [armDir,yaccDir];
*)
 
open HolKernel boolLib bossLib Parse;
open listTheory wordsTheory pred_setTheory arithmeticTheory pairTheory wordsLib;
open set_sepTheory progTheory arm_progTheory arm_instTheory set_sepLib arm_progLib;
 
(*
  quietdec := false;
*)

val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8",
                        "r9","r10","r11","r12","r13","r14","r15"];

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val EQ_IMP_IMP = METIS_PROVE [] ``(x=y) ==> x ==> y``;

fun replace_char c str = 
  String.translate (fn x => if x = c then str else implode [x]);

val code_length_rewrites = ref ([]:thm list);

fun code_length_conv () = 
  SIMP_CONV arith_ss ([LENGTH,LENGTH_APPEND] @ !code_length_rewrites);

val show_echo = ref true;
val show_proof = ref false;

fun echo st = if !Globals.interactive andalso !show_echo then print st else ();
fun print_proof st = if !Globals.interactive andalso !show_proof then print st else ();


(* ============================================================================== *)
(* STABLE CORE FUNCTIONS - these ought to be integrated with those of arm_progLib *)
(* ============================================================================== *)

fun TERMS2Q f xs = f (map (fn tm => [ANTIQUOTE tm]) xs) 
val AUTO_HIDE_PRE_TERM = TERMS2Q AUTO_HIDE_PRE
val AUTO_HIDE_POST_TERM = TERMS2Q AUTO_HIDE_POST
val AUTO_HIDE_POST1_TERM = TERMS2Q AUTO_HIDE_POST1
val MOVE_PREL_TERM = TERMS2Q MOVE_PREL
val MOVE_POSTL_TERM = TERMS2Q MOVE_POSTL
val MOVE_POST1L_TERM = TERMS2Q MOVE_POST1L

(* -- compose -- *)

val compose2_ss = simpLib.merge_ss [compose_ss,rewrites [WORD_CMP_NORMALISE]];
val RW_COMPOSE2 = SIMP_RULE (std_ss ++ compose2_ss) [];

fun MOVE_COMPOSE2 th1 th2 xs1 xs2 ys1 ys2 = let
  val th = MOVE_COMPOSE th1 th2 xs1 xs2 ys1 ys2
  val th = RW_COMPOSE2 th
  val th = CONV_RULE (code_length_conv()) th
  val th = RW_COMPOSE2 th
  in th end;

(* others *)

fun COMPILER_FORMAT_DEF th = 
  CONV_RULE (REWRITE_CONV [LET_DEF] THENC DEPTH_CONV (FORCE_PBETA_CONV)) th;

fun list_dest_forall tm = let
  val (v,x) = dest_forall tm 
  val (vs,x) = list_dest_forall x
  in (v::vs,x) end handle e => ([],tm);

fun extract_assum th = let
  val tm = (repeat (snd o dest_forall) o fst o dest_imp o concl) th
  val th = (SPEC_ALL o ASSUME o fst o dest_imp) tm
  in th end;


(* ============================================================================= *)
(* EXPERIMENTAL PROOF-PRODUCING FUNCTIONS                                        *)
(* ============================================================================= *)

(* handleing terms *)

fun TERM_CONV (conv:term->thm) = snd o dest_eq o concl o conv;
fun TERM_RW thms = TERM_CONV (QCONV (REWRITE_CONV thms));

fun get_term pat tm = find_term (can (match_term pat)) tm;

fun list_get_term pat tm = let
  val m = can (match_term pat)
  fun d mat tm = subst [mat|->genvar (type_of mat)] tm
  fun list_repeat f x g = 
    let val y = f x in y :: list_repeat f (g y x) g end handle e => []
  in list_repeat (find_term m) tm d end;


(* printing helpers *)

fun list_to_string f [] sep = ""
  | list_to_string f [x] sep = f x
  | list_to_string f (x::y::xs) sep = f x ^ sep ^ list_to_string f (y::xs) sep;

fun term_to_string_show_types tm = let
  val b = !show_types
  val _ = show_types := true
  val st = replace_char #"\n" " " (term_to_string tm) 
  val _ = show_types := b
  in st end; 

fun subst_to_string xs indent =
  let fun f {redex = x, residue = y} = 
      "`" ^ term_to_string_show_types x ^ "`|->`" ^ term_to_string_show_types y ^ "`"
  in "[" ^ list_to_string f xs "," ^ "]" end;

fun subst_to_string_no_types xs indent =
  let fun f {redex = x, residue = y} = 
      "`" ^ term_to_string x ^ "`|->`" ^ term_to_string y ^ "`"
  in "[" ^ replace_char #"\n" " " (list_to_string f xs ",") ^ "]" end;


(* make code for composing basic specs *)

(*
make_spec ["mov r0,r0","mov r0,r0"]

  val th1 = (*  mov r0,r0  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`0w`,`a_mode`|->`OneReg`,`x`|->`x1` ] arm_MOV1))
  val th2 = (*  mov r0,r0  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`0w`,`a_mode`|->`OneReg`,`x`|->`x2` ] arm_MOV1))
  val th1 = AUTO_HIDE_STATUS th1  

  val th1 = (*  ldr r1,[sp]  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`1w`,`b`|->`13w`,`imm`|->`0w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th2 = (*  ldr r1,[sp]  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`1w`,`b`|->`13w`,`imm`|->`0w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))
  val th1 = ALIGN_VARS ["y1"] th1  
  val th1 = AUTO_HIDE_STATUS th1  
  val th2 = ALIGN_VARS ["y2"] th2  

  val th1 = (*  add r1,r2,r3  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`1w`,`a`|->`2w`,`b`|->`3w`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_ADD3))
  val th2 = (*  ldr r1,[sp]   *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`1w`,`b`|->`13w`,`imm`|->`0w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))
  val th1 = AUTO_HIDE_POST1 [`R 1w`] th1
  val th2 = ALIGN_VARS ["y2"] th2
  val th2 = APP_FRAME `~R 2w` th2
  val name1 = "th1"
  val name2 = "th2"
*)

fun find_composition1 (th1,name1) (th2,name2) = let
  val (_,_,_,Q,_) = dest_ARM_PROG (concl th1)
  val (P,_,_,_,_) = dest_ARM_PROG (concl th2)
  fun number i [] = [] | number i (x::xs) = (x,i) :: number (i+1) xs
  val xs = (number 1 o list_dest_STAR) Q
  val ys = (number 1 o list_dest_STAR) P
  fun can_match x y = get_sep_domain x = get_sep_domain y handle e => x = y
  fun m x y = can_match y x
  fun fetch_match (x,i) [] = (0,0,tl [])
    | fetch_match (x,i) ((y,j)::ys) = if m x y then (i,j,ys) else 
        let val (i1,j1,zs) = fetch_match (x,i) ys in (i1,j1,(y,j)::zs) end
  fun partition [] ys (xs1,xs2,ys1,ys2) = (xs1,xs2,ys1,ys2 @ map snd ys)
    | partition (x::xs) ys (xs1,xs2,ys1,ys2) =
        let val (i,j,zs) = fetch_match x ys in
          partition xs zs (xs1 @ [i], xs2, ys1 @ [j], ys2)
        end handle e =>
          partition xs ys (xs1, xs2 @ [snd x], ys1, ys2)
  val (xs1,xs2,ys1,ys2) = partition xs ys ([],[],[],[])
  fun mk_star_q [] = "emp"
    | mk_star_q [i] = "x" ^ int_to_string i
    | mk_star_q (i::is) = "x" ^ int_to_string i ^ "*" ^ mk_star_q is
  val xs_str1 = mk_star_q (map snd xs) 
  val xs_str2 = "(" ^ mk_star_q xs1 ^ ")*(" ^ mk_star_q xs2 ^ ")" 
  val ys_str1 = mk_star_q (map snd ys) 
  val ys_str2 = "(" ^ mk_star_q ys1 ^ ")*(" ^ mk_star_q ys2 ^ ")" 
  val (xs1,xs2) = ([QUOTE xs_str1],[QUOTE xs_str2])
  val (ys1,ys2) = ([QUOTE ys_str1],[QUOTE ys_str2])
  val th = MOVE_COMPOSE2 th1 th2 xs1 xs2 ys1 ys2
  val str = "MOVE_COMPOSE2 "^ name1 ^" "^ name2 ^" `"^ 
            xs_str1 ^"` `"^ xs_str2 ^"` `"^ ys_str1 ^"` `"^ ys_str2 ^"`"
  val _ = echo "m"
  in (th,str) end;

fun find_composition2 (th1,name1) (th2,name2) = let
  val (_,_,_,Q,_) = dest_ARM_PROG (concl th1)
  val (P,_,_,_,_) = dest_ARM_PROG (concl th2)
  fun f tm = (get_sep_domain tm,is_SEP_HIDE (fst (dest_comb tm))) handle e => (tm,false)
  val xs = (map f o list_dest_STAR) Q
  val ys = (map f o list_dest_STAR) P
  fun f ((d:term,false),(zs,qs)) = (zs,qs)
    | f ((d,true),(zs,qs)) = (zs,filter (fn x => d = x) zs @ qs)
  val f_xs = map fst (filter (not o snd) xs)
  val f_ys = map fst (filter (not o snd) ys)
  val hide_from_post = snd (foldr f (f_xs,[]) ys) 
  val hide_from_preS = snd (foldr f (f_ys,[]) xs) 
  val hide_from_pre = filter (fn tm => not ((fst o dest_const) tm = "S") handle e => true) hide_from_preS
  val hide_pre_status = length hide_from_pre < length hide_from_preS
  val th1 = AUTO_HIDE_POST1_TERM hide_from_post th1
  val th2 = AUTO_HIDE_PRE_TERM hide_from_pre th2
  fun to_str tm = "`" ^ term_to_string tm ^ "`"
  val name1 = if length hide_from_post = 0 then name1
    else "(AUTO_HIDE_POST1 ["^ list_to_string to_str hide_from_post "," ^"] "^name1^")"
  val name2 = if length hide_from_pre = 0 then name2
    else "(AUTO_HIDE_PRE ["^ list_to_string to_str hide_from_pre "," ^"] "^name2^")"
  in if not hide_pre_status then 
    find_composition1 (th1,name1) (th2,name2) 
  else let
    val (th2,name2) =  
          ((AUTO_PRE_HIDE_STATUS th2,"(AUTO_PRE_HIDE_STATUS "^name2^")") handle e => 
           (AUTO_HIDE_STATUS th2,"(AUTO_HIDE_STATUS "^name2^")"))
  in find_composition1 (th1,name1) (th2,name2) end end;

fun get_address_vars tm = let
  val x = Parse.parse_in_context [] `M x`
  val y = Parse.parse_in_context [] `M30 x`
  val tm = find_term (can (match_term x)) tm handle e =>
           find_term (can (match_term y)) tm
  fun list_dest_var tm = if is_var tm then [tm] else let 
    val (x,y) = dest_comb tm 
    val xs = list_dest_var x 
    val ys = list_dest_var y 
    in xs @ ys end handle e => [];
  in list_dest_var tm end handle e => [];

fun find_composition3 (th1,name1) (th2,name2) = let
  val (_,_,_,Q,_) = dest_ARM_PROG (concl th1)
  val (P,_,_,_,_) = dest_ARM_PROG (concl th2)
  val xs = (list_dest_STAR) Q
  val ys = (list_dest_STAR) P
  val vars = map get_address_vars ys
  val vars = foldr (uncurry append) [] vars
  fun g f list tm = mem (f (dest_comb tm)) list handle e => false
  val address_holders = filter (g snd vars) ys  
  fun f tm = let
    val (x,y1) = dest_comb tm
    val y2 = snd (dest_comb (hd (filter (g fst [x]) xs)))
    in [y1|->y2] end handle e => []
  val ss = foldr (uncurry append) [] (map f address_holders) 
  val th2 = INST ss th2
  val str = subst_to_string_no_types ss "  "
  val name2 = if length ss = 0 then name2
              else "(Q.INST "^str^" "^name2^")"
  in find_composition2 (th1,name1) (th2,name2) end;

fun find_composition4 (th1,name1) (th2,name2) = let
  val th = FALSE_COMPOSE th1 th2  
  val str = "FALSE_COMPOSE "^name1^" "^name2
  val _ = echo "f"
  in (th,str) end 
  handle e => find_composition3 (th1,name1) (th2,name2);

fun LENGTH_RW () = 
  SIMP_RULE arith_ss ([wLENGTH_def,LENGTH,LENGTH_APPEND] @ (!code_length_rewrites))

fun find_composition5 (th1,name1) (th2,name2) = let
  val (th,str) = find_composition4 (th1,name1) (th2,name2)
  in let 
    val th = LENGTH_RW () (ABSORB_POST th)  
    val th = if is_imp (concl th) then hd [] else th
    val str = "LENGTH_RW () (ABSORB_POST ("^str^"))" 
    in (th,str) end handle e => (th,str) end 
  handle e => let 
    val _ = print ("\n\n\nUnable to compose: \n\n" ^ 
              thm_to_string th1 ^ "\n\n\n" ^
              thm_to_string th2 ^ "\n\n\n") 
  in raise e end;

val find_composition = find_composition5;

fun get_unaligned tm = let
  val x = Parse.parse_in_context (free_vars tm) `M (addr30 x)`
  val tm = find_term (can (match_term x)) tm
  val tm = (snd o dest_comb o snd o dest_comb) tm  
  val tm = (snd o dest_comb o fst o dest_comb) tm handle e => tm
  val str = (fst o dest_var) tm
  in str end;

fun align_addresses th = let
  fun find_unaligned th xs = let
    val st = get_unaligned (concl th)
    val th = ALIGN_VARS [st] th 
    in find_unaligned th (st::xs) end
    handle e => (th,xs);
  val (th,xs) = find_unaligned th []
  fun str_list_to_str [] = ""
    | str_list_to_str [x] = "\"" ^ x ^ "\""
    | str_list_to_str (x::y::xs) = "\"" ^ x ^ "\"," ^ str_list_to_str (y::xs)
  val st = "[" ^ str_list_to_str xs ^ "]"
  val st = "ALIGN_VARS "^st^" "
  val st = if xs = [] then "" else st
  in (th,st) end;




(* ============================================================================= *)
(* NEW EXPERIMENTAL PROOF-PRODUCING FUNCTIONS                                    *)
(* ============================================================================= *)

datatype arm_code_format = 
  InLineCode | SimpleProcedure | PushProcedure of string list * int;

(* user changeable flags *)
val optimise_code = ref true;
val abbrev_code = ref false;

(* list of compiled code (name,th,is_proc,code length,code definition) *)
val compiled_specs = ref ([]:(string * thm * arm_code_format * int * thm) list);

(* internal rewrite lists and counter *)
val code1_abbreviations = ref ([]:thm list);
val code2_abbreviations = ref ([]:thm list);
val offset_counter = ref 0;


fun add_code_abbrevs code1_def c2 = let
  val tm = mk_comb(``LENGTH:word32 list -> num``,(fst o dest_eq o concl o SPEC_ALL) code1_def)
  val cc = code_length_conv()
  val length_thm = (SIMP_CONV arith_ss [code1_def,LENGTH,LENGTH_APPEND] THENC cc) tm
  val _ = code_length_rewrites := length_thm :: (!code_length_rewrites)
  val _ = code1_abbreviations := code1_def :: (!code1_abbreviations)
  fun g NONE = () | g (SOME code2_def) = 
    (code2_abbreviations := code2_def :: (!code2_abbreviations))
  in g c2 end;


fun transpose [] = [] | transpose (x::xs) = let
  val xs = rev (x::xs)  
  fun t [] ys = ys | t (x::xs) ys = t xs (map (uncurry cons) (zip x ys))
  in t (tl xs) (map (fn x => [x]) (hd xs)) end;

(*
val thms = (zip xs p)

val [(name1,th1),(name2,th2),(name3,th3)] = xs
val (th1,name1) = find_composition3 (th1,name1) (th2,name2)
val (th2,name2) = (th3,name3)
  find_composition3 (th1,name1) (th2,name2)
*)  

fun is_jump th = 
  ((fst o dest_const o post1_ARM_PROG o concl) th = "SEP_F") handle e => false;

fun get_jump_length th = let
  val tm = mk_comb(``LENGTH:word32 list -> num``,(code_ARM_PROG o concl) th)
  val code_l = (numSyntax.int_of_term o snd o dest_eq o concl o code_length_conv()) tm
  val tm = (snd o dest_comb o fst o dest_comb o snd o dest_comb o concl) th
  val (x,y) = (dest_comb o snd o dest_pair) tm
  in if fst (dest_const x) = "pcADD" then let
    val jump_l = (numSyntax.int_of_term o snd o dest_comb) y    
    val jump_length = jump_l - code_l
    in jump_length end else 10000000 end;  

fun APPEND_CODE th cs = let
  val th = MATCH_MP ARM_PROG_APPEND_CODE th
  val th = SPEC (foldr (listSyntax.mk_append) ``[]:word32 list`` cs) th
  val th = RW [APPEND,APPEND_NIL,APPEND_ASSOC] th
  val th1 = LENGTH_RW() (ABSORB_POST th)
  val th = if is_imp (concl th) then th else th1
  in th end;

fun get_number_of_specs n [] = 0
  | get_number_of_specs n ((_,th)::xs) = 
  if n <= 0 then 0 else let
    val tm = mk_comb(``LENGTH:word32 list -> num``,(code_ARM_PROG o concl) th)
    val code_l = (numSyntax.int_of_term o snd o dest_eq o concl o code_length_conv()) tm
    in 1 + get_number_of_specs (n - code_l) xs end
(*  
make_spec ["add r1,r2,r3","sub r2,r3,r4","mul r3,r4,r5","orr r1,r2,r3","mov r4,r2"]
make_spec ["b 16"]
make_spec ["eor r3,r4,r3"]

  val th1 = (*  add r1,r2,r3  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`1w`,`a`|->`2w`,`b`|->`3w`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_ADD3))
  val th2 = (*  sub r2,r3,r4  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`2w`,`a`|->`3w`,`b`|->`4w`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_SUB3))
  val thi = (*  b 16  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (2w :word24) :word30)``, EVAL ``(2w :word30) + (2w :word30)``] (Q.INST [`c_flag`|->`AL`,`offset`|->`2w` ] arm_B2))
  val th3 = (*  mul r3,r4,r5  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`3w`,`a`|->`4w`,`b`|->`5w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_MUL3))
  val th4 = (*  orr r1,r2,r3  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`1w`,`a`|->`2w`,`b`|->`3w`,`a_mode`|->`OneReg`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4` ] arm_ORR3))
  val th5 = (*  mov r4,r2     *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`4w`,`a`|->`2w`,`a_mode`|->`OneReg`,`x`|->`x5`,`y`|->`y5` ] arm_MOV2))
  val th6 = (*  eor r3,r4,r3  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`3w`,`a`|->`4w`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_EOR2))

  val thms = [("th1",th1),("th2",th2),("thi",thi),("th3",th3),("th4",th4),("th5",th5),("th6",th6)]
  val thms = []
  val name = "result"
*)
fun mk_compose_pass thms name = let
  fun h ((name,th),0) = (("SND_PROG2 "^name, SND_PROG2 th) handle e => (name,th))
    | h ((name,th),n) = (("FST_PROG2 "^name, FST_PROG2 th) handle e => (name,th))   
  val _ = echo "composing specs: "
  val xs = map h thms
(*
  fun compose_next_group group_name [] n = let val _ = print "hi" in hd [] end 
    | compose_next_group group_name ((prev_name,prev_th)::xs) n =
     if n <= 1 then (prev_th,xs) else
     if is_jump prev_th then let
       val th = prev_th
       val len = get_jump_length th
       fun take 0 xs = [] | take n [] = [] | take n (x::xs) = x::take (n-1) xs    
       fun drop 0 xs = xs | drop n [] = [] | drop n (x::xs) = drop (n-1) xs    
       val number_of_specs = get_number_of_specs len xs
       val ys = take number_of_specs xs
       val _ = map (fn y => echo "-") ys
       val cs = map (code_ARM_PROG o concl o snd) ys 
       val th = APPEND_CODE th cs    
       val s = list_to_string fst ys ","
       val s = "  val "^group_name^" = APPEND_CODE "^prev_name^" (map (code_ARM_PROG o concl) ["^s^"])\n"
       val _ = print_proof s
       val xs = drop number_of_specs xs
       val n = n - number_of_specs
     in compose_next_group group_name ((group_name,th)::xs) n end else let
       val (curr_name,curr_th) = hd xs
       val (th,s) = find_composition (prev_th,prev_name) (curr_th,"("^curr_name^")")
       val s = "  val "^group_name^" = "^s^"\n"
       val _ = print_proof s
     in compose_next_group group_name ((group_name,th)::tl xs) (n-1) end
  fun min m n = if m < n then m else (n:int)
  fun make_groups [] i result = result
    | make_groups [(name,th)] i result = (result @ [(name,th)])
    | make_groups thms i result = let
    val name = "g" ^ int_to_string i
    val (th,thms) = compose_next_group name thms (min 2 (length thms))
    in if is_jump th then 
      make_groups ((name,th)::thms) i (result)
    else
      make_groups thms (i+1) (result @ [(name,th)]) end  
  val groups = make_groups xs 1 []
  fun compose_groups ((n2,th2),(n1,th1)) = let
    val (th,s) = find_composition (th1,n1) (th2,"("^n2^")")        
    val s = "  val "^n1^" = "^s^"\n"
    val _ = print_proof  s 
    in (n1,th) end
  val (name,th) = foldl compose_groups (hd groups) (tl groups)
*)
  fun find_compositions prev_name prev_th [] = ([],prev_th) 
    | find_compositions prev_name prev_th xs = 
       if is_jump prev_th then let
         val th = prev_th
         val len = get_jump_length th
         fun take 0 xs = [] | take n [] = [] | take n (x::xs) = x::take (n-1) xs    
         fun drop 0 xs = xs | drop n [] = [] | drop n (x::xs) = drop (n-1) xs    
         val number_of_specs = get_number_of_specs len xs
         val ys = take number_of_specs xs
         val _ = map (fn y => echo "-") ys
         val cs = map (code_ARM_PROG o concl o snd) ys 
         val th = APPEND_CODE th cs    
         val s = list_to_string fst ys ","
         val s = "  val "^name^" = APPEND_CODE "^name^" (map (code_ARM_PROG o concl) ["^s^"])\n"
         val (ys,th) = find_compositions name th (drop number_of_specs xs)
       in (s::ys,th) end else let
         val (curr_name,curr_th) = hd xs
         val (th,s) = find_composition (prev_th,prev_name) (curr_th,"("^curr_name^")")
         val s = "  val "^name^" = "^s^"\n"
         val (ys,th) = find_compositions name th (tl xs)
       in (s::ys,th) end
  val (prev_name,prev_th) = hd xs
  val (strs,th) = find_compositions ("("^prev_name^")") prev_th (tl xs) 
  val _ = echo ".\n" 
  val th = AUTO_HIDE_STATUS th
  in ([],th) end;

fun pad_strings [] = [] | pad_strings (x::xs) = let
  val m = foldr (fn (m,n) => if m > n then m else n) (size x) (map size xs)
  fun pad s i = if i <= 0 then s else pad (s^" ") (i-1) 
  in map (fn s => pad s (m - size s)) (x::xs) end;

fun make_passes_th code = let
  fun f (s,(ys,n)) = 
    if (substring(s,0,6) = "proc: ") handle e => false then let
      val i = int_to_string n
      val name = substring(s,6,size(s)-6)
      val name = replace_char #" " "" name
      fun match_name (n,_,_,_,_) = n = name 
      val (_,th,proc,_,_) = hd (filter match_name (!compiled_specs))
      val _ = offset_counter := !offset_counter + 1
      val offset_name = "offset" ^ int_to_string (!offset_counter)
      val th = if not (proc = InLineCode) then SIMP_RULE (std_ss++setINC_ss) [] (MATCH_MP (Q.INST [`offset`|->[QUOTE offset_name]] arm_BL) (PROG2PROC `lr` th)) else th
      val str = if not (proc = InLineCode) then "SIMP_RULE (std_ss++setINC_ss) [] (MATCH_MP arm_BL (PROG2PROC `lr` "^name^"_arm))" else name^"_arm"
      in ((ys @ [(s,"th"^i,str,th)]),n+1) end
    else let
      val i = int_to_string n
      val (th,str) = string_to_prog s i
      val th = RW [WORD_CMP_NORMALISE] th
      val str = "RW [WORD_CMP_NORMALISE] (" ^ str ^ ")"
      val (th,str2) = align_addresses th 
      val str = if str2 = "" then str else str2 ^ "(" ^ str ^ ")" 
      in ((ys @ [(s,"th"^i,str,th)]),n+1) end
  val xs = pad_strings (map fst code)
  val xs = fst (foldl f ([],1) xs)  
  val paths = transpose (map snd code)
  fun to_str (s,i,str,th) = let
    val i = if size(i) < 4 then i ^ " " else i
    in "  val "^i^" = ("^"*  "^s^"  *"^") "^str^"\n" end
  val strs = map to_str xs  
  val xs = map (fn (s,name,str,th) => (name,th)) xs
  fun f (p,(i,ys,strs,pnames)) = let
    val pname = "p"^int_to_string i
    val (strs2,th) = mk_compose_pass (zip xs p) pname
    in (i+1,ys @ [th],strs @ strs2,pnames @ [pname]) end;
  val (_,th,strs,pnames) = foldl f (1,[],strs,[]) paths
  val th = zip pnames th
  val pnames = foldr (fn (x,y) => x^","^y) (last pnames) (butlast pnames)
  in (th,strs) end;

(*
  val (i,ys,strs,pnames) = (1,[],strs,[])
  val p = hd paths
*)

fun make_passes code = 
  print (foldr (uncurry concat) "" (["\n\n\n"] @ snd (make_passes_th code) @ ["\n\n\n"]));

(*
 val code = [
("add r1,r2,r3",[1,1,1,1]),
("teq r1,#0   ",[1,1,1,1]),
("beq 12      ",[1,1,0,0]),
("sub r1,r1,r3",[0,0,1,1]),
("mul r2,r3,r2",[0,0,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("tst r2,r1   ",[1,1,1,1]),
("bne -44   "  ,[0,1,0,1])]
*)

(* generate ARM code *)

fun string_remove_primes str = replace_char #"'" "" str;
val num_to_string = int_to_string o Arbint.toInt o Arbint.fromNat

fun code_length xs = let
  fun is_proc s = ((substring(s,0,6) = "proc: ") handle e => false)
  val (xs,procs) = (filter (not o is_proc) xs, filter is_proc xs)
  fun f st = hd (filter (fn (n,_,_,_,_) => n = substring(st,6,size(st)-6)) (!compiled_specs))
  val procs = map ((fn (n,th,p,l,_) => (p,l)) o f) procs
  fun f ((InLineCode,i),sum) = sum + i | f ((_,i),sum) = sum + 1
  in length xs + foldr f 0 procs end;

fun dest_reg_var x = let
  val name = (string_remove_primes o fst o dest_var) x
  in if substring(name,0,1) = "r" then name else hd [] end;

fun dest_mem_var x = let
  val y = (string_remove_primes o fst o dest_var) x
  fun f s = int_to_string (string_to_int (substring(s,1,size(s)-1)) * 4)
  val v = substring(y,0,1)
  in if v = "m" then f y else if v = "n" then "-"^f y else hd [] end;

fun dest_reg_var_or_const x = dest_reg_var x handle e => let
  val (x,y) = dest_comb x
  val _ = if fst (dest_const x) = "n2w" then x else hd []
  in ("#" ^ (num_to_string o numSyntax.dest_numeral) y) end;

fun dest_addr_mode1 x = dest_reg_var_or_const x handle e => let
  val (x,rhs) = dest_comb x
  val (x,lhs) = dest_comb x
  val x = fst (dest_const x)
  val lhs = dest_reg_var_or_const lhs
  val rhs = (num_to_string o numSyntax.dest_numeral) rhs
  fun g "word_lsl" = lhs^", lsl #"^rhs
    | g "word_lsr" = lhs^", lsr #"^rhs
    | g "word_asr" = lhs^", asr #"^rhs
    | g _ = hd []
  in g x end;

fun make_branch_code_main exp = let 
  (* normal binary test *)
  val (exp,rhs) = dest_comb exp
  val (exp,lhs) = dest_comb exp
  val exp = fst (dest_const exp)
  fun comma lhs rhs = " "^lhs^", "^rhs
  fun g "=" lhs rhs       = (["cmp" ^ comma lhs rhs],"eq","ne")
    | g "word_lt" lhs rhs = (["cmp" ^ comma lhs rhs],"lt","ge")
    | g "word_le" lhs rhs = (["cmp" ^ comma lhs rhs],"le","gt")
    | g "word_ls" lhs rhs = (["cmp" ^ comma lhs rhs],"ls","hi")
    | g "word_lo" lhs rhs = (["cmp" ^ comma lhs rhs],"cc","cs") 
    | g _ _ _ = (["error"],"","")
  val (xs,cond,not_cond) = g exp (dest_reg_var lhs) (dest_addr_mode1 rhs)
  in (xs,cond,not_cond) end handle e => let
  (* case of r1 && r2 = 0w *)
  val ss = match_term (Parse.parse_in_context [] `r1 && r2:word32 = 0w`) exp
  val exp = (snd o dest_comb o fst o dest_comb) exp
  val (exp,rhs) = dest_comb exp
  val (exp,lhs) = dest_comb exp
  val x = dest_reg_var lhs
  val y = dest_addr_mode1 rhs
  in (["cmp "^x^", "^y,"tst "^x^", "^y],"eq","ne") end
  (* others failed, try if the expression was negated *) 
  handle e => let
  val (xs,cond,not_cond) = make_branch_code_main (dest_neg exp) 
  in (xs,not_cond,cond) end;

fun word_cmp_normalise_term tm = let
  val th = REWRITE_CONV [WORD_CMP_NORMALISE] tm
  val tm = (snd o dest_eq o concl) th    
  in tm end handle e => tm;

fun make_branch_code exp = 
  make_branch_code_main (word_cmp_normalise_term exp) 
  handle e => let 
  val tm = word_cmp_normalise_term (mk_neg(exp))
  val (xs,not_cond,cond) = make_branch_code_main tm
  in (xs,cond,not_cond) end;

fun find_assignment_code var exp = 
  let (* binary operators *)
  val (exp,rhs) = dest_comb exp
  val (exp,lhs) = dest_comb exp
  val exp = fst (dest_const exp)
  fun comma var lhs rhs = " "^var^", "^lhs^", "^rhs
  fun g "word_add" var lhs rhs = ["add%" ^ comma var lhs rhs]
    | g "word_sub" var lhs rhs = ["sub%" ^ comma var lhs rhs]
    | g "word_mul" var lhs rhs = ["mul%" ^ comma var lhs rhs]
    | g "word_and" var lhs rhs = ["and%" ^ comma var lhs rhs]
    | g "word_or"  var lhs rhs = ["orr%" ^ comma var lhs rhs]
    | g "word_xor" var lhs rhs = ["eor%" ^ comma var lhs rhs]
    | g _ _ _ _ = ["error"] 
  val var = (string_remove_primes o fst o dest_var) var
  in g exp var (dest_reg_var lhs) (dest_addr_mode1 rhs) end 
  handle e => let (* code for mvn - move negative *) 
  val (not,exp) = dest_comb exp
  val _ = if fst (dest_const not) = "word_1comp" then not else hd []
  val var = dest_reg_var var
  in ["mvn% "^var^", "^dest_addr_mode1 exp] end 
  handle e => let (* code for mov - move *)
  val var = dest_reg_var var
  in ["mov% "^var^", "^dest_addr_mode1 exp] end 
  handle e => (* code for ldr - load register *)
    ["ldr% "^dest_reg_var var^", [sp,#"^dest_mem_var exp^"]"]
  handle e => (* code for str - store register *)
    ["str% "^dest_reg_var exp^", [sp,#"^dest_mem_var var^"]"]
  handle e => let (* code for procedure call *)
    val name = fst (dest_const (fst (dest_comb exp) handle e => exp))       
    in ["proc: "^name] end;

fun pull_out_shared_front xs ys = let
  fun share x y = (x = y) andalso not (replace_char #"%" "" (fst x) = fst x)
  fun add (x,x1) (y,y1) = (x,x1 @ y1) 
  fun f [] [] (xs',ys',zs') = (xs',ys',zs')
    | f (x::xs) [] (xs',ys',zs') = (xs' @ (x::xs),ys',zs')
    | f [] (y::ys) (xs',ys',zs') = (xs',ys' @ (y::ys),zs')
    | f (x::xs) (y::ys) (xs',ys',zs') = 
       if share x y then f xs ys (xs',ys',zs' @ [add x y]) 
       else (xs' @ (x::xs),ys' @ (y::ys),zs')
  in f xs ys ([],[],[]) end;

fun pull_out_shared_tail xs ys = let
  fun share (x,_) (y,_) =
    replace_char #"%" "" x = replace_char #"%" "" y 
  fun add (x,x1) (y,y1) = (x,x1 @ y1)
  fun f [] [] (xs',ys',zs') = (xs',ys',zs')
    | f (x::xs) [] (xs',ys',zs') = (rev (x::xs) @ xs',ys',zs')
    | f [] (y::ys) (xs',ys',zs') = (xs',rev (y::ys) @ ys',zs')
    | f (x::xs) (y::ys) (xs',ys',zs') = 
       if share x y then f xs ys (xs',ys',add x y::zs') 
       else (rev (x::xs) @ xs',rev (y::ys) @ ys',zs')
  in f (rev xs) (rev ys) ([],[],[]) end;

fun first_n 0 xs = [] | first_n n xs = hd xs :: first_n (n-1) (tl xs);
fun repeat_n 0 x = [] | repeat_n n x = x :: repeat_n (n-1) x;
fun is_bottom st = substring(st,0,8) = "$bottom$" handle e => false;
fun is_top st = substring(st,0,5) = "$top$" handle e => false;

fun make_block_conditional xs cond = let
  val _ = if length xs < 6 then true else hd []
  fun f (cmd,trace) = let
    val cmd' = replace_char #"%" cond cmd 
    in if cmd = cmd' then hd [] else (cmd',trace) end
  in (true,map f xs) end 
  handle e => (false,map (fn (cmd,t) => (replace_char #"%" "" cmd,t)) xs);

(*
  val tm = tm2
*)

(* intial phase: choose instructions *)
fun make_inst_list1 tm = 
  let (* case: if-then-else *)
  val (g,tm1,tm2) = dest_cond tm
  val (xs,xst) = make_inst_list1 tm1
  val (ys,yst) = make_inst_list1 tm2
  val (test,cond,not_cond) = make_branch_code g
  in if not (!optimise_code) then let 
    val j_xs = ["b" ^ not_cond ^ " " ^  int_to_string (4 * (code_length xs + 1))]
    val test_trace = map (fn x => 1) test
    val xs0 = map (fn x => 0) xs
    val ys0 = map (fn x => 0) ys
    val xst = map (fn t => test_trace @ [0] @ t @ ys0) xst 
    val yst = map (fn t => test_trace @ [1] @ xs0 @ t) yst
    val code = map (replace_char #"%" "") (test @ j_xs @ xs @ ys)
    in (code,xst @ yst) end 
  else let (* optimise if-then-else *)
    val xsl = length xst
    val ysl = length yst
    val xs_zero = repeat_n xsl 0
    val xs_one = repeat_n xsl 1
    val ys_zero = repeat_n ysl 0
    val ys_one = repeat_n ysl 1
    (* zip together traces with code *)
    val xs = zip xs (transpose xst)
    val ys = zip ys (transpose yst)
    (* extract shared tails *)
    val (xs1,ys1,zs1) = pull_out_shared_tail xs ys
    val (xs1,ys1,zs2) = pull_out_shared_front xs1 ys1
    (* bug fix: if xs and ys are both empty then won't be able to 
                find the this branch, hence don't optimise in that case *)
    val (xs,ys,zs1,zs2) = if length xs1 = 0 andalso length ys1 = 0 
                          then ([hd xs],[hd ys],(tl zs1 handle e => []),(tl zs2 handle e => []))
                          else (xs1,ys1,zs1,zs2) 
    (* fix traces *)
    val xs  = map (fn (cmd,t) => (cmd,t @ ys_zero)) xs
    val ys  = map (fn (cmd,t) => (cmd,xs_zero @ t)) ys
    (* make each instruction conditional *)
    val (xs_c,xs) = make_block_conditional xs cond
    val (ys_c,ys) = make_block_conditional ys not_cond
    (* add traces for jumps *)
    val jump_over_xs_trace = xs_zero @ ys_one
    val jump_over_ys_trace = xs_one @ ys_zero
    val xs = (xs_c,(xs,(jump_over_xs_trace,cond)))
    val ys = (ys_c,(ys,(jump_over_ys_trace,not_cond)))
    (* switch the order of xs and ys in case xs will bottom out *)
    val (xs,ys) = if length(fst(snd(xs))) = 0 then (xs,ys) else 
                  (if is_bottom(fst(last(fst(snd(xs))))) then (ys,xs) else (xs,ys))
    (* switch the order of xs and ys in case ys can be made conditional but xs cannot *)
    val (xs,ys) = if not (fst xs) andalso fst ys then (ys,xs) else (xs,ys)
    (* generate jump over ys *)
    val jump_over_ys = 
      if fst ys then [] else let
        val jump_length = 4 * (code_length (map fst (fst(snd(ys)))) + 1)
        val jump_inst = "b% " ^ int_to_string jump_length
        val jump_inst = replace_char #"%" (if fst xs then snd(snd(snd(xs))) else "") jump_inst
        val jump_over_trace = fst(snd(snd(ys)))
        in [(jump_inst,jump_over_trace)] end 
    (* erase jump over ys in case xs ends in $bottom or $top *)
    val jump_over_ys = let
      val last_xs_inst = fst(last(fst(snd(xs)))) 
      in if is_bottom last_xs_inst orelse is_top last_xs_inst 
         then [] else jump_over_ys end handle e => jump_over_ys
    (* generate jump over xs *)
    val jump_over_xs = 
      if fst xs then [] else let
        val jump_length = 4 * (code_length (map fst (fst(snd(xs)))) + 1 + length jump_over_ys)
        val jump_inst = "b"^snd(snd(snd(ys)))^" " ^ int_to_string jump_length
        val jump_over_trace = fst(snd(snd(xs)))
        in [(jump_inst,jump_over_trace)] end
    (* separate code and traces *)
    val xs = jump_over_xs @ fst(snd(xs))
    val ys = jump_over_ys @ fst(snd(ys))
    val test = map (fn cmd => (cmd, xs_one @ ys_one)) test
    val qs = test @ zs2 @ xs @ ys @ zs1
    val code = map (replace_char #"%" "" o fst) qs
    val traces = transpose (map snd qs)
    in (code, traces) end end
  handle e => 
  let (* case: let *)
  val (xs,tail) = pairSyntax.dest_anylet tm  
  val (var,exp) = hd xs
  val xs = find_assignment_code var exp
  val t1 = map (fn x => 1) xs
  val (ys,ts) = make_inst_list1 tail
  in (xs @ ys,map (fn t => t1 @ t) ts) end handle e => 
  let (* case: return *)
  val xs = dest_var tm handle e => (dest_var o fst o dest_pair) tm
  in (["$bottom$%"],[[1]]) end handle e =>
  let (* case: rec call *)
  val _ = dest_comb tm
  in (["$top$%"],[[1]]) end handle e => (["error"],[[1]]);

(* second phase: make branches concrete *)
fun make_inst_list2 def = let
  val tm = (snd o dest_eq o concl o SPEC_ALL) def
  val (xs,t) = make_inst_list1 tm
  val xs = map (replace_char #"%" "") xs
  val (xs,t) = if is_bottom(last xs) then (butlast xs,map butlast t) else (xs,t)
  val l = 4 * code_length xs
  fun set_top_bottom (cmd,(xs,i)) =
    let val j = code_length [cmd] * 4 in
    if is_top(cmd) then
      (xs @ ["b"^substring(cmd,5,size(cmd) - 5)^" -"^int_to_string (i-4)],i+j)
    else if is_bottom(cmd) then
      (xs @ ["b"^substring(cmd,8,size(cmd) - 8)^" "^int_to_string (l-i+4)],i+j)
    else 
      (xs @ [cmd],i+j) end
  val xs = fst (foldl set_top_bottom ([],4) xs) 
  val t = transpose t
  in zip xs t end;


(* build spec *)

fun mk_substs_string [] name = []
  | mk_substs_string (x::xs) name = 
      ["  val "^name^" = Q.INST [" ^ foldl (fn (x,y) => x ^ "," ^ y) x xs ^ "] "^name^"\n"];

fun standardise_names name terms th = let
  (* rename variables, e.g. R 1w y3 --> R 1w r1 *)
  fun find_subst tm = let
    val (x,z) = dest_comb tm
    val z_str = fst (dest_var z)
    val (x,y) = dest_comb x 
    val n2w_to_string = num_to_string o numSyntax.dest_numeral o snd o dest_comb
    in if fst (dest_const x) = "R" then let
      val i = n2w_to_string y
      val var = mk_var("r"^i,type_of z)
      val subst = z |-> var
      val subst_str = "`"^ z_str ^"`|->`r"^i^"`"  
      in ([subst],[subst_str]) end 
    else if fst (dest_const x) = "R30" andalso y = ``13w:word4`` then 
         ([z|->``sp:word30``],["`"^ z_str ^"`|->`sp`"])
    else let
      val i = (snd o dest_comb) y handle e => ``0w:word30``
      val i = n2w_to_string i 
      val var_str = 
           if i = "0" then "m" else
           if (fst o dest_const o fst o dest_comb o fst o dest_comb) y = "word_add" 
           then "m" else "n" handle e => "m"
      val var = mk_var(var_str^i,type_of z)
      val subst = z |-> var
      val subst_str = "`"^ z_str ^"`|->`"^var_str^i^"`"  
      in ([subst],[subst_str]) end handle e => ([],[]) end
  fun renamer (tm,(th,xs,zs)) = let
      val (y,z) = find_subst tm handle e => ([],[])
      val tm = Term.subst y tm      
      val th = INST y th
      in (th, tm :: xs, z @ zs) end
  val (th,terms,substs) = foldr renamer (th,[],[]) terms
  val strs = mk_substs_string substs name
  in (th,strs) end;

fun dest_tuple tm = 
  let val (x,y) = dest_pair tm in x :: dest_tuple y end handle e => [tm];

fun get_input_list def = 
  let val tm = (fst o dest_eq o concl o SPEC_ALL) def in 
    map (fst o dest_var) ((dest_tuple o snd o dest_comb) tm) end handle e => [];
  
fun get_output_list def = let
  val tm = (snd o dest_eq o concl o SPEC_ALL) def
  fun ground_terms tm =
    let (* case: if-then-else *)
    val (_,x,y) = dest_cond tm
    in ground_terms x @ ground_terms y end handle e => 
    let (* case: let *)
    val tm = (snd o pairSyntax.dest_anylet) tm
    in ground_terms tm end handle e =>
    let (* case: return, single variable *)
    in [[fst (dest_var tm)]] end handle e =>
    let (* case: return, tuple of variables *)
    val (x,y) = dest_pair tm
    in [map (fst o dest_var) (x :: dest_tuple y)] end handle e => [];
  val gt = ground_terms tm
  val (x,xs) = (hd gt,tl gt)
  val rest = filter (fn y => not (x = y)) xs
  in if length(rest) > 0 then raise ERR "get_output_list" "Incompatible outputs." else x end;
  
(* takes e.g. ``R 1w`` produces "r1", and ``M (sp + 1w)`` produces "m1" *)
fun term_to_name tm = let
  val (x,y) = dest_comb tm  
  val f = num_to_string o numSyntax.dest_numeral o snd o dest_comb
  val i = f y handle e => (f o snd o dest_comb) y handle e => "0"         
  val x = if fst (dest_const x) = "R" then "r"^i else
          if fst (dest_const x) = "R30" andalso i = "13" then "sp" else 
          if fst (dest_const x) = "M" then "m"^i else "n"^i 
  in x end handle e => term_to_string tm;  

(* attempts to do the opposite of term_to_name *)
fun name_to_string_of_term name =
  if name = "sp" then "R30 13w" else
  if substring(name,0,1) = "r" then "R "^substring(name,1,size(name)-1)^"w" else
  if substring(name,0,1) = "m" then "M (sp + "^substring(name,1,size(name)-1)^"w)" else
  hd [];
  
fun name_to_term result_type name = 
  Parse.Term [QUOTE (name_to_string_of_term name ^ " " ^ name ^ type_to_string result_type)];

fun rename_and_fill_preconditions thms def = let
  (* extract preconditions *)
  fun is_SEP_cond tm = let
    val {Name = n, Thy = t, Ty = _} = (dest_thy_const o fst o dest_comb) tm
    in if t = "set_sep" andalso n = "cond" then true else false end handle e => false;   
  fun extract_pre_lists (name,th) = let
    val (p,_,_,_,_) = dest_ARM_PROG (concl th)
    val p = filter (not o is_SEP_cond) (list_dest_STAR p)
    in (name,p,th) end
  val thms = map extract_pre_lists thms
  (* standardise names *)
  fun f (name,pres,th) = let
    val (th,strs) = standardise_names name pres th
    val (p,_,_,_,_) = dest_ARM_PROG (concl th)
    val pres = filter (not o is_SEP_cond) (list_dest_STAR p)
    in (name,pres,th,strs) end;
  val thms = map f thms
  (* make a list of all elements that occur in a precondition *)    
  fun merge [] (ys,zs) = (ys,zs)
    | merge (x::xs) (ys,zs) = let
       val y = get_sep_domain x
       in if mem y ys then merge xs (ys,zs) else merge xs (y::ys,x::zs) end
  fun merge_pres ((name,pres,th,strs),result) = merge pres result
  val pre_elements = snd (foldl merge_pres ([],[]) thms)
  (* if no precondition mentions an element that is required then add it in *)
  val term_type = type_of (hd pre_elements)
  val in_list = get_input_list def
  val pre_names = map (term_to_name o get_sep_domain) pre_elements
  fun g x = not (mem x pre_names)
  val extras = map (name_to_term term_type) (filter g in_list)
  val pre_elements = pre_elements @ extras
  (* insert missing elements into specs *)
  fun delete xs ys = let
    val zs = map get_sep_domain ys
    in filter (fn x => not (mem (get_sep_domain x) zs)) xs end
  fun f (name,pres,th,strs) = let    
    val new = delete pre_elements pres
    val pres = pres @ new 
    in if new = [] then (name,pres,th,strs) else let
    val frame = list_mk_STAR new
    val th = RW [STAR_ASSOC] (SPEC frame (APP_BASIC_FRAME th))     
    val str = ["  val "^name^" = RW [STAR_ASSOC] (APP_FRAME `"^term_to_string frame^"` "^name^")\n"]
    in (name,pres,th,strs @ str) end end
  val thms = map f thms
  in thms end;

fun hide_pre_post_elements thms def = let
  val in_list = get_input_list def @ ["sp"]
  val out_list = get_output_list def @ ["sp"]
  (* mark which theorems exit the loop, pick out post *)
  fun f (name,pres,th,strs) = let
    val (_,_,_,q,qs) = dest_ARM_PROG (concl th)
    val g = fst (dest_const q) = "SEP_F" handle e => false
    val q = if g then (fst o dest_pair o snd o dest_comb o fst o dest_comb) qs else q
    in (name,pres,list_dest_STAR q,g,th,strs) end
  val thms = map f thms
  (* hide posts and pres *)
  fun get_hide_list xs names name func_name = let
    fun h tm = (not o is_SEP_HIDE o fst o dest_comb) tm handle e => true
    val xs = filter h xs
    fun h tm = not (mem ((term_to_name o fst o dest_comb) tm) names) handle e => false
    fun k tm = "`" ^ term_to_string tm ^ "`"
    val xs = map (fst o dest_comb) (filter h xs) 
    val ys = map k xs
    val strs = if xs = [] then [] else ["  val "^name^" = AUTO_HIDE_"^
                 func_name^" ["^ foldl (fn (x,y) => x ^","^ y) (hd ys) (tl ys)^"] "^name^"\n"]
    in (xs,strs) end
  fun hide_pre_post (name,pres,posts,loop,th,strs) = let
    val (xs,func_name,f) = if loop then (in_list,"POST",AUTO_HIDE_POST_TERM) 
                                   else (out_list,"POST1",AUTO_HIDE_POST1_TERM)
    val (xs,str1) = get_hide_list posts xs name func_name
    val th = f xs th handle e => let
      val _ = print ("\n\n\nUnable to hide from postcondition one of the following: \n\n  "^
               list_to_string term_to_string xs "   " ^
               "\n\n\n"^thm_to_string th ^"\n\n\n") in raise e end
    val (xs,str2) = get_hide_list pres in_list name "PRE"
    val th = AUTO_HIDE_PRE_TERM xs th handle e => let
      val _ = print ("\n\n\nUnable to hide from precondition one of the following: \n\n  "^
               list_to_string term_to_string xs "   " ^
               "\n\n\n"^thm_to_string th ^"\n\n\n") in raise e end
    in (name,loop,th,strs @ str1 @ str2) end 
  val thms = map hide_pre_post thms
  in thms end;      

fun flatten_pairs tm xs = let
  val (x,y) = (dest_pair o fst o dest_eq o concl o ISPEC tm) PAIR
  in flatten_pairs y (xs @ [x]) end handle e => xs @ [tm];

fun get_pre_post_terms def_name thms def strs = let
  val (_,_,th,_) = hd (filter (fn (name,b,th,strs) => not b) thms)
  val th = RW [GSYM ARM_PROG_MOVE_COND] (DISCH ``5=4`` th)  
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val (p,_,_,q,_) = dest_ARM_PROG (concl th)
  val p = fst (dest_STAR p)
  val ps = list_dest_STAR p
  val qs = list_dest_STAR q  
  (* sort the results *)
  fun sep_to_string tm = let
    val tm = (snd o dest_eq o concl o REWRITE_CONV [R30_def,M30_def]) tm handle e => tm
    val tm = get_sep_domain tm
    val is_reg = (fst o dest_const o fst o dest_comb) tm = "R" handle e => false
    in if is_reg then let
      val x = term_to_string (snd (dest_comb tm))
      in if size(x) < 3 then "AA 0"^x else "AA "^x end 
    else term_to_string tm end
  val sorter = sort (curry (fn (tm1,tm2) => sep_to_string tm1 < sep_to_string tm2))
  val ps = sorter ps
  val qs = sorter qs
  (* substitute in the result of the def function *)
  val out = get_output_list def  
  val out' = flatten_pairs ((fst o dest_eq o concl o SPEC_ALL) def) []
  val out = zip out out'
  fun f tm = let
    val tm = fst (dest_comb tm)
    val x = term_to_name tm 
    val xs = filter (fn y => fst y = x) out
    val y = snd (hd xs) 
    in mk_comb(tm,y) end handle e => tm
  val qs = map f qs
  (* wrap it up *)
  val pre_tm = list_mk_STAR ps
  val post_tm = list_mk_STAR qs
  (* print it out *)
  val s1 = "  val pre  = `" ^ replace_char #"\n" " " (term_to_string pre_tm) ^ "`\n"
  val s2 = "  val post = `" ^ replace_char #"\n" " " (term_to_string post_tm) ^ "`\n"
  val s3 = "  val def  = COMPILER_FORMAT_DEF " ^ def_name ^ "\n"
  val strs = s1::s2::s3::strs
  in (pre_tm,post_tm,strs) end;

fun RAND_SIMP_SEP_IMP def post_tm th = let
  val th = ISPEC post_tm (MATCH_MP ARM_PROG_WEAKEN_POST1 th)
  val cc = RAND_CONV (ONCE_REWRITE_CONV [def])
  val cc = cc THENC SIMP_CONV std_ss [SEP_IMP_MOVE_COND,LET_DEF] 
  val cc = cc THENC RATOR_CONV (ONCE_REWRITE_CONV 
      (map GSYM [WORD_NOT_LESS,WORD_NOT_LESS_EQUAL,
                 WORD_NOT_LOWER_EQUAL,WORD_NOT_LOWER]))
  val cc = cc THENC SIMP_CONV bool_ss []
  val cc = cc THENC SIMP_CONV (std_ss++star_ss) [SEP_IMP_REFL,LET_DEF]
  val th = CONV_RULE (RATOR_CONV (RAND_CONV cc)) th
  in th end;

fun RAND_SIMP_SEP_IMP2 def th = let
  val cc = RAND_CONV (ONCE_REWRITE_CONV [def])
  val cc = cc THENC SIMP_CONV std_ss [SEP_IMP_MOVE_COND,LET_DEF] 
  val cc = cc THENC RATOR_CONV (ONCE_REWRITE_CONV 
      (map GSYM [WORD_NOT_LESS,WORD_NOT_LESS_EQUAL,
                 WORD_NOT_LOWER_EQUAL,WORD_NOT_LOWER]))
  val cc = cc THENC SIMP_CONV bool_ss []
  val cc = cc THENC SIMP_CONV (std_ss++star_ss) [SEP_IMP_REFL,LET_DEF]
  val th = CONV_RULE (RATOR_CONV (RAND_CONV cc)) th
  in th end;

fun weaken_strengthen thms def pre_tm post_tm = let
  (* duplicate the condition, add cond (1+1=2) as a dummy to make sure there is a cond! *)
  fun dup (name,b,th,strs) = let
    val th = RW [GSYM ARM_PROG_MOVE_COND] (DISCH ``1+1=2`` th)
    val th = DUPLICATE_COND th
    val str1 = ["  val "^name^" = RW [GSYM ARM_PROG_MOVE_COND] (DISCH ``1+1=2`` "^name^")\n"]
    val str2 = ["  val "^name^" = DUPLICATE_COND "^name^"\n"]
    in (name,b,th,strs @ str1 @ str2) end
  val thms = map dup thms  
  (* weaken posts in base cases *)
  fun weak (name,true,th,strs) = (true,(name,true,th,strs))
    | weak (name,false,th,strs) = let
    val th = RAND_SIMP_SEP_IMP def post_tm th
    val th = MP th TRUTH
    val s1 = "  val "^name^" = Q.SPEC post (MATCH_MP ARM_PROG_WEAKEN_POST1 "^name^")\n"
    val s2 = "  val "^name^" = MP (RAND_SIMP_SEP_IMP2 def "^name^") TRUTH\n"
    in (true,(name,false,th,strs @ [s1,s2])) end 
    handle e => (false,(name,false,TRUTH,[]))
  val thms = map weak thms
  val l = length thms  
  val thms = map snd (filter fst thms)  
  val _ = if length thms < l then 
    print ("Dropped "^int_to_string (l - length thms)^" postconditions.\n") 
    else ()
  (* strengthen pres in all cases *)
  fun strength (name,b,th,strs) = let
    val th = PRE_CONV_RULE (ONCE_REWRITE_CONV [STAR_COMM]) th
    val th = ISPEC pre_tm (MATCH_MP ARM_PROG_PART_STRENGTHEN_PRE th)
    val lemma = prove((fst o dest_imp o concl) th,  
      SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
    val th = MATCH_MP th lemma
    val th = PRE_CONV_RULE (ONCE_REWRITE_CONV [STAR_COMM]) th
    val str1 = ["  val "^name^" = PRE_CONV_RULE (ONCE_REWRITE_CONV [STAR_COMM]) "^name^"\n"]
    val str2 = ["  val "^name^" = APP_PART_STRENGTHEN "^name^" pre (SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])\n"]
    val str3 = ["  val "^name^" = RW [EVAL ``1+1``] "^name^"\n"] 
    val (th,str3) = if b then (RW [EVAL ``1+1``] th,str3) else (th,[]) 
    in (name,b,th,strs @ str1 @ str2 @ str1 @ str3) end
  val thms = map strength thms
  in thms end;

fun merge_base_cases thms strs = let
  val bases = filter (fn (name,b,th,strs) => not b) thms
  val steps = filter (fn (name,b,th,strs) => b) thms
  fun f ((name1,b1,th1,strs1),(name2,b2,th2,strs2)) = let
    val th = APP_MERGE th1 th2
    val strs = strs1 @ strs2 @ ["  val "^name2^" = APP_MERGE "^name1^" "^name2^"\n"]
    in (name2,b1,th,strs) end    
  val (name,_,th,s1) = foldr f (last bases) (butlast bases)
  val spec = (concl o UNDISCH o RW [ARM_PROG_MOVE_COND]) th
  val s2 = ["  val spec = concl (UNDISCH (RW [ARM_PROG_MOVE_COND] "^name^"))\n"]
  val s2 = if length steps = 0 then [] else s2
  val th = RW [EVAL ``1+1``] th 
  val s3 = ["  val "^name^" = RW [EVAL ``1+1``] "^name^"\n"] 
  fun f ((name,_,th,strs1),(xs,strs2)) = (xs @ [(name,th)], strs2 @ strs1)
  val (steps,s4) = foldl f ([],[]) steps
  in ((name,th),steps,spec,strs @ s1 @ s2 @ s3 @ s4) end;
      
val EXPAND_PAIR = prove(
  ``!x y z. ((x,y) = z) = (x = FST z) /\ (y = SND z)``,
  Cases_on `z` \\ REWRITE_TAC [PAIR_EQ,FST,SND]);

fun instatiate_induction spec def ind s ind_str = let
  val pair = (snd o dest_comb o fst o dest_eq o concl) def
  val s = s @ ["  val pair = (snd o dest_comb o fst o dest_eq o concl) def\n"]
  val spec = (PairRules.UNPBETA_CONV pair spec)
  val s = s @ ["  val spec = (PairRules.UNPBETA_CONV pair spec)\n"]
  val spec = (fst o dest_comb o snd o dest_eq o concl) spec
  val s = s @ ["  val spec = (fst o dest_comb o snd o dest_eq o concl) spec\n"]
  val th = ISPEC spec (RW [EXPAND_PAIR] ind)
  val s = s @ ["  val ind = ISPEC spec (RW [EXPAND_PAIR] "^ind_str^")\n"]
  val th = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) th
  val s = s @ ["  val ind = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) ind\n"]
  val th = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) th
  val s = s @ ["  val ind = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) ind\n"]
  in (th,s) end;

fun extract_ind_hyps ind s = let
  val asm = RW [GSYM ARM_PROG_MOVE_COND] (extract_assum ind)
  val s = s @ ["  val asm = RW [GSYM ARM_PROG_MOVE_COND] (extract_assum ind)\n"]  
  fun extract_conjuncts th name prev_name i thms s = let
    val (th1,th2) = (CONJUNCT1 th, CONJUNCT2 th)
    val name1 = name^int_to_string i
    val name2 = name^int_to_string (i+1)
    val s = s @ ["  val ("^name1^","^name2^
                 ") = (CONJUNCT1 "^prev_name^",CONJUNCT2 "^prev_name^")\n"]
    in extract_conjuncts th2 name name2 (i+1) (thms @ [(name1,th1)]) s end 
    handle e => (thms @ [(name^int_to_string i,th)],s)
  val (hyps,s) = extract_conjuncts asm "a" "asm" 1 [] s
  val s = if length hyps = 1 then s @ ["  val a1 = asm\n"] else s
  in (hyps,s) end;

val ARM_PROG_COMPOSE_I = prove(  (* delete *)
  ``!P code C1 C2 Q1 Q2 Q4 Q5 Q6 Z1 Z2.
         ARM_PROG (Q2 * Q6) code C2 Q4 Z2 ==>
         ARM_PROG P code C1 Q1 ((Q2 * Q5,I) INSERT Z1) ==>
         SEP_IMP Q5 Q6 ==>
         ARM_PROG P code (C1 UNION C2) (Q1 \/ Q4) (Z1 UNION Z2)``,
  METIS_TAC [arm_progTheory.ARM_PROG_COMPOSE_I]);

fun dest_eq_genvar tm = let
  val (x,y) = dest_eq tm
  fun is_genvar v = let
    val st = (fst o dest_var) v
    in substring(st,0,10) = "%%genvar%%" end handle e => false
  val xs = filter is_genvar (free_vars x)
  val ys = filter is_genvar (free_vars y)
  in if length xs < length ys then
    fst (match_term y x) else fst (match_term x y) end;

fun FIND_INST th = let 
  val cc = SIMP_CONV bool_ss [SEP_IMP_cond,WORD_CMP_NORMALISE,GSYM CONJ_ASSOC]
  val th = CONV_RULE (RATOR_CONV (RAND_CONV cc)) th
  fun g tm = let
    val tm = (fst o dest_imp o concl) th
    val tm = (snd o dest_imp) tm handle e => tm
    val tm = (fst o dest_conj) tm handle e => tm
    in tm end
  in (let val (x,y) = dest_eq (g th)
      in FIND_INST (INST [x|->y] th) end) handle e => 
     (let val (y,x) = dest_eq (g th)
      in FIND_INST (INST [x|->y] th) end) handle e => 
     FIND_INST (INST (dest_eq_genvar (g th)) th) handle e =>
     th end;

fun weak_decide_implies tm1 tm2 = let
  val cc = REWRITE_CONV [WORD_CMP_NORMALISE,CONJ_ASSOC]
  val cc = cc THENC REWRITE_CONV [GSYM AND_IMP_INTRO]
  val cc = cc THENC SIMP_CONV bool_ss [] 
  val tm = mk_imp(tm1,tm2)
  val tm = (snd o dest_eq o concl o QCONV cc) tm
  in (tm = T,tm) end;

fun stronger_decide_implies tm1 tm2 = let
  val tm = snd (weak_decide_implies tm1 tm2)
  val th = METIS_PROVE [] tm
  in true end handle e => false;

fun find_case tm cases = let
  val xs = filter (fn (c,x) => fst (weak_decide_implies tm c)) cases
  in snd (hd xs) end handle e => let
  val xs = filter (fn (c,x) => stronger_decide_implies tm c) cases
  in snd (hd xs) end;

fun prove_step_cases post_tm hyps steps def strs = let
(*
  val (name,th) = hd (hyps)
*)
  fun f (name,th) = let
    val th = DUPLICATE_COND (RW [GSYM ARM_PROG_MOVE_COND] (SPEC_ALL th))
    val temp = RW [ARM_PROG_MOVE_COND,AND_IMP_INTRO] th
    val tm = (fst o dest_imp o concl) temp
    val (p,_,_,_,_) = dest_ARM_PROG (concl (UNDISCH_ALL temp))
    val ps = map get_sep_domain (list_dest_STAR p)
    fun extract_case (name,th) = let
      val (_,_,_,_,q) = dest_ARM_PROG (concl th) 
      val q = (snd o dest_comb o fst o dest_comb) q
      val q = (snd o dest_comb o snd o dest_STAR o fst o dest_pair) q
      in (q,(name,th)) end
    val cases = map extract_case steps
    val (name2,th2) = find_case tm cases 
    val th = SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_PREL_TERM ps th)
    val th2 = SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_POSTL_TERM ps th2)
    val th = MATCH_MP ARM_PROG_COMPOSE_I th 
    val th = MATCH_MP th th2

    val th = MP (FIND_INST th) TRUTH
    val th = SIMP_RULE (bool_ss++sep_ss) [UNION_IDEMPOT] th
    val th = ISPEC post_tm (MATCH_MP ARM_PROG_WEAKEN_POST1 th)
    val th = MP (RAND_SIMP_SEP_IMP2 def th) TRUTH  
    val s1  = "  val "^name^" = DUPLICATE_COND (RW [GSYM ARM_PROG_MOVE_COND] (SPEC_ALL "^name^"))\n"
    val s2  = "  val ps = ["^list_to_string (fn tm => "`" ^ term_to_string tm ^ "`") ps "," ^"]\n"
    val s3  = "  val "^name^" = SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_PREL ps "^name^")\n"
    val s4  = "  val "^name2^" = SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_POSTL ps "^name2^")\n"
    val s5  = "  val "^name^" = MATCH_MP ARM_PROG_COMPOSE_I "^name^"\n" 
    val s6  = "  val "^name^" = MATCH_MP "^name^" "^name2^"\n"
    val s7  = "  val "^name^" = MP (FIND_INST "^name^") TRUTH\n"
    val s8  = "  val "^name^" = SIMP_RULE (bool_ss++sep_ss) [UNION_IDEMPOT] "^name^"\n"
    val s9  = "  val "^name^" = Q.SPEC post (MATCH_MP WEAKEN1_LEMMA "^name^")\n"
    val s10 = "  val "^name^" = MP (RAND_SIMP_SEP_IMP2 def "^name^") TRUTH\n"  
    in (name,th,[s1,s2,s3,s4,s5,s6,s7,s8,s9,s10]) end
  val xs = map f hyps
  fun g ((name,th,strs),(thms,strs2)) = (thms @ [(name,th)],strs2 @ strs)   
  in foldl g ([],strs) xs end;

(*
val (name,th) = base
val s = []
*)

fun merge_all_cases (name,th) hyps ind s = let
  val th = foldr (uncurry APP_MERGE) th (map snd hyps)
  val st = "(foldr (uncurry APP_MERGE) "
  val st = st ^ name ^ " [" ^ list_to_string (fn x => x) (map fst hyps) "," ^ "])"  
  val st = if length(hyps) = 0 then name else st
  val th = RW [ARM_PROG_MOVE_COND,INSERT_UNION_EQ,UNION_EMPTY,INSERT_INSERT] th
  val s = s @ ["  val th = RW [ARM_PROG_MOVE_COND,INSERT_UNION_EQ,UNION_EMPTY,INSERT_INSERT] "^st^"\n"]
  val (th,s) = let
    val tac = REWRITE_TAC [GSYM WORD_NOT_LESS_EQUAL,GSYM WORD_NOT_LOWER_EQUAL] \\ METIS_TAC []
    val th = MP th (prove((fst o dest_imp o concl) th, tac))
    val s = s @ ["  val th = RW [ARM_PROG_MOVE_COND] "^st^"\n"]
    val s = s @ ["  val tac = REWRITE_TAC [GSYM WORD_NOT_LESS_EQUAL,GSYM WORD_NOT_LOWER_EQUAL] THEN METIS_TAC []\n"]
    val s = s @ ["  val th = MP th (prove((fst o dest_imp o concl) th, tac))\n"]
    in (th,s) end handle e => (th,s)
  in if length(hyps) > 0 then let
    val xs = (fst o list_dest_forall o fst o dest_imp o concl) ind
    val s = s @ ["  val xs = (fst o list_dest_forall o fst o dest_imp o concl) ind\n"]
    val th = SPECL xs (MATCH_MP ind (GENL xs (DISCH_ALL th)))
    val s = s @ ["  val th = SPECL xs (MATCH_MP ind (GENL xs (DISCH_ALL th)))\n"]
    in (th,s) end else (th,s) end;

(* begin temporarily here *)

val ENCLOSE_STR_LDR_PC = let
  val assum = ASSUME
    ``ARM_PROG (P * R30 a x * ~R 14w * ~S) code C (Q * R30 a x * ~R 14w * ~S) {}``
  val th = (*  str r14,[a,#-4]!  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := F; Wb := T|>`,`a`|->`14w`,`b`|->`a`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1`] arm_STR_NONALIGNED))
  val th = ALIGN_VARS ["y1"] (AUTO_HIDE_STATUS th)
  val th = AUTO_HIDE_POST1 [`R 14w`] th
  val th = RW [WORD_ADD_SUB] (Q.INST [`y1`|->`x+1w`,`x1`|->`addr32 p`] th)
  val th = FRAME_COMPOSE th assum  
  val th1 = AUTO_HIDE_PRE [`M x`] th
  val th = (*  ldr r15,[a], #4  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`imm`|->`1w`,`x`|->`x1`,`y`|->`y1`] arm_LDR_PC))
  val th = RW [ADDR_MODE2_ADDR_def,ADDR_MODE2_WB_def] th
  val th = RW [EVAL ``<|Pre := F; Up := T; Wb := T|>.Pre``] th
  val th = RW [EVAL ``<|Pre := F; Up := T; Wb := T|>.Up``] th
  val th = RW [EVAL ``<|Pre := F; Up := T; Wb := T|>.Wb``] th
  val th = RW [EVAL ``(w2w (1w:word8) << 2):word12``,EVAL ``w2w (1w :word8) :word30``] th
  val th = ALIGN_VARS ["y1"] (AUTO_HIDE_STATUS th)
  val th = RW [WORD_ADD_SUB] (Q.INST [`y1`|->`p`,`x1`|->`x`] th)
  val th = FRAME_COMPOSE th1 th    
  val th = AUTO_HIDE_POST [`M x`] th
  val th = foldl (uncurry MOVE_POST) th [`R30 a`,`R 14w`,`M x`,`S`]  
  val th = foldl (uncurry MOVE_PRE) th [`R30 a`,`R 14w`,`M x`,`S`]  
  val th = DISCH_ALL (RW [GSYM R30_def] th)
  in th end;  

val HIDE1_xR_list = prove(
  ``ARM_PROG P code C (Q * xR_list (MAP (\x. (FST x, SOME (SND x))) xs)) Z ==>
    ARM_PROG P code C (Q * xR_list (MAP (\x. (FST x, NONE)) xs)) Z``,
  (MATCH_MP_TAC o GEN_ALL o RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_COMM] o 
   RW [AND_IMP_INTRO] o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL)
       ARM_PROG_PART_WEAKEN_POST1
  \\ Induct_on `xs` \\ REWRITE_TAC [MAP,SEP_IMP_REFL]
  \\ Cases \\ SIMP_TAC std_ss [MAP,xR_list_def]
  \\ MATCH_MP_TAC SEP_IMP_STAR \\ ASM_REWRITE_TAC []
  \\ SIMP_TAC std_ss [SEP_HIDE_THM,SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC []);

val ENCLOSE_STM_LDM = let
  val assum = ASSUME
    ``ARM_PROG (P * R30 a x * xR_list (MAP (\x. (FST x,NONE)) (xs:(word4 # word32) list)) * ~R 14w * ~S) 
        code C (Q * R30 a x * xR_list (MAP (\x. (FST x,NONE)) xs) * ~R 14w * ~S) {}``
  val th = Q.INST [`c_flag`|->`AL`,`a_mode`|->`am4_DB T`] arm_STM_R14
  val th = AUTO_HIDE_STATUS (FST_PROG2 (RW [PASS_CASES] th))
  val th = RW [ADDR_MODE4_ADDR_def,ADDR_MODE4_ADDR'_def,ADDR_MODE4_WB'_def,ADDR_MODE4_wb_def,ADDR_MODE4_WB_def,ADDR_MODE4_UP_def,LENGTH] th
  val th = Q.INST [`x`|->`x + n2w (SUC (LENGTH (xs:(word4 # word32) list)))`] th
  val th = RW [WORD_ADD_SUB] th
  val th = MOVE_STAR_RULE `a*x*mm*ss` `a*mm*ss*x` th
  val th = RW [blank_ms_EQ_blank] th
  val th = MATCH_MP HIDE1_xR_list th
  val th = SIMP_RULE std_ss [xR_list_def,MAP,FST,SND,STAR_ASSOC] th
  val th1 = FRAME_COMPOSE th assum
  val th = Q.INST [`c_flag`|->`AL`,`a_mode`|->`am4_IA T`] arm_LDM_PC
  val th = AUTO_HIDE_STATUS (FST_PROG2 (RW [PASS_CASES] th))
  val th = RW [ADDR_MODE4_ADDR_def,ADDR_MODE4_ADDR'_def,ADDR_MODE4_WB'_def,ADDR_MODE4_wb_def,ADDR_MODE4_WB_def,ADDR_MODE4_UP_def,LENGTH] th
  val th = MOVE_STAR_RULE `a*x*mm*ss` `a*mm*ss*x` th
  val th = RW [blank_ms_EQ_blank] th
  val th = FRAME_COMPOSE th1 th
  val th = MOVE_POST `ms x` th
  val th = RW [ADDR_MODE4_CMD_def] th
  val th = APP_PART_WEAKEN th 
    `blank_ms x (LENGTH (reg_values ((15w:word4,addr32 p)::xs)))`
    (REWRITE_TAC [SEP_IMP_ms_blank_ms])
  val th = RW [blank_ms_EQ_blank,LENGTH_reg_values,LENGTH] th
  val th = foldl (uncurry MOVE_POST) th [`R30 a`,`xR_list`,`R 14w`,`blank_ms x`,`S`]  
  val th = foldl (uncurry MOVE_PRE) th [`R30 a`,`xR_list`,`R 14w`,`blank_ms x`,`S`]  
  val th = DISCH_ALL (RW [GSYM R30_def] th)
  in th end;

fun MATCH_MP_ARM_PROG th1 th2 = let
  val ts1 = (list_dest_STAR o pre_ARM_PROG o fst o dest_imp o concl) th1
  val ts2 = (list_dest_STAR o pre_ARM_PROG o concl) th2
  (* which need to be framed in *)    
  val t1 = map (fn tm => (get_sep_domain tm,tm)) (tl ts1)
  val t2 = map get_sep_domain ts2
  val fi = map snd (filter (fn (tm,_) => not (mem tm t2)) t1)
  (* frame them in and update ts2 *)
  val th2 = if length fi = 0 then th2 else 
              ISPEC (list_mk_STAR fi) (MATCH_MP ARM_PROG_FRAME th2) 
  val th2 = RW [STAR_ASSOC,setSTAR_CLAUSES] th2
  (* arrange precondition *)
  val th2 = MOVE_PREL_TERM (map fst t1) th2
  (* arrange first postcondition *)
  fun arrange_post1 th2 = let
    val ts1 = (list_dest_STAR o post1_ARM_PROG o fst o dest_imp o concl) th1
    val t1 = map get_sep_domain (tl ts1)
    in MOVE_POST1L_TERM t1 th2 end handle e => th2   
  val th2 = arrange_post1 th2
  (* arrange second postcondition *)
  fun arrange_post th2 = let
    val ts1 = (list_dest_STAR o post_ARM_PROG o fst o dest_imp o concl) th1
    val t1 = map get_sep_domain (tl ts1)
    in MOVE_POSTL_TERM t1 th2 end handle e => th2   
  val th2 = arrange_post th2
  (* finalise *)
  val th2 = RW [STAR_ASSOC] th2
  in MATCH_MP th1 th2 end;

fun REMOVE_PRIMES th = let
  val ts = map dest_var (free_vars (concl th))
  val ts = map (fn (s,ty) => (ty,s,replace_char #"'" "" s)) ts
  val ts = filter (fn (ty,s1,s2) => not (s1 = s2)) ts
  val ts = map (fn (ty,s1,s2) => mk_var(s1,ty) |-> mk_var(s2,ty)) ts
  in INST ts th end;   

val ENCLOSE_STACK_ALTER_LEMMA = prove(
  ``!x n. addr32 x + w2w ((n2w (4 * n)):word8) = addr32 (x + n2w (n MOD 64))``,
  Cases_word \\ SIMP_TAC (arith_ss++SIZES_ss) 
    [addr32_n2w,word_add_n2w,word_mul_n2w,w2w_def,LEFT_ADD_DISTRIB,w2n_n2w]
  \\ SIMP_TAC arith_ss [MOD_COMMON_FACTOR]);

val ENCLOSE_STACK_ALTER = let
  val assum = ASSUME
    ``ARM_PROG (P * R30 13w sp * ~S) code C (Q * R30 13w sp * ~S) {}``
  val th = (*  sub sp,sp,#y  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (12w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`13w`,`a_mode`|->`Imm y`,`x`|->`sp`] arm_SUB1))
  val th = AUTO_HIDE_STATUS th
  val th = RW [WORD_ADD_SUB] (Q.INST [`sp`|->`sp + w2w (y:word8)`] th)
  val th = ALIGN_VARS ["sp"] th
  val th1 = FRAME_COMPOSE th assum    
  val th = (*  add sp,sp,#y  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (12w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`13w`,`a_mode`|->`Imm y`,`x`|->`sp`] arm_ADD1))
  val th = AUTO_HIDE_STATUS th
  val th = ALIGN_VARS ["sp"] th
  val th = FRAME_COMPOSE th1 th
  val th = MOVE_PRE `S` (MOVE_PRE `R 13w` th)
  val th = MOVE_POST1 `S` (MOVE_POST1 `R 13w` th)  
  val th = Q.INST [`y`|->`n2w (4 * n)`] th
  val th = RW [GSYM R30_def,ENCLOSE_STACK_ALTER_LEMMA] th
  in DISCH_ALL th end;


(* end temporarily here *)

val WORD_SUB_ADD_n2w = prove(
  ``!x m n. x - n2w n + n2w m :'a word = 
            x + n2w ((dimword(:'a) - n MOD dimword(:'a) + m) MOD dimword(:'a))``,
  REWRITE_TAC [word_sub_def,word_2comp_n2w,GSYM WORD_ADD_ASSOC,
    word_add_n2w,n2w_mod]);
  
val SIMPLIFY_WORD_ADD_n2w_CONV = 
  SIMP_CONV arith_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
  THENC SIMP_CONV (arith_ss++wordsLib.SIZES_ss) [WORD_SUB_ADD_n2w,WORD_ADD_0];

fun n_times 0 f x = x | n_times n f x = n_times (n-1) f (f x) 

fun alter_stack_pointer th 0 = th
  | alter_stack_pointer th steps = let
  val th = MATCH_MP_ARM_PROG ENCLOSE_STACK_ALTER th
  val th = INST [``n:num``|->numSyntax.term_of_int steps] th
  val th = SIMP_RULE arith_ss [APPEND] th
  val cc = (CONV_RULE SIMPLIFY_WORD_ADD_n2w_CONV o Q.INST [`sp`|->`sp-1w`])
  val th = n_times steps cc th  
  in th end;

fun append_return name th InLineCode strs = (th,strs)
  | append_return name th SimpleProcedure strs = let
  val th2 = Q.INST [`a`|->`14w`,`x`|->`lr`,`c_flag`|->`AL`] arm_MOV_PC
  val th2 = AUTO_HIDE_STATUS (FST_PROG2 th2)
  val (th,str) = find_composition (th,name) (th2,"ret")
  val s1 = "  val ret = Q.INST [`a`|->`14w`,`x`|->`lr`,`c_flag`|->`AL`] arm_MOV_PC\n"
  val s2 = "  val ret = AUTO_HIDE_STATUS (FST_PROG2 ret)\n"
  val s3 = "  val "^name^" = "^str^"\n"
  in (th,strs @ [s1,s2,s3]) end
  | append_return name th (PushProcedure ([],i)) strs = let
  val th = alter_stack_pointer th i
  val th1 = Q.INST [`a`|->`13w`,`x`|->`sp`] ENCLOSE_STR_LDR_PC  
  val th = MATCH_MP_ARM_PROG th1 th
  val th = RW [WORD_SUB_ADD] (Q.INST [`sp`|->`sp - 1w`] th)
  val th = CONV_RULE SIMPLIFY_WORD_ADD_n2w_CONV th
  val th = SIMP_RULE arith_ss [setADD_CLAUSES,pcADD_pcADD,APPEND,GSYM WORD_ADD_ASSOC] th
  val th = Q.INST [`p`|->`lr`] (RW [WORD_ADD_ASSOC] th)
  in (th,strs) end
  | append_return name th (PushProcedure (xs,i)) strs = let
  val th = alter_stack_pointer th i
  val th2 = ENCLOSE_STM_LDM
  val ty = (type_of o pre_ARM_PROG o fst o dest_imp o concl) th2
  fun f tm = ((snd o dest_comb o fst o dest_comb) tm, (snd o dest_comb) tm)
  val ys = map (f o name_to_term ty) xs
  val zs = map pairSyntax.mk_pair ys 
  val zs = listSyntax.mk_list (zs,``:word4 # word32``)
  val th2 = Q.INST [`a`|->`13w`,`x`|->`sp`] th2
  val th2 = INST [``xs:(word4 # word32) list``|->zs] th2
  val th2 = SIMP_RULE std_ss [MAP,FST,xR_list_def,emp_STAR,STAR_ASSOC] th2
  val qs = map fst ys
  val q14 = mk_comb(``reg_bitmap``,listSyntax.mk_list (``14w:word4``::qs,``:word4``))
  val q15 = mk_comb(``reg_bitmap``,listSyntax.mk_list (``15w:word4``::qs,``:word4``))
  val l14 = mk_comb(``wLENGTH:word4 list->word30``,listSyntax.mk_list (``15w:word4``::qs,``:word4``))
  val th2 = RW [EVAL q14,EVAL q15,LENGTH,blank_ms_def] th2
  val th2 = RW [STAR_ASSOC,emp_STAR,ADD1,ADD,GSYM word_add_n2w] th2
  val th2 = MATCH_MP_ARM_PROG th2 th   
  val th2 = REMOVE_PRIMES th2
  val th2 = INST [``sp1:word30``|->l14] (Q.INST [`sp`|->`sp-sp1`] th2)
  val th2 = SIMP_RULE bool_ss [wLENGTH_def,LENGTH,ADD1,GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_ADD] th2
  val th2 = SIMP_RULE arith_ss [GSYM WORD_SUB_PLUS,word_add_n2w] th2
  val th2 = CONV_RULE SIMPLIFY_WORD_ADD_n2w_CONV th2
  val th = SIMP_RULE arith_ss [setADD_CLAUSES,pcADD_pcADD,APPEND,GSYM WORD_ADD_ASSOC] th2
  val th = Q.INST [`p`|->`lr`] (RW [WORD_ADD_ASSOC] th)
  in (th,strs) end


(*val tm = ``(x INSERT y INSERT z INSERT s) UNION (x INSERT z INSERT t)``

fun set_delete_duplicates tm = let

 
val INSERT_UNION_EQ2 =
  GEN_ALL ((ONCE_REWRITE_CONV [UNION_COMM] THENC 
            REWRITE_CONV [INSERT_UNION_EQ]) ``t UNION (x INSERT s)``);

  REWRITE_CONV [INSERT_UNION_EQ,INSERT_UNION_EQ2] tm

val COMM = ASSUME ``!x:num y:num z:num list. f x (f y z) = f y (f x z)``

  INSERT_COMM

val tm = ``f x (f y (f 5 [1;2;3]))``    

  fun dest_f_f tm = 
   ((fst o dest_comb o fst o dest_comb) tm,
    (snd o dest_comb o fst o dest_comb) tm,
    (fst o dest_comb o fst o dest_comb o snd o dest_comb) tm,
    (snd o dest_comb o fst o dest_comb o snd o dest_comb) tm,
    (snd o dest_comb o snd o dest_comb) tm)
  val (f,_,g,_,_) = (dest_f_f o fst o dest_eq o concl o SPEC_ALL) COMM
  fun cmp_and_swap_conv tm =
    val (f1,x,f2,y,z) = dest_f_f tm
    

  fun dest_insert_set tm = let 
    val (x,y) = pred_setSyntax.dest_insert tm 
    in x :: filter (fn z => not (z = x)) (dest_insert_set y) end handle e => [];
  fun mk_insert_set [] ty = pred_setSyntax.mk_empty ty
    | mk_insert_set (x::xs) ty = pred_setSyntax.mk_insert(x,mk_insert_set xs ty)
  val ty = (hd o snd o dest_type o type_of) tm
  in mk_insert_set (dest_insert_set tm) ty end;
*)

val ARM_PROG_SUBSET_CODE = prove(
  ``!P code C1 Q Z.
      ARM_PROG P code C1 Q Z ==> !C2. C1 SUBSET C2 ==> ARM_PROG P code C2 Q Z``,
  REPEAT STRIP_TAC
  \\ `?X. C2 = C1 UNION X` by ALL_TAC << [ 
    Q.EXISTS_TAC `C2` \\ FULL_SIMP_TAC bool_ss [EXTENSION,IN_UNION,SUBSET_DEF] 
    \\ METIS_TAC [],
    ASM_REWRITE_TAC [] \\ MATCH_MP_TAC ARM_PROG_ADD_CODE \\ ASM_REWRITE_TAC []]);

fun collect_procedure_code thms strs = let
  val code = map (code_set_ARM_PROG o concl o snd) thms
  val code = foldr pred_setSyntax.mk_union ``{}:(word32 list # (word30->word30)) set`` code
  val cc = SIMP_CONV arith_ss [INSERT_UNION_EQ,UNION_EMPTY,GSYM WORD_ADD_ASSOC,word_add_n2w]
  val tm = (snd o dest_eq o concl o cc) code    
  fun f (name,th) = let
    val th = SPEC tm (MATCH_MP ARM_PROG_SUBSET_CODE th)
    val th = MATCH_MP th
     (prove((fst o dest_imp o concl) th,
        SIMP_TAC arith_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
        \\ SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_UNION] 
        \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC []))
    in (name,th) end;
  in (map f thms,strs) end;

fun build_definition name tm def_name tm_name = let
  fun g x = fn y => let
    val (x,y) = (fst (dest_var x),fst (dest_var y))
    in if size(x) = size(y) then (x < y) else size(x) < size(y) end 
  val xs = sort g (free_vars tm)
  val xs = map (fn x => "("^fst (dest_var x) ^ (type_to_string (snd (dest_var x)))^")") xs
  val str = foldl (fn (x,y) => y ^ " " ^ x) name xs
  val _ = Parse.hide name
  val str = "("^str^")" ^ type_to_string (type_of tm) 
  val tm = mk_eq(Parse.Term [QUOTE str],tm)
  val code_def = Define [ANTIQUOTE tm]
  val str = "  val "^def_name^" = Define [ANTIQUOTE (mk_eq(``"^str^"``,"^tm_name^"))]\n"
  in (code_def,str) end;

fun abbreviate_code name thms strs = 
  if not (!abbrev_code) then (thms,TRUTH,TRUTH,strs) else let
    val (n,th) = hd thms
    val tm1 = code_ARM_PROG (concl th)
    val tm2 = code_set_ARM_PROG (concl th)
    in if tm2 = ``{}:((word32 list) # (word30 -> word30)) set`` then let
      val (code1_def,str1) = build_definition (name^"_code1") tm1 "code1_def" "tm1"
      val _ = add_code_abbrevs code1_def NONE
      val strs = strs @ ["  val tm1 = code_ARM_PROG (concl "^n^")\n"] @ [str1] 
      val strs = strs @ ["  val _ = add_code_abbrevs code1_def NONE\n"]
      fun f (name,th) = 
        ((name,RW [GSYM code1_def] th),"  val "^name^" = RW [GSYM code1_def] "^name^"\n")
      val thms = map f thms
      val strs = strs @ map snd thms
      val thms = map fst thms
      in (thms,code1_def,TRUTH,strs) end else let     
      val (code1_def,str1) = build_definition (name^"_code1") tm1 "code1_def" "tm1"
      val (code2_def,str2) = build_definition (name^"_code2") tm2 "code2_def" "tm2"
      val _ = add_code_abbrevs code1_def (SOME code2_def)
      val strs = strs @ ["  val tm1 = code_ARM_PROG (concl "^n^")\n"]
      val strs = strs @ ["  val tm2 = code_set_ARM_PROG (concl "^n^")\n"]
      val strs = strs @ [str1] @ [str2] 
      val strs = strs @ ["  val _ = add_code_abbrevs code1_def (SOME code2_def)\n"]
      fun f (name,th) = 
        ((name,RW [GSYM code1_def,GSYM code2_def] th),
         "  val "^name^" = RW [GSYM code1_def,GSYM code2_def] "^name^"\n")
      val thms = map f thms
      val strs = strs @ map snd thms
      val thms = map fst thms
      in (thms,code1_def,code2_def,strs) end end;

fun calc_code_length th = let
  val tm = code_ARM_PROG (concl th)
  val tm = mk_comb(``LENGTH:word32 list -> num``,tm)
  val th2 = (code_length_conv()) tm
  in (numSyntax.int_of_term o snd o dest_eq o concl) th2 end;

val ARM_PROG_APPEND_CODE_SET = prove(
  ``ARM_PROG P cs1 {(cs2,pcADD x)} SEP_F Z ==>
    (wLENGTH cs1 = x) ==> ARM_PROG P (cs1 ++ cs2) {} SEP_F Z``,
  ONCE_REWRITE_TAC [ARM_PROG_EXTRACT_CODE]
  \\ ONCE_REWRITE_TAC [GSYM ARM_PROG_MERGE_CODE]
  \\ SIMP_TAC std_ss [pcINC_def]);

val ARM_PROG_EMPTY_CODE = prove(
  ``ARM_PROG P cs (([],f) INSERT C) Q Z = ARM_PROG P cs C Q Z``,
  REWRITE_TAC [ARM_PROG_THM] \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ REWRITE_TAC [ARM_GPROG_EMPTY_CODE]);

val ARM_PROG_PREPEND_CODE = prove(
  ``ARM_PROG P [] {(cs1,f)} Q Z ==> 
    !cs2. ARM_PROG P [] {(cs2 ++ cs1,pcADD (0w - wLENGTH cs2) o f)} Q Z``,
  REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o RW [INSERT_UNION_EQ,UNION_EMPTY] o RW1 [UNION_COMM] o Q.SPEC `{(cs2,pcADD (0w - wLENGTH cs2) o f)}` o MATCH_MP ARM_PROG_ADD_CODE)
  \\ ONCE_REWRITE_TAC [GSYM ARM_PROG_MERGE_CODE]
  \\ REWRITE_TAC [pcINC_def,pcADD_pcADD]
  \\ `!x:word30 f:word30->word30. pcADD x o pcADD (0w - x) o f = f` by
    (SIMP_TAC std_ss [FUN_EQ_THM,pcADD_def,WORD_SUB_LZERO,WORD_ADD_ASSOC]
     \\ REWRITE_TAC [GSYM word_sub_def,WORD_SUB_REFL,WORD_ADD_0])
  \\ ASM_REWRITE_TAC []);

val as_proc = (PushProcedure ([],0))
fun arm_compile def ind as_proc = let
  (* guess name *)
  val tm = (fst o dest_eq o concl o SPEC_ALL) def
  val name = (fst o dest_const) ((fst o dest_comb) tm handle e => tm)
  (* generate code with path traces *)
  val code = make_inst_list2 def
  (* generate basic specs for each path *)
  val (thms,strs) = make_passes_th code 
  (* collect procedure code *)
  val (thms,strs) = collect_procedure_code thms strs
  (* abbreviate the code using a definition *)
  val (thms,c1_def,c2_def,strs) = abbreviate_code name thms strs 
  (* normalise names and fill using frame *)
  val thms = rename_and_fill_preconditions thms def
  (* hide irrelevant pre and post elements *)  
  val thms = hide_pre_post_elements thms def 
  (* generate pre- and postconditions *)
  val (pre_tm,post_tm,strs) = get_pre_post_terms (name^"_def") thms def strs
  (* weaken posts, strengthen pres *)
  val def' = COMPILER_FORMAT_DEF def
  val thms = weaken_strengthen thms def' pre_tm post_tm
  (* merge base cases and separate step cases *)
  val (base,steps,spec,strs) = merge_base_cases thms strs
  (* instantiate induction, extract and prove step cases *)
  val (th,strs) =
    if length(steps) > 0 (* = function is recursive *) then let
      val (ind,strs) = instatiate_induction spec def' ind strs (name^"_ind")
      val (hyps,strs) = extract_ind_hyps ind strs    
      val (hyps,strs) = prove_step_cases post_tm hyps steps def' strs  
      val (th,strs) = merge_all_cases base hyps ind strs
      in (th,strs) end 
    else let
      val (th,strs) = merge_all_cases base [] TRUTH strs
      in (th,strs) end 
  (* insert procedure entry/exit code *)
  val (th,strs) = append_return "th" th as_proc strs 
  (* calculate code length *)
  val code_length = calc_code_length th
  (* format output *)
  val strs = map (fn s => "  "^s) strs 
  val strs = ["  val "^name^"_arm = let\n"] @ strs @ ["  in th end;\n"]
  val result = (name,th,as_proc,code_length,c1_def) 
  val _ = save_thm(name^"_arm",th)
  val _ = compiled_specs := result :: !compiled_specs
  in (th,strs) end

fun reset_compiled () = let
  val _ = compiled_specs := []
  val _ = code_length_rewrites := []
  val _ = offset_counter := 0
  val _ = code1_abbreviations := [];
  val _ = code2_abbreviations := [];
  in () end;

(* function for flattening the compiled code *)

val n2w_sw2sw_n2w = prove(
  ``!n m x. n2w n + sw2sw x + n2w m = sw2sw x + n2w (n + m)``,
  SIMP_TAC bool_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,GSYM word_add_n2w]);

val ARM_PROG_MERGE_CODE_pcADD = prove(
  ``ARM_PROG P code ((c1,pcADD x) INSERT (c2,pcADD y) INSERT C) Q Z ==>
    (wLENGTH c1 = y - x) ==>
    ARM_PROG P code ((c1 ++ c2,pcADD x) INSERT C) Q Z``,
  REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [GSYM ARM_PROG_MERGE_CODE,pcINC_def,pcADD_pcADD,WORD_SUB_ADD]);

fun SWAP_INSERT_CONV tm = let
  val (x,y) = pred_setSyntax.dest_insert tm  
  val (y,z) = pred_setSyntax.dest_insert y  
  in if x = y then ISPECL [x,z] INSERT_INSERT else let
  val (x1,x2) = dest_pair x
  val (y1,y2) = dest_pair y
  val x2 = (numSyntax.int_of_term o snd o dest_comb o snd o dest_comb) x2 
  val y2 = (numSyntax.int_of_term o snd o dest_comb o snd o dest_comb) y2 
  in if x2 < y2 then ALL_CONV tm else ISPECL [x,y,z] INSERT_COMM end end;

val SORT_INSERT_CONV = REPEATC (DEPTH_CONV SWAP_INSERT_CONV)

fun arm_flatten_code () = let
  fun not_inline (_,_,InLineCode,_,_) = false | not_inline _ = true
  val xs = (filter not_inline (!compiled_specs))
  val cs = map (fn (name,th,_,_,_) => (name,code_ARM_PROG (concl th),code_set_ARM_PROG (concl th))) xs
  (* calculate lengths *)
  fun get_length x = let
    val tm = mk_comb(``LENGTH:word32 list -> num``,x)
    val th = code_length_conv() tm
    in (numSyntax.int_of_term o snd o dest_eq o concl) th end
  val cs = map (fn (n,x,y) => (n,x,y,get_length x)) cs
  (* calculate positions *)
  fun calc_pos ((n,x,y,l),(i,xs)) = (i+l,xs @ [(n,x,y,l,i)])
  val cs = snd (foldl calc_pos (0,[]) cs)
  (* calculate offsets *)
  fun calc_offsets [] (offsets,evals) = (offsets,evals)
    | calc_offsets ((n,x,y,l,position)::xs) (offsets,evals) = let
    val cc = REWRITE_CONV (!code2_abbreviations)
    val cc = cc THENC SIMP_CONV (arith_ss++compose_ss)
            (evals @ [INSERT_UNION_EQ,UNION_EMPTY,GSYM WORD_ADD_ASSOC,word_add_n2w])
    val cc = cc THENC SIMP_CONV (arith_ss) [WORD_ADD_ASSOC,word_add_n2w,n2w_sw2sw_n2w,INSERT_INSERT]
    val tm = (snd o dest_eq o concl o QCONV cc o subst offsets) y
    fun find t [] = hd [] | find t ((n,x,y,u,i)::xs) =
      if t = subst offsets x then (n,x,y,u,i) else find t xs
    fun find_offsets tm = let
      val (v,rest) = pred_setSyntax.dest_insert tm
      val (code,v) = dest_pair v
      val (v,correct) = (dest_comb o snd o dest_comb) v
      val v = (snd o dest_comb o snd o dest_comb) v
      val (_,_,_,_,i) = find code cs
      val correct = (numSyntax.int_of_term o snd o dest_comb) correct
      val correct = numSyntax.term_of_int (correct + position)
      val i = numSyntax.term_of_int i
      val offset = subst [``n:num``|->i,``x:num``|->correct] ``n2w n - n2w x:word24``
      val offset = (snd o dest_eq o concl o EVAL) offset
      in (v,offset) :: find_offsets rest end handle e => [];
    fun remove_duplicates [] = []
      | remove_duplicates (x::xs) = x :: remove_duplicates (filter (fn y => not (x = y)) xs)
    val new_offsets = remove_duplicates (find_offsets tm)
    val evals = evals @ map (EVAL o curry mk_comb ``sw2sw:word24->word30`` o snd) new_offsets
    val offsets = offsets @ (map (fn (x,y) => x |-> y) new_offsets)
    in calc_offsets xs (offsets,evals) end
  val (offsets,evals) = calc_offsets (rev cs) ([],[])
  (* build composed code *)
  val form = ``(code:word32 list,pcADD ((n2w n):word30)) INSERT x``
  val empty = pred_setSyntax.mk_empty(hd(snd(dest_type(type_of form))))
  fun f ((n,tm,_,_,pos),x) =
    subst [``code:word32 list``|->tm,mk_var("x",type_of x) |-> x,
           ``n:num``|->numSyntax.term_of_int pos] form
  val code = foldr f empty cs
  val code = subst offsets code
  (* put the code into the theorems *)
  val ys = zip xs (map (fn (_,_,_,_,i) => i) cs)
  val ((n,th,p,l,lt),i) = hd ys
  fun f ((n,th,p,l,lt),i) = let
    val th = (INST offsets o RW [ARM_PROG_FALSE_POST] o EXTRACT_CODE) th
    val th = Q.SPEC `setADD (n2w (1073741824 - nnnnnnnnnn)) C1` (MATCH_MP ARM_PROG_SUBSET_CODE th)
    val th = SPEC code (Q.GEN `C1` th)
    val th = INST [``nnnnnnnnnn:num``|->numSyntax.term_of_int i] th
    val th = RW (!code2_abbreviations) th
    fun f cc th = CONV_RULE (RATOR_CONV (RAND_CONV cc)) th
    val th = f (REWRITE_CONV [INSERT_UNION_EQ,UNION_EMPTY,setADD_CLAUSES,pcADD_pcADD]) th    
    val th = f (REWRITE_CONV [GSYM WORD_ADD_ASSOC,word_add_n2w]) th    
    val th = f (REWRITE_CONV [n2w_sw2sw_n2w,WORD_ADD_ASSOC]) th
    val th = f (SIMP_CONV arith_ss (evals @ [word_add_n2w])) th
    val th = f (ONCE_REWRITE_CONV [INST_TYPE [``:'a``|->``:30``] (GSYM n2w_mod)]) th
    val th = f (SIMP_CONV (arith_ss++SIZES_ss) []) th
    val th = f SORT_INSERT_CONV th
    val th = f (REWRITE_CONV [INSERT_SUBSET,IN_INSERT,NOT_IN_EMPTY,EMPTY_SUBSET,pcADD_0]) th
    val th = MP th TRUTH
    in (n,th,p,l,lt) end
  (* merge the code *)
  fun merge_one (n,th,p,l,lt) = let
    val cc = REWRITE_CONV [setADD_CLAUSES,pcADD_pcADD,word_add_n2w]
    val cc = cc THENC ONCE_REWRITE_CONV [INST_TYPE [``:'a``|->``:30``] (GSYM n2w_mod)]
    val cc = cc THENC SIMP_CONV (arith_ss++SIZES_ss) []
    val th = CODE_CONV_RULE cc th
    fun merge_code th = let
      val th = MATCH_MP ARM_PROG_MERGE_CODE_pcADD th
      val cc = REWRITE_CONV [wLENGTH_def]
      val cc = cc THENC code_length_conv() THENC EVAL
      val th = MP (CONV_RULE (RATOR_CONV (RAND_CONV cc)) th) TRUTH
      in th end
    val th = repeat merge_code th
    val th = RW [pcADD_0,GSYM ARM_PROG_EXTRACT_CODE] th
    val th = RW ((!code1_abbreviations) @ [APPEND]) th
  in (n,th,p,l,lt) end (* can do: map (merge_one o f) ys *)
  val (_,th,_,_,_) = (merge_one o f) (hd ys)
  (* print the code *)
  val c = fst (listSyntax.dest_list(code_ARM_PROG (concl th)))
  val pos = map (fn (n,_,_,_,p) => (p,n)) cs
  fun inst_to_str tm = instructionSyntax.dest_instruction NONE (snd (dest_comb tm))
  val c = pad_strings (map inst_to_str c)
  fun find_pos i [] = hd []
    | find_pos i ((j,x)::xs) = if i = j then x else find_pos i xs
  fun add_names (st,(xs,i)) = let
    in (xs @ [st ^ "   ; procedure "^find_pos i pos],(i+1)) end
    handle e => (xs @ [st],i+1)
  val strs = fst (foldl add_names ([],0) c)
  val _ = print ("\n\ncode length: "^(int_to_string (length c)) ^ "\n")
  val _ = print "code:\n"
  val _ = map (fn st => print ("  "^st^"\n")) strs
  val _ = print "\n\n"
  in th end;



end;
