open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_ops";

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory; 
open combinTheory finite_mapTheory addressTheory;

open decompilerLib progTheory set_sepTheory helperLib;
open lisp_typeTheory lisp_invTheory lisp_gcTheory lisp_equalTheory;
open ppc_encodeLib x86_encodeLib;
open prog_armLib prog_ppcLib prog_x86Lib;

infix \\ 
val op \\ = op THEN;
val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12","r13"];
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val aLISP_def = Define `
  aLISP (a,limit) (x1,x2,x3,x4,x5,x6) = 
    SEP_EXISTS r3 r4 r5 r6 r7 r8 df f dm m dg g s.
     aR 3w r3 * aR 4w r4 * aR 5w r5 * aR 6w r6 * aR 7w r7 * aR 8w r8 * aR 10w a * 
     aMEMORY df f * aMEMORY dm m * aBYTE_MEMORY dg g *
       cond (lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,dm,m,dg,g))`;

val pLISP_def = Define `
  pLISP (a,limit) (x1,x2,x3,x4,x5,x6) = 
    SEP_EXISTS r3 r4 r5 r6 r7 r8 df f dm m dg g s.
     ~(pR 0w) * ~(pR 2w) * pR 3w r3 * pR 4w r4 * pR 5w r5 * pR 6w r6 * pR 7w r7 * pR 8w r8 * pR 10w a * 
     pMEMORY df f * pMEMORY dm m * pBYTE_MEMORY dg g *
       cond (lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,dm,m,dg,g))`;

val xLISP_def = Define `
  xLISP (a,limit) (x1,x2,x3,x4,x5,x6) = 
    SEP_EXISTS r3 r4 r5 r6 r7 r8 df f dm m dg g s.
     xR1 EAX r3 * xR1 ECX r4 * xR1 EDX r5 * xR1 EBX r6 * xR1 EDI r7 * xR1 ESI r8 * xR1 EBP a * 
     xMEMORY df f * xMEMORY dm m * xBYTE_MEMORY dg g *
       cond (lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,dm,m,dg,g))`;

fun x86_reg 1 = "eax" | x86_reg 2 = "ecx" | x86_reg 3 = "edx"
  | x86_reg 4 = "ebx" | x86_reg 5 = "edi" | x86_reg 6 = "esi" | x86_reg _ = hd []

val _ = set_echo 0;


(* automation *)

fun dest_sep_exists tm = let
  val (x,y) = dest_comb tm
  val _ = if (fst o dest_const) x = "SEP_EXISTS" then () else hd []
  in dest_abs y end;

fun dest_sep_cond tm = 
  if (fst o dest_const o fst o dest_comb) tm = "cond" 
  then snd (dest_comb tm) else hd [];

fun prove_spec th imp def pre_tm post_tm = let  
  val (m,p,_,q) = (dest_spec o concl o SPEC_ALL) th
  val tm = (cdr o concl o SPEC_ALL) def
  val tm = repeat (snd o dest_sep_exists) tm
  val fill = list_dest dest_star tm
  val res = list_dest dest_star p
  val res2 = filter (not o can dest_sep_cond) res 
  val fill2 = filter (not o can dest_sep_cond) fill 
  val res3 = map dest_comb (filter (not o can dest_sep_hide) res2)
  val fill3 = map dest_comb (filter (not o can dest_sep_hide) fill2)
  fun rename [] (y1,y2) = (y2,y2)
    | rename ((x1,x2)::xs) (y1,y2) = if x1 = y1 then (y2,x2) else rename xs (y1,y2)
  val s = map (fn (x,y) => x |-> y) (map (rename fill3) res3) 
  val th = INST s th  
  val th = UNDISCH_ALL (RW [SPEC_MOVE_COND] (SIMP_RULE (bool_ss++sep_cond_ss)  [] th))
  val (m,p,_,q) = (dest_spec o concl o SPEC_ALL) th
  val fill = list_dest dest_star tm
  val res = list_dest dest_star p
  val f = list_mk_star (filter (fn x => not (mem x res)) fill) (type_of (hd fill))
  val th = SPEC f (MATCH_MP SPEC_FRAME th)
  val pre = (fst o dest_imp o snd o dest_imp) (concl imp) handle e => ``T:bool``
  val (_,p,_,_) = dest_spec (concl (PURE_REWRITE_RULE [GSYM SPEC_MOVE_COND] (DISCH pre th)))
  val x = (snd o dest_star) p
  val th = SPEC x (MATCH_MP SPEC_FRAME th)
  val th = SPEC post_tm (MATCH_MP SPEC_WEAKEN th)
  val goal = (cdr o car o concl) th
  fun AUTO_EXISTS_TAC (asm,tm) = let
      fun ex tm = let
        val (v,tm) = dest_exists tm
        in v :: ex tm end handle e => []
      val xs = ex tm
      val x = hd (list_dest dest_conj (repeat (snd o dest_exists) tm))
      val assum = [``lisp_inv (Dot x1 x2,x2,x3,x4,x5,x6,limit)
        (w1,w2,w3,w4,w5,w6,a',x',xs',s,dm,m,dg,g)``,
       ``lisp_inv (x1,x2,x3,x4,x5,x6,limit)
        (r3,r4,r5,r6,r7,r8,a,df,f,s,dm,m,dg,g)``]
       val tm2 = hd (filter (can (match_term x)) asm) 
       val (s,_) = match_term x tm2
       val ys = map (subst s) xs
       fun exx [] = ALL_TAC | exx (x::xs) = EXISTS_TAC x THEN exx xs 
       in exx ys (asm,tm) end
  val lemma = prove(goal,
    REWRITE_TAC [STAR_ASSOC]
    \\ SIMP_TAC (std_ss++sep_cond_ss) []
    \\ REWRITE_TAC [SEP_IMP_MOVE_COND]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC (SIMP_RULE std_ss [] imp)
    \\ REPEAT (Q.PAT_ASSUM `xx ==> yy` (K ALL_TAC))
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ SIMP_TAC std_ss [def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ AUTO_EXISTS_TAC
    \\ FULL_SIMP_TAC std_ss []    
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ METIS_TAC [])
  val th = MATCH_MP th lemma
  val th = RW [GSYM SPEC_MOVE_COND] (DISCH_ALL th)
  val tm = (cdr o concl o SPEC_ALL) def
  fun ff tm = let val (x,y) = dest_sep_exists tm in x :: ff y end handle e => []
  val zs = ff tm
  fun gg [] th = th
    | gg (x::xs) th = gg xs (EXISTS_PRE [ANTIQUOTE x] th)
  val th = gg zs th
  val th = MATCH_MP SPEC_STRENGTHEN th
  val th = SPEC (mk_cond_star(pre_tm,pre)) th
  val goal = (cdr o car o concl) th
  val lemma = prove(goal,
    SIMP_TAC std_ss [def,SEP_CLAUSES]
    \\ SIMP_TAC (bool_ss++sep_cond_ss) []
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR]
    \\ REPEAT STRIP_TAC
    \\ AUTO_EXISTS_TAC    
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC (SIMP_RULE std_ss [] imp)
    \\ REPEAT (Q.PAT_ASSUM `xx ==> yy` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ METIS_TAC [])
  val th = MATCH_MP th lemma
  val th = RW [SEP_CLAUSES] th
  in th end;


(* cons *)

val ARM_LISP_CONS = save_thm("ARM_LISP_CONS",let  
  val th = arm_alloc_thm  
  val imp = lisp_inv_cons
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p * ~aS``
  val post_tm = ``aLISP (a,limit) (Dot x1 x2,x2,x3,x4,x5,x6) * aPC (p + 0x144w) * ~aS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("arm_alloc_code",mk_eq(``(arm_alloc_code:word32->(word32 # word32) set) p``,c))
  val res = RW [GSYM def] res
  in res end);

val PPC_LISP_CONS = save_thm("PPC_LISP_CONS",let  
  val th = RW [ppc_alloc_EQ] ppc_alloc_thm  
  val imp = lisp_inv_cons
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p * ~pS``
  val post_tm = ``pLISP (a,limit) (Dot x1 x2,x2,x3,x4,x5,x6) * pPC (p + 0x190w) * ~pS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("ppc_alloc_code",mk_eq(``(ppc_alloc_code:word32->(word32 # word32) set) p``,c))
  val res = RW [GSYM def] res
  in res end);

val X86_LISP_CONS = save_thm("X86_LISP_CONS",let  
  val th = RW [x86_alloc_EQ] x86_alloc_thm  
  val imp = lisp_inv_cons
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * ~xS``
  val post_tm = ``xLISP (a,limit) (Dot x1 x2,x2,x3,x4,x5,x6) * xPC (eip + 0x12Dw) * ~xS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("x86_alloc_code",mk_eq(``(x86_alloc_code:word32->(word32 # string list) set) eip``,c))
  val res = RW [GSYM def] res
  in res end);


(* equal *)

val ARM_LISP_EQUAL = save_thm("ARM_LISP_EQUAL",let  
  val th = arm_eq_thm  
  val imp = lisp_inv_equal
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p * ~aS``
  val post_tm = ``aLISP (a,limit) (LISP_EQUAL x1 x2,x2,x3,x4,x5,x6) * aPC (p + 0xA4w) * ~aS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("arm_equal_code",mk_eq(``(arm_equal_code:word32->(word32 # word32) set) p``,c))
  val res = RW [GSYM def] res
  in res end);

val PPC_LISP_EQUAL = save_thm("PPC_LISP_EQUAL",let  
  val th = RW [ppc_eq_EQ] ppc_eq_thm  
  val imp = lisp_inv_equal
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p * ~pS``
  val post_tm = ``pLISP (a,limit) (LISP_EQUAL x1 x2,x2,x3,x4,x5,x6) * pPC (p + 0xB8w) * ~pS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("ppc_equal_code",mk_eq(``(ppc_equal_code:word32->(word32 # word32) set) p``,c))
  val res = RW [GSYM def] res
  in res end);

val X86_LISP_EQUAL = save_thm("X86_LISP_EQUAL",let  
  val th = RW [x86_eq_EQ] x86_eq_thm  
  val imp = lisp_inv_equal
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * ~xS``
  val post_tm = ``xLISP (a,limit) (LISP_EQUAL x1 x2,x2,x3,x4,x5,x6) * xPC (eip + 0x8Fw) * ~xS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("x86_equal_code",mk_eq(``(x86_equal_code:word32->(word32 # string list) set) eip``,c))
  val res = RW [GSYM def] res
  in res end);


(* isDot and isSym *)

fun ARM_LISP_ISDOT i = let 
  val _ = print "a"
  val (arm_spec,_,sts,_) = arm_tools
  val ((th,_,_),_) = arm_spec ("E31"^(int_to_string (i+2))^"0003")
  val th = HIDE_POST_RULE ``aS1 sN`` th
  val th = HIDE_POST_RULE ``aS1 sC`` th
  val th = HIDE_POST_RULE ``aS1 sV`` th
  val th = HIDE_PRE_STATUS_RULE sts th
  val def = aLISP_def
  val imp = lisp_inv_test
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p * ~aS``
  val post_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC (p + 0x4w) * ~(aS1 sN) * aS1 sZ (isDot x) * ~(aS1 sC) * ~(aS1 sV)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val th = RW [ALIGNED_INTRO] th
  val th = RW [ALIGNED_def] th
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_ISDOT" ^ int_to_string i,result) end;

fun X86_LISP_ISDOT i = let 
  val _ = print "x"
  val s = "test " ^ (x86_reg i) ^ ", 3"
  val s = x86_encode s
  val (spec,_,sts,_) = x86_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``xS1 X_PF`` th
  val th = HIDE_POST_RULE ``xS1 X_SF`` th
  val th = HIDE_POST_RULE ``xS1 X_AF`` th
  val th = HIDE_POST_RULE ``xS1 X_OF`` th
  val th = HIDE_POST_RULE ``xS1 X_CF`` th
  val def = xLISP_def
  val imp = lisp_inv_test
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * ~xS``
  val post_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * xS1 X_ZF (SOME (isDot x)) * ~xS1 X_PF * ~xS1 X_SF * ~xS1 X_AF * ~xS1 X_OF * ~xS1 X_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``xPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``eip:word32`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_ISDOT" ^ int_to_string i,result) end;

fun PPC_LISP_ISDOT i = let 
  val _ = print "p"
  val s = "andi. 2, " ^ int_to_string (i+2) ^ ", 3"
  val s = ppc_encode s
  val (spec,_,sts,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x1w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x0w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x3w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CARRY)`` th handle e => th
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p * ~pS``
  val post_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC (p+4w) * pS1 (PPC_CR0 2w) (SOME (isDot(x))) * ~(pS1 PPC_CARRY) *
      ~pS1 (PPC_CR0 0x1w) * ~pS1 (PPC_CR0 0x0w) * ~pS1 (PPC_CR0 0x3w)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val imp = lisp_inv_test
  val th = HIDE_POST_RULE ``pR 2w`` th
  val th = HIDE_PRE_RULE ``pR 2w`` th
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_ISDOT" ^ int_to_string i,result) end;

val _ = map ARM_LISP_ISDOT [1,2,3,4,5,6]
val _ = map X86_LISP_ISDOT [1,2,3,4,5,6]
val _ = map PPC_LISP_ISDOT [1,2,3,4,5,6] 

fun ARM_LISP_ISSTR i = let 
  val (arm_spec,_,sts,_) = arm_tools
  val ((th,_,_),_) = arm_spec ("E31"^(int_to_string (i+2))^"0001")
  val th = HIDE_POST_RULE ``aS1 sN`` th
  val th = HIDE_POST_RULE ``aS1 sC`` th
  val th = HIDE_POST_RULE ``aS1 sV`` th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = RW [Q.SPEC `n2w n` WORD_AND_COMM] th
  val def = aLISP_def
  val imp = lisp_inv_test
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p * ~aS``
  val post_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC (p + 0x4w) * ~(aS1 sN) * aS1 sZ ~(isSym x) * ~(aS1 sC) * ~(aS1 sV)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_ISSTR" ^ int_to_string i,result) end;

fun X86_LISP_ISSTR i = let 
  val _ = print "x"
  val s = "test " ^ (x86_reg i) ^ ", 1"
  val s = x86_encode s
  val (spec,_,sts,_) = x86_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``xS1 X_PF`` th
  val th = HIDE_POST_RULE ``xS1 X_SF`` th
  val th = HIDE_POST_RULE ``xS1 X_AF`` th
  val th = HIDE_POST_RULE ``xS1 X_OF`` th
  val th = HIDE_POST_RULE ``xS1 X_CF`` th
  val def = xLISP_def
  val imp = lisp_inv_test
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * ~xS``
  val post_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * xS1 X_ZF (SOME ~(isSym x)) * ~xS1 X_PF * ~xS1 X_SF * ~xS1 X_AF * ~xS1 X_OF * ~xS1 X_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``xPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``eip:word32`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_ISSTR" ^ int_to_string i,result) end;

fun PPC_LISP_ISSTR i = let 
  val _ = print "p"
  val s = "andi. 2, " ^ int_to_string (i+2) ^ ", 1"
  val s = ppc_encode s
  val (spec,_,sts,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x1w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x0w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x3w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CARRY)`` th handle e => th
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p * ~pS``
  val post_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC (p+4w) * pS1 (PPC_CR0 2w) (SOME (~isSym(x))) * ~(pS1 PPC_CARRY) *
      ~pS1 (PPC_CR0 0x1w) * ~pS1 (PPC_CR0 0x0w) * ~pS1 (PPC_CR0 0x3w)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val imp = lisp_inv_test
  val th = HIDE_POST_RULE ``pR 2w`` th
  val th = HIDE_PRE_RULE ``pR 2w`` th
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_ISSTR" ^ int_to_string i,result) end;

val _ = map ARM_LISP_ISSTR [1,2,3,4,5,6]
val _ = map X86_LISP_ISSTR [1,2,3,4,5,6]
val _ = map PPC_LISP_ISSTR [1,2,3,4,5,6]


(* assign Sym "nil", Sym "t" *)

fun swap_thm 1 = lisp_inv_swap1
  | swap_thm 2 = lisp_inv_swap2
  | swap_thm 3 = lisp_inv_swap3
  | swap_thm 4 = lisp_inv_swap4
  | swap_thm 5 = lisp_inv_swap5
  | swap_thm 6 = lisp_inv_swap6
  | swap_thm _ = hd []

fun ARM_LISP_CONST (c,n,thc) i = let
  val _ = print "a"
  val s = "E3A0"^(int_to_string (i+2))^"00"^n
  val (spec,_,_,_) = arm_tools
  val ((th,_,_),_) = spec s
  val imp = lisp_inv_move
  val def = aLISP_def
  val swap = swap_thm i
  val imp = DISCH_ALL (MATCH_MP swap (UNDISCH thc))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH swap))
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p``
  val post_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC (p + 4w)``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> c]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("0x" ^ n ^ "w:word32")]]
  val post_tm = cdr (concl (INST s (REFL post_tm)))
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (INST s (INST sw (REFL tm))))
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_CONST" ^ int_to_string i ^ n,result) end 

val ARM_LISP_CONST_NIL = ARM_LISP_CONST (``(Sym "nil"):SExp``, "3", lisp_inv_nil) 
val ARM_LISP_CONST_T = ARM_LISP_CONST (``(Sym "t"):SExp``, "F", lisp_inv_t) 
val _ = map ARM_LISP_CONST_NIL [1,2,3,4,5,6]
val _ = map ARM_LISP_CONST_T [1,2,3,4,5,6]

fun X86_LISP_CONST (c,n,thc) i = let
  val _ = print "x"
  val m = Arbnum.toString(Arbnum.fromHexString n)
  val s = "mov " ^ x86_reg i ^ ", " ^ m
  val s = x86_encode s
  val (spec,_,_,_) = x86_tools
  val ((th,_,_),_) = spec s
  val imp = lisp_inv_move
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6)``
  val post_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6)``
  val swap = swap_thm i
  val imp = DISCH_ALL (MATCH_MP swap (UNDISCH thc))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH swap))
  val pre_tm = mk_star(pre_tm, (snd o dest_star o cdr o car o car o concl) th)
  val post_tm = mk_star(post_tm, (snd o dest_star o cdr o concl) th)
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> c]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("0x" ^ n ^ "w:word32")]]
  val post_tm = cdr (concl (INST s (REFL post_tm)))
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (INST s (INST sw (REFL tm))))
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_CONST" ^ int_to_string i ^ n,result) end 

val X86_LISP_CONST_NIL = X86_LISP_CONST (``(Sym "nil"):SExp``, "3", lisp_inv_nil) 
val X86_LISP_CONST_T = X86_LISP_CONST (``(Sym "t"):SExp``, "F", lisp_inv_t) 
val _ = map X86_LISP_CONST_NIL [1,2,3,4,5,6]
val _ = map X86_LISP_CONST_T [1,2,3,4,5,6]

fun PPC_LISP_CONST (c,n,thc) i = let
  val _ = print "p"
  val m = Arbnum.toString(Arbnum.fromHexString n)
  val s = "addi " ^ int_to_string (i+2) ^ ", 0, " ^ m
  val s = ppc_encode s
  val (spec,_,_,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val th = RW [WORD_OR_CLAUSES] th
  val def = pLISP_def
  val swap = swap_thm i
  val imp = DISCH_ALL (MATCH_MP swap (UNDISCH thc))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH swap))
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p``
  val post_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC (p + 4w)``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> c]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("0x" ^ n ^ "w:word32")]]
  val post_tm = cdr (concl (INST s (REFL post_tm)))
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (INST s (INST sw (REFL tm))))
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_CONST" ^ int_to_string i ^ n,result) end 

val PPC_LISP_CONST_NIL = PPC_LISP_CONST (``(Sym "nil"):SExp``, "3", lisp_inv_nil) 
val PPC_LISP_CONST_T = PPC_LISP_CONST (``(Sym "t"):SExp``, "F", lisp_inv_t) 
val _ = map PPC_LISP_CONST_NIL [1,2,3,4,5,6]
val _ = map PPC_LISP_CONST_T [1,2,3,4,5,6]


(* move *)

fun ARM_LISP_MOVE (i,j) = let
  val _ = print "a"
  val inst = "E1A0"^(int_to_string (i+2))^"00"^(int_to_string (j+2))
  val (spec,_,_,_) = arm_tools
  val ((th,_,_),_) = spec inst
  val imp = lisp_inv_move
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p``
  val post_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC (p + 4w)``
  val s = [[QUOTE ("x" ^ int_to_string i)] |-> [QUOTE ("x" ^ int_to_string j)]]
  val sw = [[QUOTE ("w" ^ int_to_string i)] |-> [QUOTE ("w" ^ int_to_string j)]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val imp = prove(mk_imp(tm,tm2),METIS_TAC [imp])  
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_MOVE" ^ int_to_string i ^ int_to_string j,result) end 

fun X86_LISP_MOVE (i,j) = let
  val _ = print "x"
  val s = "mov " ^ x86_reg i ^ ", " ^ x86_reg j
  val s = x86_encode s
  val (spec,_,_,_) = x86_tools
  val ((th,_,_),_) = spec s
  val imp = lisp_inv_move
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6)``
  val post_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6)``
  val pre_tm = mk_star(pre_tm, (snd o dest_star o cdr o car o car o concl) th)
  val post_tm = mk_star(post_tm, (snd o dest_star o cdr o concl) th)
  val s = [[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> [QUOTE ("x" ^ int_to_string j)]]
  val sw = [[QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> [QUOTE ("w" ^ int_to_string j)]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val imp = prove(mk_imp(tm,tm2),METIS_TAC [imp])  
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_MOVE" ^ int_to_string i ^ int_to_string j,result) end 

fun PPC_LISP_MOVE (i,j) = let
  val _ = print "p"
  val s = "or " ^ int_to_string (i+2) ^ ", " ^ int_to_string (j+2) ^ ", " ^ int_to_string (j+2)
  val s = ppc_encode s
  val (spec,_,_,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val th = RW [WORD_OR_CLAUSES] th
  val imp = lisp_inv_move
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p``
  val post_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC (p+4w)``
  val s = [[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> [QUOTE ("x" ^ int_to_string j)]]
  val sw = [[QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> [QUOTE ("w" ^ int_to_string j)]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val imp = prove(mk_imp(tm,tm2),METIS_TAC [imp])  
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_MOVE" ^ int_to_string i ^ int_to_string j,result) end 

fun pairs x [] = [] | pairs x (y::ys) = (x,y) :: pairs x ys
fun cross [] ys = [] | cross (x::xs) ys = pairs x ys @ cross xs ys
val list = filter (fn (x,y) => not (x = y)) (cross [1,2,3,4,5,6] [1,2,3,4,5,6])
val _ = map ARM_LISP_MOVE list
val _ = map X86_LISP_MOVE list
val _ = map PPC_LISP_MOVE list


(* car *)

fun ARM_LISP_CAR (i,j) = let
  val _ = print "a"
  val inst = "E59"^(int_to_string (j+2))^(int_to_string (i+2))^"000"
  val (spec,_,_,_) = arm_tools
  val ((th,_,_),_) = spec inst
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p``
  val post_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC (p + 4w)``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> Term [QUOTE ("CAR x" ^ int_to_string j ^ ":SExp")]]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("(xs:word32->word32) w" ^ int_to_string j ^ ":word32")]]
  val post_tm = subst s post_tm
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = subst s (subst sw tm)
  val tm3 = Term [QUOTE ("isDot x" ^ int_to_string j)]
  val tm4 = Term [QUOTE ("w" ^ int_to_string j ^ " IN (x:word32 set) /\\ (w" ^ int_to_string j ^ " && 3w = 0w)")]
  val imp = prove(mk_imp(tm,mk_imp(tm3,mk_conj(tm2,tm4))),METIS_TAC [lisp_inv_car,lisp_inv_address])  
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_CAR" ^ int_to_string i ^ int_to_string j,result) end 

fun X86_LISP_CAR (i,j) = let
  val _ = print "x"
  val s = "mov " ^ x86_reg i ^ ", [" ^ x86_reg j ^ "]"
  val s = x86_encode s
  val (spec,_,_,_) = x86_tools
  val ((th,_,_),_) = spec s
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6)``
  val post_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6)``
  val pc1 = find_term (can (match_term ``xPC p``)) ((cdr o car o car o concl) th)
  val pc2 = find_term (can (match_term ``xPC p``)) ((cdr o concl) th)
  val pre_tm = mk_star(pre_tm,pc1)
  val post_tm = mk_star(post_tm,pc2)
  val s = [[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> [QUOTE ("CAR x" ^ int_to_string j)]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val sw = [[QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> [QUOTE ("(xs:word32->word32) w" ^ int_to_string j)]]
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val tm3 = Term [QUOTE ("isDot x" ^ int_to_string j)]
  val tm4 = Term [QUOTE ("w" ^ int_to_string j ^ " IN (x:word32 set) /\\ (w" ^ int_to_string j ^ " && 3w = 0w)")]
  val imp = prove(mk_imp(tm,mk_imp(tm3,mk_conj(tm2,tm4))),
    NTAC 2 STRIP_TAC
    \\ IMP_RES_TAC lisp_inv_car
    \\ IMP_RES_TAC lisp_inv_address
    \\ ASM_SIMP_TAC std_ss [])
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_CAR" ^ int_to_string i ^ int_to_string j,result) end 

fun PPC_LISP_CAR (i,j) = let
  val _ = print "p"
  val s = "lwz "^int_to_string(i+2)^",0("^int_to_string(j+2)^")"
  val s = ppc_encode s
  val (spec,_,_,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p``
  val post_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC (p+4w)``
  val s = [[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> [QUOTE ("CAR x" ^ int_to_string j)]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val sw = [[QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> [QUOTE ("(xs:word32->word32) w" ^ int_to_string j)]]
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val tm3 = Term [QUOTE ("isDot x" ^ int_to_string j)]
  val tm4 = Term [QUOTE ("w" ^ int_to_string j ^ " IN (x:word32 set) /\\ (w" ^ int_to_string j ^ " && 3w = 0w)")]
  val imp = prove(mk_imp(tm,mk_imp(tm3,mk_conj(tm2,tm4))),
    NTAC 2 STRIP_TAC
    \\ IMP_RES_TAC lisp_inv_car
    \\ IMP_RES_TAC lisp_inv_address
    \\ ASM_SIMP_TAC std_ss [])
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_CAR" ^ int_to_string i ^ int_to_string j,result) end 

val _ = map ARM_LISP_CAR (cross [1,2,3,4,5,6] [1,2,3,4,5,6])
val _ = map X86_LISP_CAR (cross [1,2,3,4,5,6] [1,2,3,4,5,6])
val _ = map PPC_LISP_CAR (cross [1,2,3,4,5,6] [1,2,3,4,5,6])


(* cdr *)

fun ARM_LISP_CDR (i,j) = let
  val _ = print "a"
  val inst = "E59"^(int_to_string (j+2))^(int_to_string (i+2))^"004"
  val (spec,_,_,_) = arm_tools
  val ((th,_,_),_) = spec inst
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p``
  val post_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC (p + 4w)``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> Term [QUOTE ("CDR x" ^ int_to_string j ^ ":SExp")]]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("(xs:word32->word32) (w" ^ int_to_string j ^ " + 4w):word32")]]
  val post_tm = subst s post_tm
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = subst s (subst sw tm)
  val tm3 = Term [QUOTE ("isDot x" ^ int_to_string j)]
  val tm4 = Term [QUOTE ("(w" ^ int_to_string j ^ " + 4w) IN (x:word32 set) /\\ ((w" ^ int_to_string j ^ " + 4w) && 3w = 0w)")]
  val imp = prove(mk_imp(tm,mk_imp(tm3,mk_conj(tm2,tm4))),
    REWRITE_TAC [ALIGNED_INTRO,ALIGNED_CLAUSES]
    \\ REWRITE_TAC [ALIGNED_def] \\ METIS_TAC [lisp_inv_cdr,lisp_inv_address])  
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_CDR" ^ int_to_string i ^ int_to_string j,result) end 

fun X86_LISP_CDR (i,j) = let
  val _ = print "x"
  val s = "mov " ^ x86_reg i ^ ", [" ^ x86_reg j ^ "+4]"
  val s = x86_encode s
  val (spec,_,_,_) = x86_tools
  val ((th,_,_),_) = spec s
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6)``
  val post_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6)``
  val pc1 = find_term (can (match_term ``xPC p``)) ((cdr o car o car o concl) th)
  val pc2 = find_term (can (match_term ``xPC p``)) ((cdr o concl) th)
  val pre_tm = mk_star(pre_tm,pc1)
  val post_tm = mk_star(post_tm,pc2)
  val s = [[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> [QUOTE ("CDR x" ^ int_to_string j)]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val sw = [[QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> [QUOTE ("(xs:word32->word32) (w" ^ int_to_string j ^ " + 4w)")]]
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val tm3 = Term [QUOTE ("isDot x" ^ int_to_string j)]
  val tm4 = Term [QUOTE ("w" ^ int_to_string j ^ " + 4w IN (x:word32 set) /\\ ((w" ^ int_to_string j ^ " + 4w) && 3w = 0w)")]
  val imp = prove(mk_imp(tm,mk_imp(tm3,mk_conj(tm2,tm4))),
    NTAC 2 STRIP_TAC
    \\ REWRITE_TAC [ALIGNED_INTRO,ALIGNED_CLAUSES]
    \\ REWRITE_TAC [ALIGNED_def]
    \\ IMP_RES_TAC lisp_inv_cdr
    \\ IMP_RES_TAC lisp_inv_address
    \\ ASM_SIMP_TAC std_ss [])
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_CDR" ^ int_to_string i ^ int_to_string j,result) end 

fun PPC_LISP_CDR (i,j) = let
  val _ = print "p"
  val s = "lwz "^int_to_string(i+2)^",4("^int_to_string(j+2)^")"
  val s = ppc_encode s
  val (spec,_,_,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p``
  val post_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC (p+4w)``
  val s = [[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> [QUOTE ("CDR x" ^ int_to_string j)]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val sw = [[QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> [QUOTE ("(xs:word32->word32) (w" ^ int_to_string j ^ " + 4w)")]]
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val tm3 = Term [QUOTE ("isDot x" ^ int_to_string j)]
  val tm4 = Term [QUOTE ("w" ^ int_to_string j ^ " + 4w IN (x:word32 set) /\\ ((w" ^ int_to_string j ^ " + 4w) && 3w = 0w)")]
  val imp = prove(mk_imp(tm,mk_imp(tm3,mk_conj(tm2,tm4))),
    NTAC 2 STRIP_TAC
    \\ REWRITE_TAC [ALIGNED_INTRO,ALIGNED_CLAUSES]
    \\ REWRITE_TAC [ALIGNED_def]
    \\ IMP_RES_TAC lisp_inv_cdr
    \\ IMP_RES_TAC lisp_inv_address
    \\ ASM_SIMP_TAC std_ss [])
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_CDR" ^ int_to_string i ^ int_to_string j,result) end 

val _ = map ARM_LISP_CDR (cross [1,2,3,4,5,6] [1,2,3,4,5,6])
val _ = map X86_LISP_CDR (cross [1,2,3,4,5,6] [1,2,3,4,5,6])
val _ = map PPC_LISP_CDR (cross [1,2,3,4,5,6] [1,2,3,4,5,6])


(* add *)

val ARM_LISP_ADD = let 
  val (th,def) = decompile_arm "ha" `
    E0833004 (* add r3,r3,r4 *)
    E2433002 (* sub r3,r3,#2 *)`
  val th = SIMP_RULE std_ss [def,LET_DEF,SEP_CLAUSES] th
  val imp = lisp_inv_ADD
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p * ~aS``
  val post_tm = ``aLISP (a,limit) (LISP_ADD x1 x2,x2,x3,x4,x5,x6) * aPC (p + 0x8w) * ~aS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_ADD",result) end;  

val X86_LISP_ADD = let 
  val (th,def) = decompile_x86 "ha" `
    01C8   (* add eax,ecx *)
    83E802 (* sub eax,2 *)`
  val th = SIMP_RULE std_ss [def,LET_DEF,SEP_CLAUSES] th
  val imp = lisp_inv_ADD
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * ~xS``
  val post_tm = ``xLISP (a,limit) (LISP_ADD x1 x2,x2,x3,x4,x5,x6) * xPC (eip + 0x5w) * ~xS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_ADD",result) end;  

val PPC_LISP_ADD = let 
  val (th,def) = decompile_ppc "ha" `
    7C632214 (* add 3,3,4 *)
    3863FFFE (* addi 3,3,-2 *)`
  val th = SIMP_RULE std_ss [def,LET_DEF,SEP_CLAUSES] th
  val imp = lisp_inv_ADD
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p * ~pS``
  val post_tm = ``pLISP (a,limit) (LISP_ADD x1 x2,x2,x3,x4,x5,x6) * pPC (p + 0x8w) * ~pS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_ADD",result) end;  


(* sub *)

val ARM_LISP_SUB = let 
  val (th,def) = decompile_arm "ha" `
    E0433004 (* sub r3,r3,r4 *)
    E2833002 (* add r3,r3,#2 *)`
  val th = SIMP_RULE std_ss [def,LET_DEF,SEP_CLAUSES] th
  val imp = lisp_inv_SUB
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p * ~aS``
  val post_tm = ``aLISP (a,limit) (LISP_SUB x1 x2,x2,x3,x4,x5,x6) * aPC (p + 0x8w) * ~aS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_SUB",result) end;  

val X86_LISP_SUB = let 
  val (th,def) = decompile_x86 "ha" `
    29C8   (* sub eax,ecx *)
    83C002 (* add eax,2 *)`
  val th = SIMP_RULE std_ss [def,LET_DEF,SEP_CLAUSES] th
  val imp = lisp_inv_SUB
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * ~xS``
  val post_tm = ``xLISP (a,limit) (LISP_SUB x1 x2,x2,x3,x4,x5,x6) * xPC (eip + 0x5w) * ~xS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_SUB",result) end;  

val PPC_LISP_SUB = let 
  val (th,def) = decompile_ppc "ha" `
    7C641810 (* subfc 3,4,3 *)
    38630002 (* addi 3,3,2 *)`
  val th = SIMP_RULE std_ss [def,LET_DEF,SEP_CLAUSES] th
  val imp = lisp_inv_SUB
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p * ~pS``
  val post_tm = ``pLISP (a,limit) (LISP_SUB x1 x2,x2,x3,x4,x5,x6) * pPC (p + 0x8w) * ~pS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_SUB",result) end;  


(* less *)

val ARM_LISP_LESS = let 
  val (arm_spec,_,sts,_) = arm_tools
  val ((th,_,_),_) = arm_spec "E1530004"
  val imp = lisp_inv_LESS
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = RW1 [EQ_SYM_EQ] imp
  val th = RW [GSYM WORD_NOT_LOWER] th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``aS1 sN`` th
  val th = HIDE_POST_RULE ``aS1 sZ`` th
  val th = HIDE_POST_RULE ``aS1 sV`` th
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p * ~aS``
  val post_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC (p + 0x4w) * ~(aS1 sN) * ~(aS1 sZ) * aS1 sC ~(LISP_LESS x1 x2) * ~(aS1 sV)``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_LESS",result) end;

val X86_LISP_LESS = let 
  val s = x86_encode "cmp eax,ecx"
  val (spec,_,sts,_) = x86_tools
  val ((th,_,_),_) = spec s
  val imp = lisp_inv_LESS
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = RW1 [EQ_SYM_EQ] imp
  val th = RW [GSYM WORD_NOT_LOWER] th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``xS1 X_PF`` th
  val th = HIDE_POST_RULE ``xS1 X_SF`` th
  val th = HIDE_POST_RULE ``xS1 X_AF`` th
  val th = HIDE_POST_RULE ``xS1 X_OF`` th
  val th = HIDE_POST_RULE ``xS1 X_ZF`` th
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * ~xS``
  val post_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC (eip + 0x2w) * ~(xS1 X_AF) * ~(xS1 X_OF) *
        ~(xS1 X_SF) * ~(xS1 X_ZF) * ~(xS1 X_PF) * xS1 X_CF (SOME (LISP_LESS x1 x2))``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_LESS",result) end;

val PPC_LISP_LESS = let 
  val s = ppc_encode "cmplw 3,4"
  val (spec,_,sts,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val imp = lisp_inv_LESS
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = RW1 [EQ_SYM_EQ] imp
  val th = RW [GSYM WORD_NOT_LOWER] th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x1w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x2w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x3w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CARRY)`` th handle e => th
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p * ~pS``
  val post_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC (p + 0x4w) * 
    pS1 (PPC_CR0 0x0w) (SOME (LISP_LESS x1 x2)) * ~pS1 PPC_CARRY *
    ~pS1 (PPC_CR0 0x1w) * ~pS1 (PPC_CR0 0x2w) * ~pS1 (PPC_CR0 0x3w)``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_LESS",result) end;


(* test eq *)

val ARM_LISP_EQ = let 
  val _ = print "a"
  val i = 1
  val j = 2
  val (arm_spec,_,sts,_) = arm_tools
  val inst = "E13"^(int_to_string (i+2))^"000"^(int_to_string (j+2))
  val ((th,_,_),_) = arm_spec inst
  val th = RW [WORD_EQ_XOR_ZERO] th
  val th = HIDE_POST_RULE ``aS1 sN`` th
  val th = HIDE_POST_RULE ``aS1 sC`` th
  val th = HIDE_POST_RULE ``aS1 sV`` th
  val th = HIDE_PRE_STATUS_RULE sts th
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p * ~aS``
  val post_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC (p + 0x4w) * ~(aS1 sN) * aS1 sZ (x = y:SExp) * ~(aS1 sC) * ~(aS1 sV)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``y:SExp``|->Term [QUOTE ("x" ^ int_to_string j ^ ": SExp")]] post_tm
  val imp = lisp_inv_eq
  val imp = RW [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_EQ" ^ (int_to_string i) ^ (int_to_string j),result) end;

val X86_LISP_EQ = let 
  val _ = print "x"
  val i = 1
  val j = 2
  val s = "cmp " ^ (x86_reg i) ^ ", " ^ (x86_reg j)
  val s = x86_encode s
  val (spec,_,sts,_) = x86_tools
  val ((th,_,_),_) = spec s
  val th = RW [WORD_EQ_SUB_ZERO] th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``xS1 X_PF`` th
  val th = HIDE_POST_RULE ``xS1 X_SF`` th
  val th = HIDE_POST_RULE ``xS1 X_AF`` th
  val th = HIDE_POST_RULE ``xS1 X_OF`` th
  val th = HIDE_POST_RULE ``xS1 X_CF`` th
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * ~xS``
  val post_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * xS1 X_ZF (SOME (x = y:SExp)) * ~xS1 X_PF * ~xS1 X_SF * ~xS1 X_AF * ~xS1 X_OF * ~xS1 X_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``y:SExp``|->Term [QUOTE ("x" ^ int_to_string j ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``xPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``eip:word32`` |-> cdr tm] post_tm
  val imp = lisp_inv_eq
  val imp = RW [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_EQ" ^ (int_to_string i) ^ (int_to_string j),result) end;

val PPC_LISP_EQ = let 
  val _ = print "p"
  val i = 1
  val j = 2
  val s = "cmpw " ^ (int_to_string (i+2)) ^ ", " ^ (int_to_string (j+2))
  val s = ppc_encode s
  val (spec,_,sts,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val th = RW [WORD_EQ_SUB_ZERO] th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x1w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x0w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x3w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CARRY)`` th handle e => th
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p * ~pS``
  val post_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC (p+4w) * pS1 (PPC_CR0 2w) (SOME (x = y:SExp)) * ~(pS1 PPC_CARRY) *
      ~pS1 (PPC_CR0 0x1w) * ~pS1 (PPC_CR0 0x0w) * ~pS1 (PPC_CR0 0x3w)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``y:SExp``|->Term [QUOTE ("x" ^ int_to_string j ^ ": SExp")]] post_tm
  val imp = lisp_inv_eq
  val imp = RW [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_EQ" ^ (int_to_string i) ^ (int_to_string j),result) end;


(* test symbol *)

fun ARM_LISP_EQ_SYMBOL (j,str) = let 
  val _ = print "a"
  val i = 2
  val (arm_spec,_,sts,_) = arm_tools
  val s = Arbnum.toHexString(Arbnum.fromInt j)
  val s = if size(s) < 2 then "0" ^ s else s
  val ((th,_,_),_) = arm_spec ("E33"^(int_to_string (i+2))^"00"^s)
  val th = RW [WORD_EQ_XOR_ZERO] th
  val th = HIDE_POST_RULE ``aS1 sN`` th
  val th = HIDE_POST_RULE ``aS1 sC`` th
  val th = HIDE_POST_RULE ``aS1 sV`` th
  val th = HIDE_PRE_STATUS_RULE sts th
  val def = aLISP_def
  val pre_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC p * ~aS``
  val post_tm = ``aLISP (a,limit) (x1,x2,x3,x4,x5,x6) * aPC (p + 0x4w) * ~(aS1 sN) * aS1 sZ (x = Sym str) * ~(aS1 sC) * ~(aS1 sV)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``str:string`` |-> (stringSyntax.fromMLstring str)] post_tm
  val imp = DISCH_ALL (MATCH_MP lisp_inv_builtin (UNDISCH lisp_inv_swap2))
  val imp = RW1 [EQ_SYM_EQ] imp
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_SYMBOL" ^ (int_to_string j),result) end;

fun X86_LISP_EQ_SYMBOL (j,str) = let 
  val _ = print "x"
  val i = 2
  val s = "cmp " ^ (x86_reg 2) ^ ", " ^ int_to_string j
  val s = x86_encode s
  val (spec,_,sts,_) = x86_tools
  val ((th,_,_),_) = spec s
  val th = RW [WORD_EQ_SUB_ZERO] th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``xS1 X_PF`` th
  val th = HIDE_POST_RULE ``xS1 X_SF`` th
  val th = HIDE_POST_RULE ``xS1 X_AF`` th
  val th = HIDE_POST_RULE ``xS1 X_OF`` th
  val th = HIDE_POST_RULE ``xS1 X_CF`` th
  val def = xLISP_def
  val pre_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * ~xS``
  val post_tm = ``xLISP (a,limit) (x1,x2,x3,x4,x5,x6) * xPC eip * xS1 X_ZF (SOME (x = Sym str)) * ~xS1 X_PF * ~xS1 X_SF * ~xS1 X_AF * ~xS1 X_OF * ~xS1 X_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``str:string`` |-> (stringSyntax.fromMLstring str)] post_tm
  val tm = find_term (can (match_term ``xPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``eip:word32`` |-> cdr tm] post_tm
  val imp = DISCH_ALL (MATCH_MP lisp_inv_builtin (UNDISCH lisp_inv_swap2))
  val imp = RW1 [EQ_SYM_EQ] imp
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_SYMBOL" ^ (int_to_string j),result) end;

fun PPC_LISP_EQ_SYMBOL (j,str) = let 
  val _ = print "p"
  val i = 2
  val s = "cmpwi " ^ (int_to_string (i+2)) ^ ", " ^ int_to_string j
  val s = ppc_encode s
  val (spec,_,sts,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val th = RW [WORD_EQ_SUB_ZERO] th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x1w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x0w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CR0 0x3w)`` th
  val th = HIDE_POST_RULE ``pS1 (PPC_CARRY)`` th handle e => th
  val def = pLISP_def
  val pre_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC p * ~pS``
  val post_tm = ``pLISP (a,limit) (x1,x2,x3,x4,x5,x6) * pPC (p+4w) * pS1 (PPC_CR0 2w) (SOME (x = Sym str)) * ~(pS1 PPC_CARRY) *
      ~pS1 (PPC_CR0 0x1w) * ~pS1 (PPC_CR0 0x0w) * ~pS1 (PPC_CR0 0x3w)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``str:string`` |-> (stringSyntax.fromMLstring str)] post_tm
  val imp = DISCH_ALL (MATCH_MP lisp_inv_builtin (UNDISCH lisp_inv_swap2))
  val imp = RW1 [EQ_SYM_EQ] imp
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_SYMBOL" ^ (int_to_string j),result) end;

val list = 
  [(0x3,"nil"), (0xF,"t"), (0x1B,"quote"), (0x2B,"*"), (0x37,"+"), (0x43,"-"), 
   (0x4F,"<"), (0x5B,"car"), (0x67,"cdr"), (0x73,"cons"), (0x7F,"equal"), 
   (0x8F,"if"), (0x9B,"consp"), (0xAB,"numberp"), (0xBB,"symbolp"), (0xCB,"lambda")]
 
val _ = map ARM_LISP_EQ_SYMBOL list;
val _ = map X86_LISP_EQ_SYMBOL list;
val _ = map PPC_LISP_EQ_SYMBOL list;
  

val _ = export_theory();

