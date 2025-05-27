open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_ops";

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory;

open decompilerLib progTheory set_sepTheory helperLib;
open lisp_typeTheory lisp_invTheory lisp_gcTheory lisp_equalTheory;
open ppc_encodeLib x86_encodeLib;
open prog_armLib prog_ppcLib prog_x86Lib;

val decompile_arm = decompile prog_armLib.arm_tools;
val decompile_ppc = decompile prog_ppcLib.ppc_tools;
val decompile_x86 = decompile prog_x86Lib.x86_tools;

val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12","r13"];
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val aLISP_def = Define `
  aLISP (x1,x2,x3,x4,x5,x6,limit) =
    SEP_EXISTS a r3 r4 r5 r6 r7 r8 df f dm m dg g s.
     ~(aR 2w) * aR 3w r3 * aR 4w r4 * aR 5w r5 * aR 6w r6 * aR 7w r7 * aR 8w r8 * aR 9w a *
     aMEMORY df f * aMEMORY dm m * aBYTE_MEMORY dg g *
       cond (lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,dm,m,dg,g))`;

val pLISP_def = Define `
  pLISP (x1,x2,x3,x4,x5,x6,limit) =
    SEP_EXISTS a r3 r4 r5 r6 r7 r8 df f dm m dg g s.
     ~(pR 0w) * ~(pR 2w) * pR 3w r3 * pR 4w r4 * pR 5w r5 * pR 6w r6 * pR 7w r7 * pR 8w r8 * pR 9w a *
     pMEMORY df f * pMEMORY dm m * pBYTE_MEMORY dg g *
       cond (lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,dm,m,dg,g))`;

val xLISP_def = Define `
  xLISP (x1,x2,x3,x4,x5,x6,limit) =
    SEP_EXISTS a r3 r4 r5 r6 r7 r8 df f dm m dg g s.
     xR EAX r3 * xR ECX r4 * xR EDX r5 * xR EBX r6 * xR EDI r7 * xR ESI r8 * xR EBP a *
     xMEMORY df f * xMEMORY dm m * xBYTE_MEMORY dg g *
       cond (lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,dm,m,dg,g))`;

fun x86_reg 1 = "eax" | x86_reg 2 = "ecx" | x86_reg 3 = "edx"
  | x86_reg 4 = "ebx" | x86_reg 5 = "edi" | x86_reg 6 = "esi" | x86_reg _ = fail()

val _ = set_echo 0;


(* automation *)

fun dest_sep_exists tm = let
  val (x,y) = dest_comb tm
  val _ = if (fst o dest_const) x = "SEP_EXISTS" then () else fail()
  in dest_abs y end;

fun dest_sep_cond tm =
  if (fst o dest_const o fst o dest_comb) tm = "cond"
  then snd (dest_comb tm) else fail();

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
    | rename ((x1,x2)::xs) (y1,y2) = if x1 ~~ y1 then (y2,x2)
                                     else rename xs (y1,y2)
  val s = map (fn (x,y) => x |-> y) (map (rename fill3) res3)
  val th = INST s th
  val th = UNDISCH_ALL (RW [SPEC_MOVE_COND] (SIMP_RULE (bool_ss++sep_cond_ss)  [] th))
  val (m,p,_,q) = (dest_spec o concl o SPEC_ALL) th
  val fill = list_dest dest_star tm
  val res = list_dest dest_star p
  val f = list_mk_star (filter (fn x => not (tmem x res)) fill) (type_of (hd fill))
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
    \\ REPEAT (Q.PAT_X_ASSUM `xx ==> yy` (K ALL_TAC))
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ SIMP_TAC std_ss [def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ AUTO_EXISTS_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_MULT_COMM WORD_MULT_ASSOC]
    \\ METIS_TAC [])
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
    \\ REPEAT (Q.PAT_X_ASSUM `xx ==> yy` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ METIS_TAC [])
  val th = MATCH_MP th lemma
  val th = RW [SEP_CLAUSES] th
  in th end;

fun set_pc th = let
  val (_,_,_,q) = (dest_spec o concl o UNDISCH_ALL) th
  val tm = find_term (fn x => tmem (car x) [``xPC``,``aPC``,``pPC``] handle e => false) q
  in subst [``p:word32``|->cdr tm] end


(* cons *)

val ARM_LISP_CONS = save_thm("ARM_LISP_CONS",let
  val th = arm_alloc_thm
  val imp = lisp_inv_cons
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = set_pc th ``aLISP (Dot x1 x2,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("arm_alloc_code",mk_eq(``(arm_alloc_code:word32->(word32 # word32) set) p``,c))
  val res = RW [GSYM def] res
  in res end);

val PPC_LISP_CONS = save_thm("PPC_LISP_CONS",let
  val th = RW [ppc_alloc_EQ] ppc_alloc_thm
  val imp = lisp_inv_cons
  val def = pLISP_def
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = set_pc th ``pLISP (Dot x1 x2,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("ppc_alloc_code",mk_eq(``(ppc_alloc_code:word32->(word32 # word32) set) p``,c))
  val res = RW [GSYM def] res
  in res end);

val X86_LISP_CONS = save_thm("X86_LISP_CONS",let
  val th = RW [x86_alloc_EQ] x86_alloc_thm
  val imp = lisp_inv_cons
  val def = xLISP_def
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC p * ~xS``
  val post_tm = set_pc th ``xLISP (Dot x1 x2,x2,x3,x4,x5,x6,limit) * xPC p * ~xS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("x86_alloc_code",mk_eq(``(x86_alloc_code:word32->(word32 # word8 list # bool) set) p``,c))
  val res = RW [GSYM def] res
  in res end);


(* equal *)

val ARM_LISP_EQUAL = save_thm("ARM_LISP_EQUAL",let
  val th = arm_eq_thm
  val imp = lisp_inv_equal
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = set_pc th ``aLISP (LISP_EQUAL x1 x2,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("arm_equal_code",mk_eq(``(arm_equal_code:word32->(word32 # word32) set) p``,c))
  val res = RW [GSYM def] res
  in res end);

val PPC_LISP_EQUAL = save_thm("PPC_LISP_EQUAL",let
  val th = ppc_eq_thm
  val imp = lisp_inv_equal
  val def = pLISP_def
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = set_pc th ``pLISP (LISP_EQUAL x1 x2,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("ppc_equal_code",mk_eq(``(ppc_equal_code:word32->(word32 # word32) set) p``,c))
  val res = RW [GSYM def] res
  in res end);

val X86_LISP_EQUAL = save_thm("X86_LISP_EQUAL",let
  val th = x86_eq_thm
  val imp = lisp_inv_equal
  val def = xLISP_def
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC p * ~xS``
  val post_tm = set_pc th ``xLISP (LISP_EQUAL x1 x2,x2,x3,x4,x5,x6,limit) * xPC p * ~xS``
  val res = prove_spec th imp def pre_tm post_tm
  val (_,_,c,_) = dest_spec (concl res)
  val def = new_definition("x86_equal_code",mk_eq(``(x86_equal_code:word32->(word32 # word8 list # bool) set) p``,c))
  val res = RW [GSYM def] res
  in res end);


(* isDot and isSym *)

fun ARM_LISP_ISDOT i = let
  val _ = print "a"
  val (arm_spec,_,sts,_) = arm_tools
  val ((th,_,_),_) = arm_spec ("E31"^(int_to_string (i+2))^"0003")
  val th = HIDE_POST_RULE ``aS1 psrN`` th
  val th = HIDE_POST_RULE ``aS1 psrC`` th
  val th = HIDE_POST_RULE ``aS1 psrV`` th
  val th = HIDE_PRE_STATUS_RULE sts th
  val def = aLISP_def
  val imp = lisp_inv_test
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 0x4w) * ~(aS1 psrN) * aS1 psrZ (isDot x) * ~(aS1 psrC) * ~(aS1 psrV)``
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * xS1 X_ZF (SOME (isDot x)) * ~xS1 X_PF * ~xS1 X_SF * ~xS1 X_AF * ~xS1 X_OF * ~xS1 X_CF``
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p+4w) * pS1 (PPC_CR0 2w) (SOME (isDot(x))) * ~(pS1 PPC_CARRY) *
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
  val th = HIDE_POST_RULE ``aS1 psrN`` th
  val th = HIDE_POST_RULE ``aS1 psrC`` th
  val th = HIDE_POST_RULE ``aS1 psrV`` th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = RW [Q.SPEC `n2w n` WORD_AND_COMM] th
  val def = aLISP_def
  val imp = lisp_inv_test
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 0x4w) * ~(aS1 psrN) * aS1 psrZ ~(isSym x) * ~(aS1 psrC) * ~(aS1 psrV)``
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * xS1 X_ZF (SOME ~(isSym x)) * ~xS1 X_PF * ~xS1 X_SF * ~xS1 X_AF * ~xS1 X_OF * ~xS1 X_CF``
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p+4w) * pS1 (PPC_CR0 2w) (SOME (~isSym(x))) * ~(pS1 PPC_CARRY) *
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
  | swap_thm _ = fail()

fun ARM_LISP_CONST (c,n,task,thc) i = let
  val _ = print "a"
  val s = "E3A0"^(int_to_string (i+2))^"0"^n
  val (spec,_,_,_) = arm_tools
  val ((th,_,_),_) = spec s
  val imp = lisp_inv_move
  val def = aLISP_def
  val swap = swap_thm i
  val imp = DISCH_ALL (MATCH_MP swap (UNDISCH thc))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH swap))
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 4w)``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> c]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("0x" ^ n ^ "w:word32")]]
  val post_tm = cdr (concl (INST s (REFL post_tm)))
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (INST s (INST sw (REFL tm))))
  val result = prove_spec th imp def pre_tm post_tm
  val r1 = save_thm("ARM_LISP_CONST" ^ int_to_string i ^ n,result)
  val r2 = save_thm("ARM_LISP_CONST" ^ int_to_string i ^ "_" ^ task,
           RW [GSYM TASK_EVAL_def,GSYM TASK_CONT_def,GSYM TASK_FUNC_def] result)
  in (r1,r2) end

val ARM_LISP_CONST_NIL   = ARM_LISP_CONST (``(Sym "nil"):SExp``, "03", "EVAL", lisp_inv_nil)
val ARM_LISP_CONST_T     = ARM_LISP_CONST (``(Sym "t"):SExp``, "0F", "CONT", lisp_inv_t)
val ARM_LISP_CONST_QUOTE = ARM_LISP_CONST (``(Sym "quote"):SExp``, "1B", "FUNC", lisp_inv_quote)

val _ = map ARM_LISP_CONST_NIL [1,2,3,4,5,6]
val _ = map ARM_LISP_CONST_T [1,2,3,4,5,6]
val _ = map ARM_LISP_CONST_QUOTE [1,2,3,4,5,6]

fun X86_LISP_CONST (c,n,task,thc) i = let
  val _ = print "x"
  val m = Arbnum.toString(Arbnum.fromHexString n)
  val s = "mov " ^ x86_reg i ^ ", " ^ m
  val s = x86_encode s
  val (spec,_,_,_) = x86_tools
  val ((th,_,_),_) = spec s
  val imp = lisp_inv_move
  val def = xLISP_def
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit)``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit)``
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
  val r1 = save_thm("X86_LISP_CONST" ^ int_to_string i ^ n,result)
  val r2 = save_thm("X86_LISP_CONST" ^ int_to_string i ^ "_" ^ task,
           RW [GSYM TASK_EVAL_def,GSYM TASK_CONT_def,GSYM TASK_FUNC_def] result)
  in (r1,r2) end

val X86_LISP_CONST_NIL   = X86_LISP_CONST (``(Sym "nil"):SExp``, "03", "EVAL", lisp_inv_nil)
val X86_LISP_CONST_T     = X86_LISP_CONST (``(Sym "t"):SExp``, "0F", "CONT", lisp_inv_t)
val X86_LISP_CONST_QUOTE = X86_LISP_CONST (``(Sym "quote"):SExp``, "1B", "FUNC", lisp_inv_quote)

val _ = map X86_LISP_CONST_NIL [1,2,3,4,5,6]
val _ = map X86_LISP_CONST_T [1,2,3,4,5,6]
val _ = map X86_LISP_CONST_QUOTE [1,2,3,4,5,6]

fun PPC_LISP_CONST (c,n,task,thc) i = let
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p + 4w)``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> c]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("0x" ^ n ^ "w:word32")]]
  val post_tm = cdr (concl (INST s (REFL post_tm)))
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (INST s (INST sw (REFL tm))))
  val result = prove_spec th imp def pre_tm post_tm
  val r1 = save_thm("PPC_LISP_CONST" ^ int_to_string i ^ n,result)
  val r2 = save_thm("PPC_LISP_CONST" ^ int_to_string i ^ "_" ^ task,
           RW [GSYM TASK_EVAL_def,GSYM TASK_CONT_def,GSYM TASK_FUNC_def] result)
  in (r1,r2) end

val PPC_LISP_CONST_NIL   = PPC_LISP_CONST (``(Sym "nil"):SExp``, "3", "EVAL", lisp_inv_nil)
val PPC_LISP_CONST_T     = PPC_LISP_CONST (``(Sym "t"):SExp``, "F", "CONT", lisp_inv_t)
val PPC_LISP_CONST_QUOTE = PPC_LISP_CONST (``(Sym "quote"):SExp``, "1B", "FUNC", lisp_inv_quote)

val _ = map PPC_LISP_CONST_NIL [1,2,3,4,5,6]
val _ = map PPC_LISP_CONST_T [1,2,3,4,5,6]
val _ = map PPC_LISP_CONST_QUOTE [1,2,3,4,5,6]


(* assign 0 or 1 *)

val lisp_inv_0 = (DISCH_ALL o SIMP_RULE std_ss [] o Q.SPEC `0` o UNDISCH) lisp_inv_Val
val lisp_inv_1 = (DISCH_ALL o SIMP_RULE std_ss [] o Q.SPEC `1` o UNDISCH) lisp_inv_Val

fun ARM_LISP_VAL thc i = let
  val _ = print "a"
  val v = find_term (can (match_term ``Val n``)) (concl thc)
  val n = find_term (can (match_term ``(n2w n):word32``)) (concl thc)
  val n = int_to_string (numSyntax.int_of_term (cdr n))
  val s = "E3A0"^(int_to_string (i+2))^"00"^n
  val (spec,_,_,_) = arm_tools
  val ((th,_,_),_) = spec s
  val def = aLISP_def
  val swap = swap_thm i
  val imp = DISCH_ALL (MATCH_MP swap (UNDISCH thc))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH swap))
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 4w)``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> v]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("0x" ^ n ^ "w:word32")]]
  val post_tm = cdr (concl (INST s (REFL post_tm)))
  val tm = ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``
  val tm2 = cdr (concl (INST s (INST sw (REFL tm))))
  val result = prove_spec th imp def pre_tm post_tm
  val r1 = save_thm("ARM_LISP_VAL_" ^ int_to_string i ^ "_" ^ n,result)
  in r1 end

val _ = map (ARM_LISP_VAL lisp_inv_0) [1,2,3,4,5,6]
val _ = map (ARM_LISP_VAL lisp_inv_1) [1,2,3,4,5,6]

fun X86_LISP_VAL thc i = let
  val _ = print "x"
  val v = find_term (can (match_term ``Val n``)) (concl thc)
  val n = find_term (can (match_term ``(n2w n):word32``)) (concl thc)
  val n = int_to_string (numSyntax.int_of_term (cdr n))
  val s = "mov " ^ x86_reg i ^ ", " ^ n
  val s = x86_encode s
  val (spec,_,_,_) = x86_tools
  val ((th,_,_),_) = spec s
  val def = xLISP_def
  val swap = swap_thm i
  val imp = DISCH_ALL (MATCH_MP swap (UNDISCH thc))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH swap))
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> v]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("0x" ^ n ^ "w:word32")]]
  val post_tm = cdr (concl (INST s (REFL post_tm)))
  val tm = find_term (can (match_term ``xPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``eip:word32`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  val r1 = save_thm("X86_LISP_VAL_" ^ int_to_string i ^ "_" ^ n,result)
  in r1 end

val _ = map (X86_LISP_VAL lisp_inv_0) [1,2,3,4,5,6]
val _ = map (X86_LISP_VAL lisp_inv_1) [1,2,3,4,5,6]

fun PPC_LISP_VAL thc i = let
  val _ = print "p"
  val v = find_term (can (match_term ``Val n``)) (concl thc)
  val n = find_term (can (match_term ``(n2w n):word32``)) (concl thc)
  val n = int_to_string (numSyntax.int_of_term (cdr n))
  val s = "addi " ^ (int_to_string (i+2)) ^ ", 0, " ^ n
  val s = ppc_encode s
  val (spec,_,_,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val def = pLISP_def
  val swap = swap_thm i
  val imp = DISCH_ALL (MATCH_MP swap (UNDISCH thc))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH swap))
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p+4w)``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> v]
  val sw = [Term [QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> Term [QUOTE ("0x" ^ n ^ "w:word32")]]
  val post_tm = cdr (concl (INST s (REFL post_tm)))
  val result = prove_spec th imp def pre_tm post_tm
  val r1 = save_thm("PPC_LISP_VAL_" ^ int_to_string i ^ "_" ^ n,result)
  in r1 end

val _ = map (PPC_LISP_VAL lisp_inv_0) [1,2,3,4,5,6]
val _ = map (PPC_LISP_VAL lisp_inv_1) [1,2,3,4,5,6]


(* move *)

fun ARM_LISP_MOVE (i,j) = let
  val _ = print "a"
  val inst = "E1A0"^(int_to_string (i+2))^"00"^(int_to_string (j+2))
  val (spec,_,_,_) = arm_tools
  val ((th,_,_),_) = spec inst
  val imp = lisp_inv_move
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 4w)``
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit)``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit)``
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p+4w)``
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
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 4w)``
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit)``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit)``
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p+4w)``
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
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 4w)``
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit)``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit)``
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p+4w)``
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
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = ``aLISP (LISP_ADD x1 x2,x2,x3,x4,x5,x6,limit) * aPC (p + 0x8w)``
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC p * ~xS``
  val post_tm = ``xLISP (LISP_ADD x1 x2,x2,x3,x4,x5,x6,limit) * xPC (p + 0x5w) * ~xS``
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p``
  val post_tm = ``pLISP (LISP_ADD x1 x2,x2,x3,x4,x5,x6,limit) * pPC (p + 0x8w)``
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
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = ``aLISP (LISP_SUB x1 x2,x2,x3,x4,x5,x6,limit) * aPC (p + 0x8w)``
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC p * ~xS``
  val post_tm = ``xLISP (LISP_SUB x1 x2,x2,x3,x4,x5,x6,limit) * xPC (p + 0x5w) * ~xS``
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = ``pLISP (LISP_SUB x1 x2,x2,x3,x4,x5,x6,limit) * pPC (p + 0x8w) * ~pS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_SUB",result) end;

(* sub1 and add1 *)

fun ARM_LISP_SUB1 i = let
  val (arm_spec,_,sts,_) = arm_tools
  val st = int_to_string (i+2)
  val ((th,_,_),_) = arm_spec ("E24"^st^st^"004")
  val imp = lisp_inv_SUB1
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH (swap_thm i)))
  val imp = UNDISCH (RW [AND_IMP_INTRO] imp)
  val imp = DISCH_ALL (MATCH_MP (swap_thm i) imp)
  val imp = RW1 [GSYM AND_IMP_INTRO] imp
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 0x4w)``
  val v = Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]
  val tm = subst [``x:SExp``|->v] ``LISP_SUB x (Val 1)``
  val post_tm = subst [v|->tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_SUB1_" ^ (int_to_string i),result) end;

fun ARM_LISP_ADD1 i = let
  val (arm_spec,_,sts,_) = arm_tools
  val st = int_to_string (i+2)
  val ((th,_,_),_) = arm_spec ("E28"^st^st^"004")
  val imp = lisp_inv_ADD1
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH (swap_thm i)))
  val imp = UNDISCH (RW [AND_IMP_INTRO] imp)
  val imp = DISCH_ALL (MATCH_MP (swap_thm i) imp)
  val imp = RW1 [GSYM AND_IMP_INTRO] imp
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 0x4w)``
  val v = Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]
  val tm = subst [``x:SExp``|->v] ``LISP_ADD x (Val 1)``
  val post_tm = subst [v|->tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_ADD1_" ^ (int_to_string i),result) end;

val _ = map ARM_LISP_SUB1 [1,2,3,4,5,6]
val _ = map ARM_LISP_ADD1 [1,2,3,4,5,6]

fun X86_LISP_SUB1 i = let
  val st = x86_reg i
  val s = x86_encode ("sub "^st^",4")
  val (spec,_,sts,_) = x86_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_STATUS_RULE true sts th
  val imp = lisp_inv_SUB1
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH (swap_thm i)))
  val imp = UNDISCH (RW [AND_IMP_INTRO] imp)
  val imp = DISCH_ALL (MATCH_MP (swap_thm i) imp)
  val imp = RW1 [GSYM AND_IMP_INTRO] imp
  val def = xLISP_def
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val tm = find_term (can (match_term ``xPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``eip:word32`` |-> cdr tm] post_tm
  val v = Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]
  val tm = subst [``x:SExp``|->v] ``LISP_SUB x (Val 1)``
  val post_tm = subst [v|->tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_SUB1_" ^ (int_to_string i),result) end;

fun X86_LISP_ADD1 i = let
  val st = x86_reg i
  val s = x86_encode ("add "^st^",4")
  val (spec,_,sts,_) = x86_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_STATUS_RULE true sts th
  val imp = lisp_inv_ADD1
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH (swap_thm i)))
  val imp = UNDISCH (RW [AND_IMP_INTRO] imp)
  val imp = DISCH_ALL (MATCH_MP (swap_thm i) imp)
  val imp = RW1 [GSYM AND_IMP_INTRO] imp
  val def = xLISP_def
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val tm = find_term (can (match_term ``xPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``eip:word32`` |-> cdr tm] post_tm
  val v = Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]
  val tm = subst [``x:SExp``|->v] ``LISP_ADD x (Val 1)``
  val post_tm = subst [v|->tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_ADD1_" ^ (int_to_string i),result) end;

val _ = map X86_LISP_SUB1 [1,2,3,4,5,6]
val _ = map X86_LISP_ADD1 [1,2,3,4,5,6]

fun PPC_LISP_SUB1 i = let
  val st = int_to_string (i+2)
  val s = ppc_encode ("addi "^st^","^st^",-4")
  val (spec,_,sts,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val imp = lisp_inv_SUB1
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH (swap_thm i)))
  val imp = UNDISCH (RW [AND_IMP_INTRO] imp)
  val imp = DISCH_ALL (MATCH_MP (swap_thm i) imp)
  val imp = RW1 [GSYM AND_IMP_INTRO] imp
  val def = pLISP_def
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p + 0x4w)``
  val v = Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]
  val tm = subst [``x:SExp``|->v] ``LISP_SUB x (Val 1)``
  val post_tm = subst [v|->tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_SUB1_" ^ (int_to_string i),result) end;

fun PPC_LISP_ADD1 i = let
  val st = int_to_string (i+2)
  val s = ppc_encode ("addi "^st^","^st^",4")
  val (spec,_,sts,_) = ppc_tools
  val ((th,_,_),_) = spec s
  val imp = lisp_inv_ADD1
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH (swap_thm i)))
  val imp = UNDISCH (RW [AND_IMP_INTRO] imp)
  val imp = DISCH_ALL (MATCH_MP (swap_thm i) imp)
  val imp = RW1 [GSYM AND_IMP_INTRO] imp
  val def = pLISP_def
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p + 0x4w)``
  val v = Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]
  val tm = subst [``x:SExp``|->v] ``LISP_ADD x (Val 1)``
  val post_tm = subst [v|->tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_ADD1_" ^ (int_to_string i),result) end;

val _ = map PPC_LISP_SUB1 [1,2,3,4,5,6]
val _ = map PPC_LISP_ADD1 [1,2,3,4,5,6]


(* less *)

val ARM_LISP_LESS = let
  val (arm_spec,_,sts,_) = arm_tools
  val ((th,_,_),_) = arm_spec "E1530004"
  val imp = lisp_inv_LESS
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val imp = RW1 [EQ_SYM_EQ] imp
  val th = RW [GSYM WORD_NOT_LOWER] th
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``aS1 psrN`` th
  val th = HIDE_POST_RULE ``aS1 psrZ`` th
  val th = HIDE_POST_RULE ``aS1 psrV`` th
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 0x4w) * ~(aS1 psrN) * ~(aS1 psrZ) * aS1 psrC ~(getVal x1 < getVal x2) * ~(aS1 psrV)``
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC (eip + 0x2w) * ~(xS1 X_AF) * ~(xS1 X_OF) *
        ~(xS1 X_SF) * ~(xS1 X_ZF) * ~(xS1 X_PF) * xS1 X_CF (SOME (getVal x1 < getVal x2))``
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p + 0x4w) *
    pS1 (PPC_CR0 0x0w) (SOME (getVal x1 < getVal x2)) * ~pS1 PPC_CARRY *
    ~pS1 (PPC_CR0 0x1w) * ~pS1 (PPC_CR0 0x2w) * ~pS1 (PPC_CR0 0x3w)``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_LESS",result) end;


(* mult, div and mod *)

open divideTheory;

val ARM_LISP_MULT = let
  val th = SIMP_RULE std_ss [lisp_word_mul_def,LET_DEF,SEP_CLAUSES] lisp_word_mul_arm_thm
  val th = RW [Q.SPEC `f y` SEP_HIDE_def] th
  val th = SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th
  val th = SPEC (mk_var("r5",``:word32``)) th
  val imp = lisp_inv_MULT
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p``
  val post_tm = set_pc th ``aLISP (LISP_MULT x1 x2,Sym "nil",Sym "nil",x4,x5,x6,limit) * aPC p``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_MULT",result) end;

val PPC_LISP_MULT = let
  val th = SIMP_RULE std_ss [lisp_word_mul_def,LET_DEF,SEP_CLAUSES] lisp_word_mul_ppc_thm
  val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [Q.ISPEC `pR 5w` SEP_HIDE_def])) th
  val th = SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th
  val th = SPEC (mk_var("r5",``:word32``)) th
  val imp = lisp_inv_MULT
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = pLISP_def
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = set_pc th ``pLISP (LISP_MULT x1 x2,Sym "nil",Sym "nil",x4,x5,x6,limit) * pPC p * ~pS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_MULT",result) end;

val X86_LISP_MULT = let
  val th = SIMP_RULE std_ss [lisp_word_mul_def,LET_DEF,SEP_CLAUSES] lisp_word_mul_x86_thm
  val th = RW [Q.SPEC `f y` SEP_HIDE_def] th
  val th = SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th
  val th = Q.SPEC `edx` th
  val imp = lisp_inv_MULT
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = xLISP_def
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC p * ~xS``
  val post_tm = set_pc th ``xLISP (LISP_MULT x1 x2,Sym "nil",Sym "nil",x4,x5,x6,limit) * xPC p * ~xS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_MULT",result) end;

val ARM_LISP_DIV = let
  val th = SIMP_RULE std_ss [lisp_word_div_def,LET_DEF,SEP_CLAUSES] lisp_word_div_arm_thm
  val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [Q.ISPEC `aR 5w` SEP_HIDE_def])) th
  val th = SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th
  val th = SPEC (mk_var("r5",``:word32``)) th
  val imp = lisp_inv_DIV
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = set_pc th ``aLISP (LISP_DIV x1 x2,Sym "nil",Sym "nil",x4,x5,x6,limit) * aPC p * ~aS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_DIV",result) end;

val PPC_LISP_DIV = let
  val th = SIMP_RULE std_ss [lisp_word_div_def,LET_DEF,SEP_CLAUSES] lisp_word_div_ppc_thm
  val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [Q.ISPEC `pR 5w` SEP_HIDE_def])) th
  val th = SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th
  val th = SPEC (mk_var("r5",``:word32``)) th
  val imp = lisp_inv_DIV
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = pLISP_def
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = set_pc th ``pLISP (LISP_DIV x1 x2,Sym "nil",Sym "nil",x4,x5,x6,limit) * pPC p * ~pS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_DIV",result) end;

val X86_LISP_DIV = let
  val th = SIMP_RULE std_ss [lisp_word_div_def,LET_DEF,SEP_CLAUSES] lisp_word_div_x86_thm
  val th = RW [Q.SPEC `f y` SEP_HIDE_def] th
  val th = SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th
  val th = Q.SPEC `edx` th
  val imp = lisp_inv_DIV
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = xLISP_def
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC p * ~xS``
  val post_tm = set_pc th ``xLISP (LISP_DIV x1 x2,Sym "nil",Sym "nil",x4,x5,x6,limit) * xPC p * ~xS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_DIV",result) end;

val ARM_LISP_MOD = let
  val th = SIMP_RULE std_ss [lisp_word_mod_def,LET_DEF,SEP_CLAUSES] lisp_word_mod_arm_thm
  val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [Q.ISPEC `aR 5w` SEP_HIDE_def])) th
  val th = SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th
  val th = SPEC (mk_var("r5",``:word32``)) th
  val imp = lisp_inv_MOD
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = set_pc th ``aLISP (LISP_MOD x1 x2,Sym "nil",Sym "nil",x4,x5,x6,limit) * aPC p * ~aS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_MOD",result) end;

val PPC_LISP_MOD = let
  val th = SIMP_RULE std_ss [lisp_word_mod_def,LET_DEF,SEP_CLAUSES] lisp_word_mod_ppc_thm
  val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [Q.ISPEC `pR 5w` SEP_HIDE_def])) th
  val th = SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th
  val th = SPEC (mk_var("r5",``:word32``)) th
  val imp = lisp_inv_MOD
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = pLISP_def
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = set_pc th ``pLISP (LISP_MOD x1 x2,Sym "nil",Sym "nil",x4,x5,x6,limit) * pPC p * ~pS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_MOD",result) end;

val X86_LISP_MOD = let
  val th = SIMP_RULE std_ss [lisp_word_mod_def,LET_DEF,SEP_CLAUSES] lisp_word_mod_x86_thm
  val th = RW [Q.SPEC `f y` SEP_HIDE_def] th
  val th = SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th
  val th = Q.SPEC `edx` th
  val imp = lisp_inv_MOD
  val imp = RW1 [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val def = xLISP_def
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC p * ~xS``
  val post_tm = set_pc th ``xLISP (LISP_MOD x1 x2,Sym "nil",Sym "nil",x4,x5,x6,limit) * xPC p * ~xS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_MOD",result) end;


(* test eq *)

val ARM_LISP_EQ = let
  val _ = print "a"
  val i = 1
  val j = 2
  val (arm_spec,_,sts,_) = arm_tools
  val inst = "E13"^(int_to_string (i+2))^"000"^(int_to_string (j+2))
  val ((th,_,_),_) = arm_spec inst
  val th = RW [WORD_EQ_XOR_ZERO] th
  val th = HIDE_POST_RULE ``aS1 psrN`` th
  val th = HIDE_POST_RULE ``aS1 psrC`` th
  val th = HIDE_POST_RULE ``aS1 psrV`` th
  val th = HIDE_PRE_STATUS_RULE sts th
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 0x4w) * ~(aS1 psrN) * aS1 psrZ (x = y:SExp) * ~(aS1 psrC) * ~(aS1 psrV)``
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * xS1 X_ZF (SOME (x = y:SExp)) * ~xS1 X_PF * ~xS1 X_SF * ~xS1 X_AF * ~xS1 X_OF * ~xS1 X_CF``
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p+4w) * pS1 (PPC_CR0 2w) (SOME (x = y:SExp)) * ~(pS1 PPC_CARRY) *
      ~pS1 (PPC_CR0 0x1w) * ~pS1 (PPC_CR0 0x0w) * ~pS1 (PPC_CR0 0x3w)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``y:SExp``|->Term [QUOTE ("x" ^ int_to_string j ^ ": SExp")]] post_tm
  val imp = lisp_inv_eq
  val imp = RW [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] imp))
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_EQ" ^ (int_to_string i) ^ (int_to_string j),result) end;


(* test symbol *)

fun ARM_LISP_EQ_SYMBOL (i,name,rw) (j,str) = let
  val _ = print "a"
  val (arm_spec,_,sts,_) = arm_tools
  val s = Arbnum.toHexString(Arbnum.fromInt j)
  val s = if size(s) < 2 then "0" ^ s else s
  val ((th,_,_),_) = arm_spec ("E33"^(int_to_string (i+2))^"00"^s)
  val th = RW [WORD_EQ_XOR_ZERO] th
  val th = HIDE_POST_RULE ``aS1 psrN`` th
  val th = HIDE_POST_RULE ``aS1 psrC`` th
  val th = HIDE_POST_RULE ``aS1 psrV`` th
  val th = HIDE_PRE_STATUS_RULE sts th
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 0x4w) * ~(aS1 psrN) * aS1 psrZ (x = Sym str) * ~(aS1 psrC) * ~(aS1 psrV)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``str:string`` |-> (stringSyntax.fromMLstring str)] post_tm
  val imp = DISCH_ALL (MATCH_MP lisp_inv_builtin (UNDISCH (swap_thm i)))
  val imp = RW1 [EQ_SYM_EQ] imp
  val result = prove_spec th imp def pre_tm post_tm
  val result = RW [GSYM rw] result
  in save_thm("ARM_LISP_SYMBOL" ^ name ^ "_" ^ (int_to_string j),result) end;

fun X86_LISP_EQ_SYMBOL (i,name,rw) (j,str) = let
  val _ = print "x"
  val s = "cmp " ^ (x86_reg i) ^ ", " ^ int_to_string j
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * xS1 X_ZF (SOME (x = Sym str)) * ~xS1 X_PF * ~xS1 X_SF * ~xS1 X_AF * ~xS1 X_OF * ~xS1 X_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``str:string`` |-> (stringSyntax.fromMLstring str)] post_tm
  val tm = find_term (can (match_term ``xPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``eip:word32`` |-> cdr tm] post_tm
  val imp = DISCH_ALL (MATCH_MP lisp_inv_builtin (UNDISCH (swap_thm i)))
  val imp = RW1 [EQ_SYM_EQ] imp
  val result = prove_spec th imp def pre_tm post_tm
  val result = RW [GSYM rw] result
  in save_thm("X86_LISP_SYMBOL" ^ name ^ "_" ^ (int_to_string j),result) end;

fun PPC_LISP_EQ_SYMBOL (i,name,rw) (j,str) = let
  val _ = print "p"
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p+4w) * pS1 (PPC_CR0 2w) (SOME (x = Sym str)) * ~(pS1 PPC_CARRY) *
      ~pS1 (PPC_CR0 0x1w) * ~pS1 (PPC_CR0 0x0w) * ~pS1 (PPC_CR0 0x3w)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``str:string`` |-> (stringSyntax.fromMLstring str)] post_tm
  val imp = DISCH_ALL (MATCH_MP lisp_inv_builtin (UNDISCH (swap_thm i)))
  val imp = RW1 [EQ_SYM_EQ] imp
  val result = prove_spec th imp def pre_tm post_tm
  val result = RW [GSYM rw] result
  in save_thm("PPC_LISP_SYMBOL" ^ name ^ "_" ^ (int_to_string j),result) end;

val list = let
  val th = SIMP_CONV std_ss [builtin_symbols_set_def,word_add_n2w] ``builtin_symbols_set 3w``
  val xs = (helperLib.list_dest (pred_setSyntax.dest_insert) o snd o dest_eq o concl) th
  val xs = map pairSyntax.dest_pair (tl (rev xs))
  val xs = map (fn (x,y) => (numSyntax.int_of_term ((snd (dest_comb x))), stringSyntax.fromHOLstring y)) xs
  in rev xs end

val _ = map (ARM_LISP_EQ_SYMBOL (1,"_EXP",TRUTH)) [hd list];
val _ = map (X86_LISP_EQ_SYMBOL (1,"_EXP",TRUTH)) [hd list];
val _ = map (PPC_LISP_EQ_SYMBOL (1,"_EXP",TRUTH)) [hd list];

val _ = map (ARM_LISP_EQ_SYMBOL (2,"",TRUTH)) list;
val _ = map (X86_LISP_EQ_SYMBOL (2,"",TRUTH)) list;
val _ = map (PPC_LISP_EQ_SYMBOL (2,"",TRUTH)) list;

val _ = ARM_LISP_EQ_SYMBOL (4,"_TASK",TASK_EVAL_def) (3,"nil")
val _ = ARM_LISP_EQ_SYMBOL (4,"_TASK",TASK_CONT_def) (15,"t")
val _ = ARM_LISP_EQ_SYMBOL (4,"_TASK",TASK_FUNC_def) (27,"quote")

val _ = X86_LISP_EQ_SYMBOL (4,"_TASK",TASK_EVAL_def) (3,"nil")
val _ = X86_LISP_EQ_SYMBOL (4,"_TASK",TASK_CONT_def) (15,"t")
val _ = X86_LISP_EQ_SYMBOL (4,"_TASK",TASK_FUNC_def) (27,"quote")

val _ = PPC_LISP_EQ_SYMBOL (4,"_TASK",TASK_EVAL_def) (3,"nil")
val _ = PPC_LISP_EQ_SYMBOL (4,"_TASK",TASK_CONT_def) (15,"t")
val _ = PPC_LISP_EQ_SYMBOL (4,"_TASK",TASK_FUNC_def) (27,"quote")


(* test for zero *)

val lisp_inv_test_zero = (SIMP_RULE std_ss [] o Q.SPEC `0`) lisp_inv_eq_0

fun ARM_LISP_EQ_ZERO i = let
  val _ = print "a"
  val (arm_spec,_,sts,_) = arm_tools
  val ((th,_,_),_) = arm_spec ("E33"^(int_to_string (i+2))^"0002")
  val th = RW [WORD_EQ_XOR_ZERO] th
  val th = HIDE_POST_RULE ``aS1 psrN`` th
  val th = HIDE_POST_RULE ``aS1 psrC`` th
  val th = HIDE_POST_RULE ``aS1 psrV`` th
  val th = HIDE_PRE_STATUS_RULE sts th
  val def = aLISP_def
  val pre_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC p * ~aS``
  val post_tm = ``aLISP (x1,x2,x3,x4,x5,x6,limit) * aPC (p + 0x4w) * ~(aS1 psrN) * aS1 psrZ (x = Val 0) * ~(aS1 psrC) * ~(aS1 psrV)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val imp = DISCH_ALL (MATCH_MP lisp_inv_test_zero (UNDISCH (swap_thm i)))
  val imp = RW1 [EQ_SYM_EQ] imp
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("ARM_LISP_EQ_ZERO_" ^ (int_to_string i),result) end;

fun X86_LISP_EQ_ZERO i = let
  val _ = print "x"
  val s = "cmp " ^ (x86_reg i) ^ ", 2"
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
  val pre_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * ~xS``
  val post_tm = ``xLISP (x1,x2,x3,x4,x5,x6,limit) * xPC eip * xS1 X_ZF (SOME (x = Val 0)) * ~xS1 X_PF * ~xS1 X_SF * ~xS1 X_AF * ~xS1 X_OF * ~xS1 X_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``xPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``eip:word32`` |-> cdr tm] post_tm
  val imp = DISCH_ALL (MATCH_MP lisp_inv_test_zero (UNDISCH (swap_thm i)))
  val imp = RW1 [EQ_SYM_EQ] imp
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("X86_LISP_EQ_ZERO_" ^ (int_to_string i),result) end;

fun PPC_LISP_EQ_ZERO i = let
  val _ = print "p"
  val s = "cmpwi " ^ (int_to_string (i+2)) ^ ", 2"
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
  val pre_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC p * ~pS``
  val post_tm = ``pLISP (x1,x2,x3,x4,x5,x6,limit) * pPC (p+4w) * pS1 (PPC_CR0 2w) (SOME (x = Val 0)) * ~(pS1 PPC_CARRY) *
      ~pS1 (PPC_CR0 0x1w) * ~pS1 (PPC_CR0 0x0w) * ~pS1 (PPC_CR0 0x3w)``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val imp = DISCH_ALL (MATCH_MP lisp_inv_test_zero (UNDISCH (swap_thm i)))
  val imp = RW1 [EQ_SYM_EQ] imp
  val result = prove_spec th imp def pre_tm post_tm
  in save_thm("PPC_LISP_EQ_ZERO_" ^ (int_to_string i),result) end;

val _ = map ARM_LISP_EQ_ZERO [1,2,3,4,5,6];
val _ = map X86_LISP_EQ_ZERO [1,2,3,4,5,6];
val _ = map PPC_LISP_EQ_ZERO [1,2,3,4,5,6];


val _ = export_theory();
