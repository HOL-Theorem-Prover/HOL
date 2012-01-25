open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_symbols";
open lisp_sexpTheory lisp_consTheory lisp_invTheory;

(* --- *)

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib;
open set_sepTheory bitTheory fcpTheory stringTheory;

val wstd_ss = std_ss ++ SIZES_ss ++ rewrites [DECIDE ``n<256 ==> (n:num)<18446744073709551616``,ORD_BOUND];

open stop_and_copyTheory;
open codegenLib decompilerLib prog_x64Lib prog_x64Theory progTheory;
open lisp_parseTheory;

infix \\
val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
fun SUBGOAL q = REVERSE (q by ALL_TAC)


val align_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a - w && 3w = 0w) = (w && 3w = 0w:word64))``

val align_add_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a + w && 3w = 0w) = (w && 3w = 0w:word64))``


(* lookup

  r11 - pointer to symbol table
  r0 - used as temp
  r10 - symbol index

  (assemble "x64" `
L1:  test r10,r10
     je L2
     movzx r0,BYTE [r11]
     add r11,r0
     dec r10
     jmp L1
L2:  `)

*)

val (thm,mc_lookup_def) = decompile_io x64_tools "mc_lookup"
  (SOME (``(r10:word64,r11:word64,dg:word64 set,g:word64->word8)``,
         ``(r11:word64,dg:word64 set,g:word64->word8)``)) `
  4D85D2      (* L1:  test r10,r10             *)
  48740D      (*      je L2                    *)
  490FB603/g  (*      movzx r0,BYTE [r11]      *)
  4901C3      (*      add r11,r0               *)
  49FFCA      (*      dec r10                  *)
  48EBED      (*      jmp L1                   *)
              (* L2:                           *)`;

val mc_lookup_thm = prove(
  ``!xs a k i p.
      (LIST_FIND k s xs = SOME (k+i)) /\ i < 2**32 /\
      EVERY (\x. LENGTH x < 255) xs /\
      (one_byte_list a (symbol_list xs) * p) (fun2set (g,dg)) ==>
      ?a2 q. mc_lookup_pre (n2w i,a,dg,g) /\
             (mc_lookup (n2w i,a,dg,g) = (a2,dg,g)) /\
             (one_byte_list a2 (string_data s) * q) (fun2set (g,dg))``,
  Induct \\ SIMP_TAC std_ss [LIST_FIND_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `s = h` \\ FULL_SIMP_TAC std_ss [] THEN1
   (`i = 0` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [mc_lookup_def] \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [one_symbol_list_def,SEP_CLAUSES,
          SEP_EXISTS_THM,cond_STAR,symbol_list_def,one_byte_list_APPEND]
    \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [one_symbol_list_def,SEP_CLAUSES,
        SEP_EXISTS_THM,cond_STAR,symbol_list_def,RW1[STAR_COMM]one_byte_list_APPEND]
  \\ ONCE_REWRITE_TAC [mc_lookup_def] \\ FULL_SIMP_TAC std_ss []
  \\ `i < 18446744073709551616` by DECIDE_TAC
  \\ IMP_RES_TAC LIST_FIND_LESS_EQ
  \\ `~(i = 0)` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF]
  \\ Cases_on `i` \\ FULL_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [string_data_def,one_byte_list_def,STAR_ASSOC]
  \\ SEP_R_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,EVERY_DEF]
  \\ `(STRLEN h + 1) < 256` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `n < 4294967296` by DECIDE_TAC
  \\ SEP_I_TAC "mc_lookup" \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `k+1`)
  \\ FULL_SIMP_TAC std_ss [DECIDE ``k + SUC n = k + 1 + n``]
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_MAP,ADD1] \\ SEP_F_TAC
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC []);


(* string less-than

  r10 - length of str10
  r11 - length of str11
  r8 - pointer to str10
  r9 - pointer to str11
  r0 - temp and result

  (assemble "x64" `
START: cmp r11,0
       je FALSE
       cmp r10,0
       je TRUE
       movzx r0,BYTE [r8]
       cmp r0b,BYTE [r9]
       jb TRUE
       ja FALSE
       inc r8
       inc r9
       dec r10
       dec r11
       jmp START
FALSE: mov r0d,3
       jmp EXIT
TRUE:  mov r0d,11
EXIT:`)

*)

val (thm,mc_string_lt_def) = basic_decompile x64_tools "mc_string_lt"
  (SOME (``(r10:word64,r11:word64,r8:word64,r9:word64,dg:word64 set,g:word64->word8)``,
         ``(r0:word64,dg:word64 set,g:word64->word8)``)) `
  4983FB00      (* START: cmp r11,0                 *)
  487423        (*        je FALSE                  *)
  4983FA00      (*        cmp r10,0                 *)
  487424        (*        je TRUE                   *)
  490FB600/g    (*        movzx r0,BYTE [r8]        *)
  413A01/g      (*        cmp r0b,BYTE [r9]         *)
  48721A        (*        jb TRUE                   *)
  48770F        (*        ja FALSE                  *)
  49FFC0        (*        inc r8                    *)
  49FFC1        (*        inc r9                    *)
  49FFCA        (*        dec r10                   *)
  49FFCB        (*        dec r11                   *)
  48EBD6        (*        jmp START                 *)
  B803000000    (* FALSE: mov r0d,3                 *)
  48EB05        (*        jmp EXIT                  *)
  B80B000000    (* TRUE:  mov r0d,11                *)
                (* EXIT:                            *)`;

val one_string_def = Define `
  one_string a s = one_byte_list a (MAP (n2w o ORD) s)`;

val one_string_CONS = ``one_string a (x::xs)``
  |> (SIMP_CONV std_ss [one_string_def,MAP,one_byte_list_def] THENC
      SIMP_CONV std_ss [GSYM one_string_def]) |> RW1 [STAR_COMM]

val mc_string_lt_lemma = prove(
  ``!w. (7 -- 0) (w2w (w:word8)):word64 = w2w (w:word8)``,
  blastLib.BBLAST_TAC);

val mc_string_lt_thm = prove(
  ``!s2 s1 a1 a2 q1 q2.
      LENGTH s1 < 255 /\ LENGTH s2 < 255 /\
      (one_string a1 s1 * q1) (fun2set (g,dg)) /\
      (one_string a2 s2 * q2) (fun2set (g,dg)) ==>
      mc_string_lt_pre (n2w (LENGTH s1),n2w (LENGTH s2),a1,a2,dg,g) /\
      (mc_string_lt (n2w (LENGTH s1),n2w (LENGTH s2),a1,a2,dg,g) =
         (if s1 < s2 then 11w else 3w,dg,g))``,
  Induct THEN1
   (Cases \\ SIMP_TAC std_ss [string_lt_def,LENGTH]
    \\ ONCE_REWRITE_TAC [mc_string_lt_def] \\ ASM_SIMP_TAC std_ss [LET_DEF])
  \\ Cases_on `s1` THEN1
   (SIMP_TAC std_ss [string_lt_def,LENGTH,ADD1]
    \\ ONCE_REWRITE_TAC [mc_string_lt_def] \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ REPEAT STRIP_TAC
    \\ `(STRLEN s2 + 1) < 18446744073709551616` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  \\ SIMP_TAC std_ss [string_lt_def] \\ NTAC 6 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [one_string_CONS,GSYM STAR_ASSOC,LENGTH]
  \\ IMP_RES_TAC (DECIDE ``SUC n < 255 ==> n < 255 /\ n+1 < 18446744073709551616``)
  \\ ONCE_REWRITE_TAC [mc_string_lt_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [ADD1,n2w_11,LET_DEF]
  \\ SEP_R_TAC
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [mc_string_lt_lemma]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,n2w_11,word_lo_n2w]
  \\ `ORD h < 256 /\ ORD h' < 256` by ASM_SIMP_TAC std_ss [ORD_BOUND]
  \\ IMP_RES_TAC (DECIDE ``n < 256 ==> n < 18446744073709551616``)
  \\ ASM_SIMP_TAC std_ss [char_lt_def,GSYM ORD_11] \\ METIS_TAC []);

(* symbol-<

  (assemble "x64" `
     mov r11,[r7-224]
     shr r8,3
     mov r10,r8
     insert mc_lookup
     mov r8,r11
     shr r9,3
     mov r10,r9
     mov r11,[r7-224]
     insert mc_lookup
     mov r9,r11
     movzx r10,BYTE [r8]
     movzx r11,BYTE [r9]
     dec r10
     dec r11
     inc r8
     inc r9
     insert mc_string_lt
     mov r8,r0
     mov r0d,3
     mov r9,r0
     mov r10,r0
     mov r11,r0
     `)

*)

val (mc_symbol_less_spec,mc_symbol_less_def) = basic_decompile x64_tools "mc_symbol_less"
  (SOME (``(r8:word64,r9:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r0:word64,r8:word64,r9:word64,r10:word64,r11:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``)) `
  4C8B9F20FFFFFF         (*      mov r11,[r7-224]         *)
  49C1E803               (*      shr r8,3                 *)
  4D8BD0                 (*      mov r10,r8               *)
  insert:mc_lookup
  4D8BC3                 (*      mov r8,r11               *)
  49C1E903               (*      shr r9,3                 *)
  4D8BD1                 (*      mov r10,r9               *)
  4C8B9F20FFFFFF         (*      mov r11,[r7-224]         *)
  insert:mc_lookup
  4D8BCB                 (*      mov r9,r11               *)
  4D0FB610/g             (*      movzx r10,BYTE [r8]      *)
  4D0FB619/g             (*      movzx r11,BYTE [r9]      *)
  49FFCA                 (*      dec r10                  *)
  49FFCB                 (*      dec r11                  *)
  49FFC0                 (*      inc r8                   *)
  49FFC1                 (*      inc r9                   *)
  insert:mc_string_lt
  4C8BC0                 (*      mov r8,r0                *)
  B803000000             (*      mov r0d,3                *)
  4C8BC8                 (*      mov r9,r0                *)
  4C8BD0                 (*      mov r10,r0               *)
  4C8BD8                 (*      mov r11,r0               *)`

val _ = save_thm("mc_symbol_less_spec",mc_symbol_less_spec);

val mc_symbol_less_blast = prove(
  ``!w. ((w2w (w2w (w:29 word) << 3 !! 0x3w:word32) >>> 3):word64 = w2w w) /\
        (((sp - 0xE0w && 0x3w) = 0x0w) = (sp && 0x3w = 0x0w:word64)) /\
        (((sp - 0xDCw && 0x3w) = 0x0w) = (sp && 0x3w = 0x0w:word64))``,
  blastLib.BBLAST_TAC);

val FORALL_EXISTS = METIS_PROVE [] ``(!x. P x ==> Q) = ((?x. P x) ==> Q)``
val IMP_IMP = METIS_PROVE [] ``b /\ (c ==> d) ==> ((b ==> c) ==> d)``

val LIST_FIND_MEM = prove(
  ``!s a k l. (LIST_FIND k a s = SOME l) ==> MEM a s``,
  Induct \\ SIMP_TAC std_ss [LIST_FIND_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `a = h` \\ FULL_SIMP_TAC std_ss [MEM] \\ METIS_TAC []);

val LISP = lisp_inv_def |> SPEC_ALL |> concl |> dest_eq |> fst;
val REST = LISP |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;
val STAT = LISP |> car |> car |> cdr;
val VAR_REST = LISP |> car |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;

val lisp_inv_NIL = lisp_inv_Sym
  |> CONJUNCTS |> hd |> UNDISCH |> CONJUNCTS |> hd |> DISCH_ALL |> GEN_ALL;

val lisp_inv_T = save_thm("lisp_inv_T",lisp_inv_Sym
  |> CONJUNCTS |> tl |> hd |> UNDISCH |> CONJUNCTS |> hd |> DISCH_ALL |> GEN_ALL);

val mc_symbol_less_thm = store_thm("mc_symbol_less_thm",
  ``lisp_inv ^STAT (x0,x1,x2,x3,x4,x5,^VAR_REST)
       (w0,w1,w2,w3,w4,w5,df,f,^REST) ==> isSym x0 /\ isSym x1 ==>
    ?fi w0i w1i w2i w3i.
      mc_symbol_less_pre (w2w w0,w2w w1,sp,df,f,dg,g) /\
      (mc_symbol_less (w2w w0,w2w w1,sp,df,f,dg,g) = (tw0,w2w w0i,w2w w1i,w2w w2i,w2w w3i,sp,df,fi,dg,g)) /\
      lisp_inv ^STAT (LISP_SYMBOL_LESS x0 x1,Sym "NIL",Sym "NIL",Sym "NIL",x4,x5,^VAR_REST)
        (w0i,w1i,w2i,w3i,w4,w5,df,fi,^REST)``,
  SIMP_TAC std_ss [AND_IMP_INTRO]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(b1 ==> b1 /\ b2 /\ b3 ==> b4) ==> (b1 /\ b2 /\ b3 ==> b4)``)
  \\ STRIP_TAC \\ SIMP_TAC std_ss [Once lisp_inv_def]
  \\ SIMP_TAC std_ss [isSym_thm,mc_symbol_less_def] \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [LISP_SYMBOL_LESS_def,getSym_def]
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11,lisp_x_def]
  \\ Q.PAT_ASSUM `ref_heap_addr s0 = w0` (MP_TAC o GSYM)
  \\ Q.PAT_ASSUM `ref_heap_addr s1 = w1` (MP_TAC o GSYM)
  \\ ASM_SIMP_TAC std_ss [ref_heap_addr_def,INSERT_SUBSET,EMPTY_SUBSET]
  \\ `(w2w (f (sp - 0xDCw)) << 32 !! w2w (f (sp - 0xE0w)) = sa1) /\
      sp - 0xDCw IN df /\ sp - 0xE0w IN df` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [lisp_inv_def,ref_full_stack_def,ref_static_def,APPEND]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,word64_3232_def,word_arith_lemma3,STAR_ASSOC,SEP_CLAUSES]
    \\ SEP_R_TAC \\ blastLib.BBLAST_TAC)
  \\ ASM_SIMP_TAC std_ss [mc_symbol_less_blast]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,LET_DEF]
  (* lookup1 *)
  \\ ASSUME_TAC ((GEN_ALL o RW [ADD_CLAUSES] o Q.INST [`k`|->`0`] o SPEC_ALL) mc_lookup_thm)
  \\ SEP_I_TAC "mc_lookup"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`INIT_SYMBOLS ++ sym`,`a`])
  \\ ASM_SIMP_TAC std_ss [FORALL_EXISTS]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [symtable_inv_def,one_symbol_list_def,
       one_byte_list_APPEND,SEP_EXISTS_THM,cond_STAR]
    \\ Q.EXISTS_TAC `one_byte_list
          (sa1 + n2w (LENGTH (symbol_list (INIT_SYMBOLS ++ sym)))) ys`
    \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  (* lookup2 *)
  \\ ASSUME_TAC ((GEN_ALL o RW [ADD_CLAUSES] o Q.INST [`k`|->`0`] o SPEC_ALL) mc_lookup_thm)
  \\ SEP_I_TAC "mc_lookup"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`INIT_SYMBOLS ++ sym`,`a'`])
  \\ ASM_SIMP_TAC std_ss [FORALL_EXISTS]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [symtable_inv_def,one_symbol_list_def,
       one_byte_list_APPEND,SEP_EXISTS_THM,cond_STAR]
    \\ Q.EXISTS_TAC `one_byte_list
          (sa1 + n2w (LENGTH (symbol_list (INIT_SYMBOLS ++ sym)))) ys`
    \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  (* string_lt *)
  \\ FULL_SIMP_TAC std_ss [string_data_def,one_byte_list_def]
  \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [GSYM one_string_def]
  \\ `STRLEN a < 255 /\ STRLEN a' < 255` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [symtable_inv_def,one_symbol_list_def,
       one_byte_list_APPEND,SEP_EXISTS_THM,cond_STAR]
    \\ IMP_RES_TAC LIST_FIND_MEM \\ FULL_SIMP_TAC std_ss [EVERY_MEM])
  \\ IMP_RES_TAC (DECIDE ``n<255 ==> n+1<256``)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ ASSUME_TAC (GEN_ALL mc_string_lt_thm)
  \\ SEP_I_TAC "mc_string_lt" \\ POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC std_ss [FORALL_EXISTS]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (Q.EXISTS_TAC `one (a2',n2w (STRLEN a) + 0x1w) * q`
    \\ Q.EXISTS_TAC `one (a2'',n2w (STRLEN a') + 0x1w) * q'`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`if a < a' then 0xBw else 0x3w`,`3w`,`3w`,`3w`]
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC
  THEN1 (Cases_on `a < a'` \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
  \\ MATCH_MP_TAC lisp_inv_swap1
  \\ MATCH_MP_TAC lisp_inv_NIL \\ Q.LIST_EXISTS_TAC [`x1`,`w1`]
  \\ MATCH_MP_TAC lisp_inv_swap1
  \\ MATCH_MP_TAC lisp_inv_swap2
  \\ MATCH_MP_TAC lisp_inv_NIL \\ Q.LIST_EXISTS_TAC [`x2`,`w2`]
  \\ MATCH_MP_TAC lisp_inv_swap2
  \\ MATCH_MP_TAC lisp_inv_swap3
  \\ MATCH_MP_TAC lisp_inv_NIL \\ Q.LIST_EXISTS_TAC [`x3`,`w3`]
  \\ MATCH_MP_TAC lisp_inv_swap3
  \\ Cases_on `a < a'` \\ FULL_SIMP_TAC std_ss [LISP_TEST_def]
  THEN1 (MATCH_MP_TAC lisp_inv_T \\ Q.LIST_EXISTS_TAC [`x0`,`w0`]
         \\ FULL_SIMP_TAC std_ss [])
  THEN1 (MATCH_MP_TAC lisp_inv_NIL \\ Q.LIST_EXISTS_TAC [`x0`,`w0`]
         \\ FULL_SIMP_TAC std_ss []));


(* helper function *)

fun make_code_set code = let
  fun take 0 xs = [] | take n xs = hd xs :: take (n-1) xs
  fun drop 0 xs = xs | drop n xs = drop (n-1) xs
  fun split s = if s = "" then [] else
                  substring(s,0,2) :: split (substring(s,2,size(s)-2));
  val ns = map (map (Arbnum.toInt o Arbnum.fromHexString)) (map split code)
  fun mk_byte n = wordsSyntax.mk_n2w(numSyntax.term_of_int n,``:8``)
  fun listw x = listSyntax.mk_list(map mk_byte x,``:word8``)
  fun foo n w = subst [mk_var("n",``:num``)|->numSyntax.term_of_int n,
                       mk_var("xs",``:word8 list``)|->w]
    ``(p + (n2w n):word64,xs:word8 list)``
  fun foos n [] = pred_setSyntax.mk_empty(type_of (foo 0 (listw (hd ns))))
    | foos n (w::ws) = pred_setSyntax.mk_insert(foo n (listw w),foos (n+length w) ws)
  fun post_pc n [] = (fst (dest_pair (foo n (listw (hd ns)))),n)
    | post_pc n (w::ws) = post_pc (n+length w) ws
  in (foos 0 ns, post_pc 0 ns) end;


(* reading and writing io *)

val IO_READ_def = Define `
  (IO_READ (IO_STREAMS [] ys) = ~0w:word64) /\
  (IO_READ (IO_STREAMS (x::xs) ys) = n2w (ORD x))`;

val IO_NEXT_def = Define `
  (IO_NEXT (IO_STREAMS  [] ys) = IO_STREAMS [] ys) /\
  (IO_NEXT (IO_STREAMS (x::xs) ys) = IO_STREAMS xs ys)`;

val IO_WRITE_def = Define `
  IO_WRITE (IO_STREAMS xs ys) zs = IO_STREAMS xs (ys ++ zs)`;

val IO_STATS_def = Define `
  IO_STATS (n:num) (IO_STREAMS xs ys) = (IO_STREAMS xs ys)`;

val REPLACE_INPUT_IO_def = Define `
  REPLACE_INPUT_IO x (IO_STREAMS xs ys) = IO_STREAMS x ys`;

val getINPUT_def = Define `
  getINPUT (IO_STREAMS xs ys) = xs`;

val IO_INPUT_APPLY_def = Define `
  IO_INPUT_APPLY f io = REPLACE_INPUT_IO (f (getINPUT io)) io`;

val IO_INPUT_LEMMA = store_thm("IO_INPUT_LEMMA",
  ``(IO_READ (REPLACE_INPUT_IO (w::ws) io) = n2w (ORD w)) /\
    (IO_NEXT (REPLACE_INPUT_IO (w::ws) io) = REPLACE_INPUT_IO ws io) /\
    (IO_READ (REPLACE_INPUT_IO [] io) = ~0w) /\
    (REPLACE_INPUT_IO (getINPUT io) io = io)``,
  Cases_on `io` \\ SIMP_TAC std_ss [REPLACE_INPUT_IO_def,IO_READ_def,IO_NEXT_def,getINPUT_def]);

val IO_WRITE_APPEND = store_thm("IO_WRITE_APPEND",
  ``!io x1 x2. IO_WRITE (IO_WRITE io x1) x2 = IO_WRITE io (x1 ++ x2)``,
  Cases \\ ASM_SIMP_TAC std_ss [IO_WRITE_def,APPEND_ASSOC,MAP_APPEND]);

val zIO_def = Define `
  zIO (iow:word64,ior:word64,iod:word64,ioi:word64) (io:io_streams) = zR 2w 3w`;

val zIO_R_def = Define `
  zIO_R (iow,ior,iod) io = SEP_EXISTS ioi. zR 1w ioi * zIO (iow,ior,iod,ioi) io`;

val null_term_str_def = Define `
  null_term_str a df f str =
    ?p. (one_string a (str ++ [CHR 0]) * p) (fun2set (f,df)) /\
        EVERY (\x. ~(x = CHR 0)) str`;

val exists_null_term_str_def = Define `
  exists_null_term_str a df f = ?str. null_term_str a df f str`;

val mem2string_def = Define `
  mem2string a df f = @str. null_term_str a df f str`;


(* IO assumpiptions *)

val IO = mk_var("IO",``:bool[64] # bool[64] # bool[64] # bool[64] ->
                        io_streams -> x64_set -> bool``);

val IOR = ``\(iow,ior,iod) io. SEP_EXISTS ioi. zR 1w ioi * ^IO (iow,ior,iod,ioi) io``

val (read_code,(read_post_pc,read_code_len)) = make_code_set
  (assemble "x64" `
      movzx r0, BYTE [r1]
      test r0,r0
      jne SKIP
      call r2
      movzx r0, BYTE [r1]
      test r0,r0
      jne SKIP
      xor r0,r0
      not r0
SKIP:`)

val io_read_tm =
  ``SPEC X64_MODEL
       (zPC p * zR 0x0w r0 * zR 0x2w r2 * ^IOR (x,r2,y) io * ~zS)
       ^read_code
       (let r0 = IO_READ io in
          (zPC ^read_post_pc * zR 0x0w r0 * zR 0x2w r2 * ^IOR (x,r2,y) io * ~zS))``;

(* IO_NEXT *)

val (next_code,(next_post_pc,next_code_len)) = make_code_set
  (assemble "x64" `
     inc r1
     `)

val io_next_tm =
  ``SPEC X64_MODEL
       (zPC p * zR 0x2w r2 * ^IOR (x,r2,y) io * ~zS)
       ^next_code
       (let io = IO_NEXT io in (zPC ^next_post_pc * zR 0x2w r2 * ^IOR (x,r2,y) io * ~zS))``;

(* IO_WRITE *)

val (write_code,(write_post_pc,write_code_len)) = make_code_set
  (assemble "x64" `
      call r1
   `)

val io_write_tm =
  ``SPEC X64_MODEL
       (zPC p * zR 0w r0 * zR 0x1w r1 * ^IO (ior,x,y,z) io * zBYTE_MEMORY dg g * ~zS *
        cond (exists_null_term_str r0 dg g /\ (ior = r1)))
       ^write_code
       (let io = IO_WRITE io (mem2string r0 dg g) in
          (zPC ^write_post_pc * zR 0w r0 * zR 0x1w r1 * ^IO (ior,x,y,z) io * ~zS * zBYTE_MEMORY dg g))``;

(* IO_STATS *)

val (stats_code,(stats_post_pc,stats_code_len)) = make_code_set
  (assemble "x64" `
      call r1
   `)

val io_stats_tm =
  ``SPEC X64_MODEL
       (zPC p * zR 0x1w r1 * zR 0x7w r7 * ^IO (ior,iow,iod,ioi) io * ~zS * cond (iod = r1))
       ^stats_code
       (let io = IO_STATS (w2n r7) io in
          (zPC ^stats_post_pc * zR 0x1w r1 * zR 0x7w r7 * ^IO (ior,iow,iod,ioi) io * ~zS))``;

(* definition of IO assertions *)

fun genall tm v = foldr mk_forall tm (filter (fn x => not (x = v)) (free_vars tm));

val io_assums_def = Define `
  io_assums ^IO = ^(genall io_stats_tm IO) /\
                  ^(genall io_write_tm IO) /\
                  ^(genall io_read_tm IO) /\
                  ^(genall io_next_tm IO)`;

val zIO_def = Define `
  zIO (iow,ior,iod,ioi) io =
    SEP_EXISTS IO. ^IO (iow,ior,iod,ioi) io * cond (io_assums ^IO)`;

val zIO_R_def = Define `
  zIO_R (iow,ior,iod) io =
     SEP_EXISTS ioi. zR 0x1w ioi * zIO (iow,ior,iod,ioi) io`;

val SPEC_EXISTS_EXISTS = store_thm("SPEC_EXISTS_EXISTS",
  ``(!x. SPEC m (P x) c (Q x)) ==> SPEC m (SEP_EXISTS x. P x) c (SEP_EXISTS x. Q x)``,
  SIMP_TAC std_ss [GSYM progTheory.SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `x`)
  \\ IMP_RES_TAC progTheory.SPEC_WEAKEN
  \\ POP_ASSUM MATCH_MP_TAC
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ METIS_TAC []);

val ff = subst [IO |-> ``zIO``,
                IOR |-> ``zIO_R``]

val zIO_R_THM = prove(
  ``zIO_R (iow,ior,iod) io =
    SEP_EXISTS IO. ^IOR (iow,ior,iod) io * cond (io_assums IO)``,
  SIMP_TAC std_ss [zIO_def,zIO_R_def,SEP_CLAUSES,STAR_ASSOC]
  \\ SIMP_TAC std_ss [FUN_EQ_THM,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val zIO_STATS = prove(ff io_stats_tm,
  SIMP_TAC std_ss [zIO_def,SEP_CLAUSES,LET_DEF]
  \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS
  \\ REPEAT STRIP_TAC \\ Cases_on `io_assums IO`
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,progTheory.SPEC_FALSE_PRE]
  \\ FULL_SIMP_TAC std_ss [io_assums_def,LET_DEF]);

val zIO_WRITE = prove(ff io_write_tm,
  SIMP_TAC std_ss [zIO_def,SEP_CLAUSES,LET_DEF]
  \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS
  \\ REPEAT STRIP_TAC \\ Cases_on `io_assums IO`
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,progTheory.SPEC_FALSE_PRE]
  \\ FULL_SIMP_TAC std_ss [io_assums_def,LET_DEF]);

val zIO_READ = prove(ff io_read_tm,
  SIMP_TAC std_ss [zIO_R_THM,SEP_CLAUSES,LET_DEF]
  \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS
  \\ REPEAT STRIP_TAC \\ Cases_on `io_assums IO`
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,progTheory.SPEC_FALSE_PRE]
  \\ FULL_SIMP_TAC std_ss [io_assums_def,LET_DEF,SEP_CLAUSES]);

val zIO_NEXT = prove(ff io_next_tm,
  SIMP_TAC std_ss [zIO_R_THM,SEP_CLAUSES,LET_DEF]
  \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS
  \\ REPEAT STRIP_TAC \\ Cases_on `io_assums IO`
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,progTheory.SPEC_FALSE_PRE]
  \\ FULL_SIMP_TAC std_ss [io_assums_def,LET_DEF,SEP_CLAUSES]);

val _ = add_decompiled("io_next",zIO_NEXT,next_code_len,SOME next_code_len);
val _ = add_decompiled("io_read",zIO_READ,read_code_len,SOME read_code_len);
val _ = add_decompiled("io_write",zIO_WRITE,write_code_len,SOME write_code_len);
val _ = add_decompiled("io_stats",zIO_STATS,stats_code_len,SOME stats_code_len);


(* read until newline character *)

val (thm,mc_read_until_newline_def) = basic_decompile_strings x64_tools "mc_read_until_newline"
  (SOME (``(io:io_streams)``,
         ``(io:io_streams)``))
  (assemble "x64" `
START:
       insert io_read
       cmp r0,255
       ja EXIT
       cmp r0,10
       je EXIT
       insert io_next
       jmp START
EXIT:`)

val SND_read_while = prove(
  ``!zs s P. SND (read_while P zs s) = SND (read_while P zs "")``,
  Induct \\ SIMP_TAC std_ss [read_while_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `P h` \\ ASM_SIMP_TAC std_ss []);

val mc_read_until_newline_thm = prove(
  ``!zs io.
      mc_read_until_newline_pre (REPLACE_INPUT_IO zs io) /\
      (mc_read_until_newline (REPLACE_INPUT_IO zs io) =
       REPLACE_INPUT_IO (SND (read_while (\x. x <> #"\n") zs "")) io)``,
  Induct \\ ONCE_REWRITE_TAC [mc_read_until_newline_def]
  \\ SIMP_TAC std_ss [MAP,LET_DEF,IO_INPUT_LEMMA,APPEND,EVAL ``~0w:word64``]
  \\ ASM_SIMP_TAC wstd_ss [word_lo_n2w,read_while_def] \\ REPEAT STRIP_TAC
  \\ `ORD h < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
  \\ `~(255 < ORD h)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h = #"\n"` \\ ASM_SIMP_TAC std_ss [EVAL ``ORD #"\n"``]
  \\ `~(ORD h = 10)` by ALL_TAC THEN1
      (ONCE_REWRITE_TAC [GSYM (EVAL ``ORD #"\n"``)] \\ FULL_SIMP_TAC std_ss [ORD_11])
  \\ FULL_SIMP_TAC wstd_ss [n2w_11]
  \\ ONCE_REWRITE_TAC [SND_read_while] \\ FULL_SIMP_TAC std_ss []);


(* read space chars -- test for end of file *)

val (mc_test_eof_spec,mc_test_eof_def) = basic_decompile_strings x64_tools "mc_test_eof"
  (SOME (``io:io_streams``,
         ``(r0:word64,r8:word64,io:io_streams)``))
  (assemble "x64" `
START:
       insert io_read
       cmp r0,32
       ja NOT_SPACE
       insert io_next
       jmp START
NOT_SPACE:
       cmp r0,255
       ja TRUE
       cmp r0,59
       je COMMENT
       mov r8d,3
       jmp EXIT
COMMENT:
       mov r0d,0
       insert io_next
       insert mc_read_until_newline
       mov r0d,0
       jmp START
TRUE:
       mov r8d,11
EXIT:
       mov r0d,3
     `);

val _ = save_thm("mc_test_eof_spec",mc_test_eof_spec);

val mc_test_eof_lemma = prove(
  ``!cs.
      mc_test_eof_pre (REPLACE_INPUT_IO (cs) io) /\
      (mc_test_eof (REPLACE_INPUT_IO (cs) io) =
                   (3w,if FST (is_eof cs) then 11w else 3w,
                    REPLACE_INPUT_IO (SND (is_eof cs)) io))``,
  HO_MATCH_MP_TAC is_eof_ind \\ STRIP_TAC THEN1
   (ONCE_REWRITE_TAC [mc_test_eof_def]
    \\ SIMP_TAC std_ss [MAP,MAP,IO_INPUT_LEMMA,LET_DEF] \\ EVAL_TAC)
  \\ NTAC 3 STRIP_TAC \\ Cases_on `space_char c` \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [mc_test_eof_def]
  \\ ONCE_REWRITE_TAC [is_eof_def]
  \\ SIMP_TAC std_ss [MAP,IO_INPUT_LEMMA,LET_DEF]
  \\ SIMP_TAC wstd_ss [w2w_def,w2n_n2w,word_lo_n2w,space_char_def,GSYM NOT_LESS]
  \\ FULL_SIMP_TAC std_ss [space_char_def,DECIDE ``32 < n = ~(n <= 32)``]
  \\ `ORD c < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
  \\ `~(255 < ORD c)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `c = #";"`
  \\ FULL_SIMP_TAC std_ss [mc_read_until_newline_thm, EVAL ``ORD #";"``]
  \\ Cases_on `c`
  \\ FULL_SIMP_TAC wstd_ss [ORD_CHR_RWT,n2w_11,CHR_11]);

val MAP_MAP_LEMMA = prove(
  ``!xs. MAP (n2w o ORD) (MAP (CHR o w2n) xs) = xs:word8 list``,
  Induct \\ ASM_SIMP_TAC std_ss [MAP,CONS_11]
  \\ Cases \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,ORD_CHR_RWT]);

val getINPUT_EQ_NIL = prove(
  ``!io. (f (getINPUT io) = "") =
         (getINPUT (IO_INPUT_APPLY f io) = [])``,
  Cases \\ SIMP_TAC std_ss [getINPUT_def,IO_INPUT_APPLY_def,
    REPLACE_INPUT_IO_def,MAP_EQ_NIL]);

val mc_test_eof_thm = prove(
  ``^LISP ==>
    ?v0 io2.
      mc_test_eof_pre io /\
      (mc_test_eof io = (tw0,w2w v0,io2)) /\
      (io2 = IO_INPUT_APPLY (SND o is_eof) io) /\
      let (io,w0,x0) = (io2,v0,LISP_TEST (FST (is_eof (getINPUT io)))) in ^LISP``,
  SIMP_TAC std_ss [RW [IO_INPUT_LEMMA,GSYM IO_INPUT_APPLY_def,MAP_MAP_LEMMA] (Q.SPEC `((getINPUT io))` mc_test_eof_lemma)]
  \\ SIMP_TAC std_ss [IO_INPUT_APPLY_def,LET_DEF] \\ STRIP_TAC
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ Cases_on `FST (is_eof (getINPUT io))` \\ FULL_SIMP_TAC std_ss []
  THEN1
   (Q.EXISTS_TAC `0xBw` \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,LISP_TEST_def]
    \\ METIS_TAC [el 2 (CONJUNCTS lisp_inv_Sym),lisp_inv_ignore_io])
  THEN1
   (Q.EXISTS_TAC `0x3w` \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,LISP_TEST_def]
    \\ METIS_TAC [el 1 (CONJUNCTS lisp_inv_Sym),lisp_inv_ignore_io]));

val _ = save_thm("mc_test_eof_thm",mc_test_eof_thm);


(* read number *)

val (thm,mc_read_num_def) = basic_decompile_strings x64_tools "mc_read_num"
  (SOME (``(r8:word64,io:io_streams)``,
         ``(r8:word64,io:io_streams)``))
  (assemble "x64" `
START:
       insert io_read
       cmp r0,57
       ja EXIT
       cmp r0,48
       jb EXIT
       insert io_next
       sub r0,48
       xchg r8,r0
       lea r0,[4*r0+r0]
       add r0,r0
       xchg r8,r0
       add r8,r0
       cmp r8,1073741824
       jb START
       xor r8,r8
       not r8
       jmp START
EXIT:
     `)

val PUSH_IF = METIS_PROVE []
  ``((if b then mc_read_num (x1,y) else mc_read_num (x2,y)) =
     mc_read_num (if b then x1 else x2,y)) /\
    ((if b then mc_read_num_pre (x1,y) else mc_read_num_pre (x2,y)) =
     mc_read_num_pre (if b then x1 else x2,y))``

val mc_read_num_lemma = prove(
  ``!cs cs2 n.
      EVERY number_char cs /\ (~(cs2 = []) ==> (~number_char (HD cs2))) ==>
      mc_read_num_pre (if n < 2**30 then (n2w n) else ~0w,
                       REPLACE_INPUT_IO ((cs ++ cs2)) io) /\
      (mc_read_num (if n < 2**30 then (n2w n) else ~0w,
                    REPLACE_INPUT_IO ((cs ++ cs2)) io) =
                   (if 10**(LENGTH cs) * n + str2num cs < 2**30 then
                      n2w (10**(LENGTH cs) * n + str2num cs) else ~0w,
                    REPLACE_INPUT_IO (cs2) io))``,
  Induct THEN1
   (SIMP_TAC std_ss [LENGTH,str2num_def,APPEND] \\ Cases
    \\ ONCE_REWRITE_TAC [mc_read_num_def] THEN1
     (SIMP_TAC std_ss [MAP,LET_DEF,IO_INPUT_LEMMA]
      \\ SIMP_TAC std_ss [IO_INPUT_LEMMA,LET_DEF,EVAL ``~0w:word64``]
      \\ SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w])
    \\ SIMP_TAC std_ss [MAP,LET_DEF,IO_INPUT_LEMMA]
    \\ `ORD h < 256` by METIS_TAC [ORD_BOUND]
    \\ `ORD h < 18446744073709551616` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,word_lo_n2w,number_char_def]
    \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL,HD]
    \\ SIMP_TAC std_ss [LESS_EQ,ADD1]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `58 <= ORD h` \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `ORD h + 1 <= 48` \\ ASM_SIMP_TAC std_ss []
    \\ `F` by DECIDE_TAC)
  \\ SIMP_TAC std_ss [read_while_def,LET_DEF,LENGTH,str2num_def,MAP]
  \\ ONCE_REWRITE_TAC [mc_read_num_def]
  \\ SIMP_TAC std_ss [IO_INPUT_LEMMA,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [MAP,IO_INPUT_LEMMA,APPEND]
  \\ STRIP_TAC
  \\ `ORD h < 256` by METIS_TAC [ORD_BOUND]
  \\ `ORD h < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,word_lo_n2w,number_char_def,EVERY_DEF]
  \\ NTAC 3 STRIP_TAC
  \\ `~(57 < ORD h)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `~(ORD h < 48)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [word_mul_n2w,word_add_n2w,DECIDE ``4*n+n+(4*n+n)=10*n``]
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma2,word_add_n2w]
  \\ REVERSE (Cases_on `n < 1073741824`) THEN1
   (ASM_SIMP_TAC std_ss [EVAL ``~0w:word64``,word_mul_n2w,word_add_n2w]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,word_lo_n2w]
    \\ ONCE_REWRITE_TAC [MATCH_MP (GSYM MOD_PLUS) (DECIDE ``0 < 18446744073709551616:num``)]
    \\ SIMP_TAC std_ss []
    \\ `(ORD h - 48) < 18446744073709551616` by DECIDE_TAC
    \\ `(18446744073709551606 + (ORD h - 48)) < 18446744073709551616` by DECIDE_TAC
    \\ `~(18446744073709551606 + (ORD h - 48) < 1073741824)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [number_char_def]
    \\ FULL_SIMP_TAC std_ss [EVAL ``~0w:word64``]
    \\ RES_TAC \\ REPEAT (POP_ASSUM (MP_TAC o Q.SPEC`n`))
    \\ Q.PAT_ASSUM `!csss. bbb` (K ALL_TAC)
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [EXP]
    \\ Cases_on `(10:num) ** (LENGTH cs)` \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
    \\ `~(n' * n + n + str2num cs < 1073741824)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [RIGHT_ADD_DISTRIB]
    \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC std_ss [DECIDE ``10*n=n+9*n``,GSYM ADD_ASSOC]
    \\ IMP_RES_TAC (DECIDE ``n+m<k==>n<k:num``))
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [word_mul_n2w,word_add_n2w,DECIDE ``4*n+n+(4*n+n)=10*n``]
  \\ `(10 * n + (ORD h - 48)) < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,PUSH_IF]
  \\ FULL_SIMP_TAC std_ss [number_char_def]
  \\ SIMP_TAC std_ss [EXP,LEFT_ADD_DISTRIB]
  \\ SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM,AC ADD_ASSOC ADD_COMM]);

val ORD_BOUND_LEMMA = prove(
  ``ORD h < 1073741872``,
  METIS_TAC [DECIDE ``256 < 1073741872:num``,ORD_BOUND,LESS_TRANS]);

val mc_read_num_thm = mc_read_num_lemma
  |> Q.SPECL [`cs1`,`cs2`,`ORD h - 48`]
  |> SIMP_RULE std_ss [RW1[MULT_COMM](GSYM str2num_def)]
  |> SIMP_RULE std_ss [ORD_BOUND_LEMMA] |> GEN_ALL

val mc_read_num_thm0 = mc_read_num_lemma
  |> Q.SPECL [`cs1`,`cs2`,`0`] |> SIMP_RULE std_ss []

val read_while_SPLIT_lemma = prove(
  ``!xs ys P.
      EVERY P ys ==>
      ?xs1 xs2. (read_while P xs ys = (xs1,xs2)) /\ (ys ++ xs = xs1 ++ xs2) /\
                EVERY P xs1 /\ (xs2 <> "" ==> ~P (HD xs2))``,
  Induct \\ SIMP_TAC std_ss [read_while_def,APPEND,EVERY_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `P h` \\ ASM_SIMP_TAC std_ss [] THEN1
   (`EVERY P (ys ++ [h])` by ASM_SIMP_TAC std_ss [EVERY_APPEND,EVERY_DEF]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND])
  \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL,HD]);

val read_while_SPLIT = read_while_SPLIT_lemma
  |> Q.SPECL [`xs`,`[]`] |> RW [EVERY_DEF] |> Q.GEN `xs`;


(* read symbol *)

val (thm,mc_read_barsym_0_def) = basic_decompile_strings x64_tools "mc_read_barsym_0"
  (SOME (``(r0:word64)``,
         ``(r0:word64)``))
  (assemble "x64" `
       cmp r0,48
       jne EXIT
       xor r0d,r0d
EXIT:
     `)

val (thm,mc_read_barsym_def) = basic_decompile_strings x64_tools "mc_read_barsym"
  (SOME (``(r9:word64,r10:word64,r15:word64,io:io_streams,dg:word64 set,g:word64->word8)``,
         ``(r9:word64,r15:word64,io:io_streams,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
START:
       insert io_read
       cmp r0,255
       ja EXIT
       insert io_next
       test r10,r10
       jne SKIP
       cmp r0,124
       je EXIT
       not r10
       cmp r0,92
       je START
       mov [r9+r15],r0b
       inc r15
       not r10
       cmp r15,254
       jna START
       jmp EXIT
SKIP:
       insert mc_read_barsym_0
       mov [r9+r15],r0b
       inc r15
       not r10
       cmp r15,254
       jna START
EXIT:
     `)

val mc_read_barsym_thm = prove(
  ``!cs b cs1 cs2 r15 r15i g p xs.
      (str2sym_aux cs b = (cs1,cs2)) /\
      LENGTH cs1 + w2n r15 < 255 /\ (LENGTH xs = LENGTH cs1) ==>
      (one_string (r9+r15) xs * p) (fun2set (g,dg)) ==>
      ?g2 cs3 r15i.
        mc_read_barsym_pre (r9,if b then ~0w else 0w,r15,REPLACE_INPUT_IO (cs) io,dg,g) /\
        (mc_read_barsym (r9,if b then ~0w else 0w,r15,REPLACE_INPUT_IO (cs) io,dg,g) =
           (r9,r15 + n2w (LENGTH cs1),REPLACE_INPUT_IO (cs2) io,dg,g2)) /\
        (one_string (r9+r15) cs1 * p) (fun2set (g2,dg))``,
  Induct \\ SIMP_TAC std_ss [MAP] THEN1
   (ONCE_REWRITE_TAC [mc_read_barsym_def]
    \\ SIMP_TAC std_ss [IO_INPUT_LEMMA,LET_DEF,EVAL ``0xFFw <+ ~0x0w:word64``]
    \\ SIMP_TAC std_ss [str2sym_aux_def,LENGTH,MAP,WORD_ADD_0,LENGTH_NIL])
  \\ ONCE_REWRITE_TAC [mc_read_barsym_def]
  \\ SIMP_TAC wstd_ss [IO_INPUT_LEMMA,LET_DEF,w2w_def,w2n_n2w,word_lo_n2w]
  \\ STRIP_TAC \\ `ORD h < 256` by FULL_SIMP_TAC wstd_ss []
  \\ `~(255 < ORD h)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Cases \\ ASM_SIMP_TAC wstd_ss [n2w_11,EVAL ``~0w = 0w:word64``] THEN1
   (SIMP_TAC std_ss [str2sym_aux_def]
    \\ `?x1 x2. str2sym_aux cs F = (x1,x2)` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,LENGTH,WORD_NOT_NOT]
    \\ NTAC 5 STRIP_TAC
    \\ `~(0xFEw <+ r15 + 0x1w) /\ STRLEN x1 + w2n (r15 + 0x1w) < 255` by ALL_TAC THEN1
     (NTAC 4 (POP_ASSUM MP_TAC) \\ Q.SPEC_TAC (`r15`,`w`) \\ Cases
      \\ ASM_SIMP_TAC wstd_ss [w2n_n2w,word_add_n2w,word_lo_n2w,LENGTH]
      \\ REPEAT STRIP_TAC \\ `n + 1 < 256` by DECIDE_TAC
      \\ FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
    \\ Q.PAT_ASSUM `!b.bbb` (MP_TAC o Q.SPEC `F`)
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [one_string_def,one_byte_list_def,MAP]
    \\ Q.ABBREV_TAC `g6 = (r15 + r9 =+ n2w (w2n (mc_read_barsym_0 (n2w (ORD h))))) g`
    \\ `(one (r9 + r15,n2w (w2n (mc_read_barsym_0 (n2w (ORD h))))) *
         one_byte_list (r9 + r15 + 0x1w) (MAP (n2w o ORD) t) * p)
           (fun2set (g6,dg)) /\ r15 + r9 IN dg` by
       (Q.UNABBREV_TAC `g6` \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC] \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
    \\ SEP_I_TAC "mc_read_barsym"
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * one (r9 + r15,n2w (w2n (mc_read_barsym_0 (n2w (ORD h)))))`,`t`])
    \\ `w2n (mc_read_barsym_0 (n2w (ORD h))) = ORD (if h = #"0" then #"\^@" else h)` by ALL_TAC THEN1
     (SIMP_TAC wstd_ss [mc_read_barsym_0_def,LET_DEF,n2w_11]
      \\ Cases_on `h` \\ ASM_SIMP_TAC std_ss [ORD_CHR_RWT,CHR_11]
      \\ Cases_on `n = 48` \\ ASM_SIMP_TAC wstd_ss [ORD_CHR_RWT,w2n_n2w])
    \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_COMM WORD_ADD_ASSOC,GSYM word_add_n2w])
  \\ SIMP_TAC std_ss [str2sym_aux_def]
  \\ Cases_on `h` \\ ASM_SIMP_TAC std_ss [CHR_11,ORD_CHR_RWT,WORD_NOT_NOT]
  \\ Cases_on `n = 92` \\ ASM_SIMP_TAC std_ss [] THEN1
   (Q.PAT_ASSUM `!b.bbb` (MP_TAC o Q.SPEC `T`)
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC)
  \\ Cases_on `n = 124` \\ ASM_SIMP_TAC std_ss []
  THEN1 SIMP_TAC std_ss [LENGTH,LENGTH_NIL,WORD_ADD_0]
  \\ `?x1 x2. str2sym_aux cs F = (x1,x2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,LENGTH,WORD_NOT_NOT]
  \\ NTAC 5 STRIP_TAC
  \\ `~(0xFEw <+ r15 + 0x1w) /\ STRLEN x1 + w2n (r15 + 0x1w) < 255` by ALL_TAC THEN1
     (NTAC 4 (POP_ASSUM MP_TAC) \\ Q.SPEC_TAC (`r15`,`w`) \\ Cases
      \\ ASM_SIMP_TAC wstd_ss [w2n_n2w,word_add_n2w,word_lo_n2w,LENGTH]
      \\ REPEAT STRIP_TAC \\ `n' + 1 < 255` by DECIDE_TAC
      \\ `(n' + 1) < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ Q.PAT_ASSUM `!b.bbb` (MP_TAC o Q.SPEC `F`)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [one_string_def,one_byte_list_def,MAP]
  \\ Q.ABBREV_TAC `g6 = (r15 + r9 =+ n2w n) g`
  \\ `(one (r9 + r15,n2w n) *
       one_byte_list (r9 + r15 + 0x1w) (MAP (n2w o ORD) t) * p)
           (fun2set (g6,dg)) /\ r15 + r9 IN dg` by
       (Q.UNABBREV_TAC `g6` \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC] \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [ORD_CHR_RWT]
  \\ SEP_I_TAC "mc_read_barsym"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * one (r9 + r15,n2w n)`,`t`])
  \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_COMM WORD_ADD_ASSOC,GSYM word_add_n2w]);

val mc_read_barsym_overflow_thm = prove(
  ``!cs b cs1 cs2 r15 g p xs.
      (str2sym_aux cs b = (cs1,cs2)) /\
      (254 <= LENGTH cs1 + w2n r15) /\
      (LENGTH xs <= LENGTH cs1) /\ (LENGTH xs = 255 - w2n r15) /\ w2n r15 < 255 ==>
      (one_string (r9+r15) xs * p) (fun2set (g,dg)) ==>
      ?g2 io2 xs2.
        mc_read_barsym_pre (r9,if b then ~0w else 0w,r15,REPLACE_INPUT_IO cs io,dg,g) /\
        (mc_read_barsym (r9,if b then ~0w else 0w,r15,REPLACE_INPUT_IO cs io,dg,g) =
           (r9,255w,io2,dg,g2)) /\
        (one_string (r9+r15) xs2 * p) (fun2set (g2,dg)) /\
        (LENGTH xs2 = LENGTH xs)``,
  Induct \\ SIMP_TAC std_ss [MAP] THEN1
   (SIMP_TAC std_ss [str2sym_aux_def,LENGTH] \\ REPEAT STRIP_TAC
    \\ `F` by DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [mc_read_barsym_def]
  \\ SIMP_TAC wstd_ss [IO_INPUT_LEMMA,LET_DEF,w2w_def,w2n_n2w,word_lo_n2w]
  \\ STRIP_TAC \\ `ORD h < 256` by FULL_SIMP_TAC wstd_ss []
  \\ `~(255 < ORD h)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Cases \\ ASM_SIMP_TAC wstd_ss [n2w_11,EVAL ``~0w = 0w:word64``] THEN1
   (SIMP_TAC std_ss [str2sym_aux_def]
    \\ `?x1 x2. str2sym_aux cs F = (x1,x2)` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,LENGTH,WORD_NOT_NOT]
    \\ NTAC 5 STRIP_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ FULL_SIMP_TAC wstd_ss [w2n_n2w] THEN1 (`F` by DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [IO_INPUT_LEMMA,APPEND]
    \\ ASM_SIMP_TAC wstd_ss [IO_INPUT_LEMMA,LET_DEF,w2w_def,w2n_n2w,word_lo_n2w]
    \\ Q.PAT_ASSUM `!b.bbb` (MP_TAC o Q.SPEC `F`)
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [one_string_def,one_byte_list_def,MAP]
    \\ Q.ABBREV_TAC `g6 = (r15 + r9 =+ n2w (w2n (mc_read_barsym_0 (n2w (ORD h))))) g`
    \\ `(one (r9 + r15,n2w (w2n (mc_read_barsym_0 (n2w (ORD h))))) *
         one_byte_list (r9 + r15 + 0x1w) (MAP (n2w o ORD) t) * p)
           (fun2set (g6,dg)) /\ r15 + r9 IN dg` by
       (Q.UNABBREV_TAC `g6` \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC] \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
    \\ `w2n (mc_read_barsym_0 (n2w (ORD h))) = ORD (if h = #"0" then #"\^@" else h)` by ALL_TAC THEN1
     (SIMP_TAC wstd_ss [mc_read_barsym_0_def,LET_DEF,n2w_11]
      \\ Cases_on `h` \\ ASM_SIMP_TAC std_ss [ORD_CHR_RWT,CHR_11]
      \\ Cases_on `n = 48` \\ ASM_SIMP_TAC wstd_ss [ORD_CHR_RWT,w2n_n2w])
    \\ SEP_R_TAC
    \\ Cases_on `0xFEw <+ r15 + 0x1w` \\ FULL_SIMP_TAC std_ss [] THEN1
     (Cases_on `r15` \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,word_lo_n2w,word_add_n2w]
      \\ `n+1 < 18446744073709551616` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
      \\ `n = 254` by DECIDE_TAC \\ FULL_SIMP_TAC wstd_ss [n2w_11]
      \\ Q.EXISTS_TAC `(if h = #"0" then #"\^@" else h)::t`
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,LENGTH,MAP,word_arith_lemma1])
    \\ SEP_I_TAC "mc_read_barsym"
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * one (r9 + r15,n2w (w2n (mc_read_barsym_0 (n2w (ORD h)))))`,`t`])
    \\ Cases_on `r15`
    \\ FULL_SIMP_TAC wstd_ss [word_add_n2w,w2n_n2w,word_lo_n2w]
    \\ `(n + 1) < 18446744073709551616` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC wstd_ss [word_add_n2w,w2n_n2w,word_lo_n2w]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_COMM WORD_ADD_ASSOC,GSYM word_add_n2w]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(if h = #"0" then #"\^@" else h) :: xs2`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [LENGTH,MAP,one_byte_list_def,WORD_ADD_ASSOC]
    \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC wstd_ss [IO_INPUT_LEMMA,LET_DEF,w2w_def,w2n_n2w,word_lo_n2w,APPEND]
  \\ SIMP_TAC std_ss [str2sym_aux_def]
  \\ Cases_on `h` \\ ASM_SIMP_TAC std_ss [CHR_11,ORD_CHR_RWT,WORD_NOT_NOT]
  \\ Cases_on `n = 92` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC wstd_ss [n2w_11]
    \\ Q.PAT_ASSUM `!b.bbb` (MP_TAC o Q.SPEC `T`)
    \\ ASM_SIMP_TAC std_ss [LENGTH] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `!xx.bbb` (MATCH_MP_TAC o RW [AND_IMP_INTRO])
    \\ Q.EXISTS_TAC `xs` \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `n = 124` \\ ASM_SIMP_TAC std_ss [] THEN1
   (SIMP_TAC std_ss [LENGTH,LENGTH_NIL,WORD_ADD_0]
    \\ REPEAT STRIP_TAC \\ `F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC wstd_ss [n2w_11]
  \\ `?x1 x2. str2sym_aux cs F = (x1,x2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,LENGTH,WORD_NOT_NOT]
  \\ NTAC 5 STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1] THEN1 (`F` by DECIDE_TAC)
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [one_string_def,one_byte_list_def,MAP]
  \\ Q.ABBREV_TAC `g6 = (r15 + r9 =+ n2w n) g`
  \\ `(one (r9 + r15,n2w n) *
       one_byte_list (r9 + r15 + 0x1w) (MAP (n2w o ORD) t) * p)
           (fun2set (g6,dg)) /\ r15 + r9 IN dg` by
       (Q.UNABBREV_TAC `g6` \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC] \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ SEP_R_TAC
  \\ Cases_on `0xFEw <+ r15 + 0x1w` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Cases_on `r15` \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,word_lo_n2w,word_add_n2w]
    \\ `n'+1 < 18446744073709551616` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `n' = 254` by DECIDE_TAC \\ FULL_SIMP_TAC wstd_ss [n2w_11]
    \\ Q.EXISTS_TAC `CHR n::t`
    \\ FULL_SIMP_TAC std_ss [one_byte_list_def,LENGTH,MAP,word_arith_lemma1,ORD_CHR_RWT])
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ Q.PAT_ASSUM `!b.bbb` (MP_TAC o Q.SPEC `F`)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [ORD_CHR_RWT]
  \\ SEP_I_TAC "mc_read_barsym"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * one (r9 + r15,n2w n)`,`t`])
  \\ Cases_on `r15`
  \\ FULL_SIMP_TAC wstd_ss [word_add_n2w,w2n_n2w,word_lo_n2w]
  \\ `(n' + 1) < 18446744073709551616` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC wstd_ss [word_add_n2w,w2n_n2w,word_lo_n2w]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_COMM WORD_ADD_ASSOC,GSYM word_add_n2w]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `CHR n :: xs2`
  \\ FULL_SIMP_TAC (std_ss++star_ss) [LENGTH,MAP,one_byte_list_def,WORD_ADD_ASSOC,ORD_CHR_RWT]
  \\ DECIDE_TAC);

val (thm,mc_read_stdsym_0_def) = basic_decompile_strings x64_tools "mc_read_stdsym_0"
  (SOME (``(r0:word64)``,
         ``(r0:word64)``))
  (assemble "x64" `
       cmp r0,96
       jna EXIT
       cmp r0,122
       ja EXIT
       sub r0,32
EXIT:
     `)

val mc_read_stdsym_0_thm = prove(
  ``!c. mc_read_stdsym_0 (n2w (ORD c)) = n2w (ORD (upper_case c))``,
  Cases \\ ASM_SIMP_TAC wstd_ss [mc_read_stdsym_0_def,word_lo_n2w,
    upper_case_def,LET_DEF,is_lower_case_def,CHR_11,char_le_def,ORD_CHR_RWT]
  \\ SIMP_TAC std_ss [LESS_EQ,ADD1]
  \\ Cases_on `97 <= n` \\ ASM_SIMP_TAC std_ss [ORD_CHR_RWT]
  \\ ASM_SIMP_TAC std_ss [DECIDE ``n <= 122 = ~(123 <= n:num)``]
  \\ Cases_on `123 <= n` \\ ASM_SIMP_TAC std_ss [ORD_CHR_RWT]
  \\ `~(n < 32) /\ n - 32 < 256` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma2,ORD_CHR_RWT]);

val (thm,mc_read_stdsym_def) = basic_decompile_strings x64_tools "mc_read_stdsym"
  (SOME (``(r9:word64,r15:word64,io:io_streams,dg:word64 set,g:word64->word8)``,
         ``(r9:word64,r15:word64,io:io_streams,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
START:
       insert io_read
       cmp r0,255
       ja EXIT
       cmp r0,41
       jna EXIT
       cmp r0,46
       je EXIT
       cmp r0,59
       je EXIT
       cmp r0,124
       je EXIT
       insert io_next
       insert mc_read_stdsym_0
       mov [r9+r15],r0b
       inc r15
       cmp r15,254
       jna START
EXIT:
     `)

val mc_read_stdsym_thm = prove(
  ``!cs cs2 r15 g p xs.
      EVERY identifier_char cs /\ (~(cs2 = []) ==> (~identifier_char (HD cs2))) ==>
      LENGTH cs + w2n r15 < 255 /\ (LENGTH xs = LENGTH cs) ==>
      (one_string (r9+r15) xs * p) (fun2set (g,dg)) ==>
      ?g2.
        mc_read_stdsym_pre (r9,r15,REPLACE_INPUT_IO ((cs ++ cs2)) io,dg,g) /\
        (mc_read_stdsym (r9,r15,REPLACE_INPUT_IO ((cs ++ cs2)) io,dg,g) =
           (r9,r15 + n2w (LENGTH cs),REPLACE_INPUT_IO ((cs2)) io,dg,g2)) /\
        (one_string (r9+r15) (MAP upper_case cs) * p) (fun2set (g2,dg))``,
  Induct THEN1
   (SIMP_TAC std_ss [LENGTH,LENGTH_NIL,EVERY_DEF] \\ Cases
    \\ ASM_SIMP_TAC std_ss [HD,APPEND,MAP] THEN1
     (ONCE_REWRITE_TAC [mc_read_stdsym_def]
      \\ SIMP_TAC std_ss [IO_INPUT_LEMMA,LET_DEF,EVAL ``0xFFw <+ ~0x0w:word64``]
      \\ SIMP_TAC std_ss [WORD_ADD_0] \\ METIS_TAC [])
    \\ SIMP_TAC std_ss [NOT_CONS_NIL]
    \\ ONCE_REWRITE_TAC [mc_read_stdsym_def]
    \\ SIMP_TAC wstd_ss [IO_INPUT_LEMMA,LET_DEF,w2w_def,w2n_n2w,word_lo_n2w,n2w_11]
    \\ `ORD h < 256` by FULL_SIMP_TAC wstd_ss []
    \\ `~(255 < ORD h)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [DECIDE ``41<n=42<=n:num``]
    \\ SIMP_TAC std_ss [identifier_char_def]
    \\ NTAC 5 STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_ADD_0] \\ METIS_TAC [])
  \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [mc_read_stdsym_def]
  \\ SIMP_TAC wstd_ss [IO_INPUT_LEMMA,LET_DEF,w2w_def,w2n_n2w,word_lo_n2w,n2w_11,MAP,APPEND]
  \\ `ORD h < 256` by FULL_SIMP_TAC wstd_ss []
  \\ `~(255 < ORD h)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [EVERY_DEF,identifier_char_def]
  \\ SIMP_TAC std_ss [DECIDE ``41<n=42<=n:num``]
  \\ NTAC 7 STRIP_TAC
  \\ `~(0xFEw <+ r15 + 0x1w) /\ STRLEN cs + w2n (r15 + 0x1w) < 255` by ALL_TAC THEN1
   (NTAC 4 (POP_ASSUM MP_TAC) \\ Q.SPEC_TAC (`r15`,`w`) \\ Cases
    \\ ASM_SIMP_TAC wstd_ss [w2n_n2w,word_add_n2w,word_lo_n2w,LENGTH]
    \\ REPEAT STRIP_TAC \\ `n + 1 < 255 /\ n + 1 < 256` by DECIDE_TAC
    \\ FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,mc_read_stdsym_0_thm]
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ Q.ABBREV_TAC `g4 = (r15 + r9 =+ n2w (ORD (upper_case h))) g`
  \\ FULL_SIMP_TAC std_ss [one_string_def,MAP,one_byte_list_def]
  \\ STRIP_TAC
  \\ `(one_byte_list (r9 + r15 + 0x1w) (MAP (n2w o ORD) t) * (p * one (r9 + r15,n2w (ORD (upper_case h)))))
           (fun2set (g4,dg)) /\ r15 + r9 IN dg` by
       (Q.UNABBREV_TAC `g4` \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC] \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ SEP_I_TAC "mc_read_stdsym"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * one (r9 + r15,n2w (ORD (upper_case h)))`,`t`])
  \\ FULL_SIMP_TAC (std_ss++star_ss) [identifier_char_def,AC WORD_ADD_COMM WORD_ADD_ASSOC,GSYM word_add_n2w]);

val mc_read_stdsym_overflow_thm = prove(
  ``!cs cs2 r15 g p xs.
      EVERY identifier_char cs ==>
      (255 <= LENGTH cs + w2n r15) /\
      (LENGTH xs <= LENGTH cs) /\ (LENGTH xs = 255 - w2n r15) /\ w2n r15 < 255 ==>
      (one_string (r9+r15) xs * p) (fun2set (g,dg)) ==>
      ?g2 io2 xs2.
        mc_read_stdsym_pre (r9,r15,REPLACE_INPUT_IO ((cs ++ cs2)) io,dg,g) /\
        (mc_read_stdsym (r9,r15,REPLACE_INPUT_IO ((cs ++ cs2)) io,dg,g) =
           (r9,255w,io2,dg,g2)) /\
        (one_string (r9+r15) xs2 * p) (fun2set (g2,dg)) /\
        (LENGTH xs2 = LENGTH xs)``,
  Induct THEN1
   (SIMP_TAC std_ss [LENGTH,LENGTH_NIL,EVERY_DEF] \\ Cases
    \\ FULL_SIMP_TAC std_ss [w2n_n2w,APPEND]
    \\ REPEAT STRIP_TAC \\ `F` by DECIDE_TAC)
  \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [mc_read_stdsym_def]
  \\ SIMP_TAC wstd_ss [IO_INPUT_LEMMA,LET_DEF,w2w_def,w2n_n2w,word_lo_n2w,n2w_11,MAP,APPEND]
  \\ `ORD h < 256` by FULL_SIMP_TAC wstd_ss []
  \\ `~(255 < ORD h)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [EVERY_DEF,identifier_char_def]
  \\ SIMP_TAC std_ss [DECIDE ``41<n=42<=n:num``]
  \\ NTAC 7 STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,mc_read_stdsym_0_thm]
  THEN1 (`F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ Q.ABBREV_TAC `g4 = (r15 + r9 =+ n2w (ORD (upper_case h))) g`
  \\ FULL_SIMP_TAC std_ss [one_string_def,MAP,one_byte_list_def]
  \\ STRIP_TAC
  \\ `(one_byte_list (r9 + r15 + 0x1w) (MAP (n2w o ORD) t) * (p * one (r9 + r15,n2w (ORD (upper_case h)))))
           (fun2set (g4,dg)) /\ r15 + r9 IN dg` by
       (Q.UNABBREV_TAC `g4` \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC] \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ Cases_on `0xFEw <+ r15 + 0x1w` \\ FULL_SIMP_TAC std_ss [] THEN1
   (NTAC 10 (POP_ASSUM MP_TAC) \\ Q.SPEC_TAC (`r15`,`w`) \\ Cases
    \\ ASM_SIMP_TAC wstd_ss [w2n_n2w,word_add_n2w,word_lo_n2w,LENGTH]
    \\ REPEAT STRIP_TAC \\ `n + 1 < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC wstd_ss []
    \\ `n = 254` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `t` \\ Q.EXISTS_TAC `[upper_case h]`
    \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,one_byte_list_def,SEP_CLAUSES,MAP]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ SEP_I_TAC "mc_read_stdsym"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * one (r9 + r15,n2w (ORD (upper_case h)))`,`t`])
  \\ FULL_SIMP_TAC (std_ss++star_ss) [identifier_char_def,AC WORD_ADD_COMM WORD_ADD_ASSOC,GSYM word_add_n2w]
  \\ NTAC 10 (POP_ASSUM MP_TAC) \\ Q.SPEC_TAC (`r15`,`w`) \\ Cases
  \\ ASM_SIMP_TAC wstd_ss [w2n_n2w,word_add_n2w,word_lo_n2w,LENGTH]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ `n + 1 < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC wstd_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `upper_case h :: xs2`
  \\ FULL_SIMP_TAC (std_ss++star_ss) [LENGTH,MAP,one_byte_list_def,WORD_ADD_ASSOC]
  \\ DECIDE_TAC);

val (thm,mc_read_sym_def) = basic_decompile_strings x64_tools "mc_read_sym"
  (SOME (``(r9:word64,io:io_streams,dg:word64 set,g:word64->word8)``,
         ``(r9:word64,r15:word64,io:io_streams,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
START:
       insert io_read
       xor r15,r15
       cmp r0,124
       je BAR
       cmp r0,255
       ja EXIT
       insert mc_read_stdsym_0
       mov [r9+r15],r0b
       inc r15
       insert io_next
       insert mc_read_stdsym
       jmp EXIT
BAR:
       insert io_next
       xor r10,r10
       insert mc_read_barsym
EXIT:
     `)

val mc_read_sym_thm = prove(
  ``!cs cs1 cs2 g p xs.
      (str2sym cs = (cs1,cs2)) /\
      LENGTH cs1 < 255 /\ (LENGTH xs = LENGTH cs1) ==>
      (one_string r9 xs * p) (fun2set (g,dg)) ==>
      ?g2 cs3 r15i.
        mc_read_sym_pre (r9,REPLACE_INPUT_IO (cs) io,dg,g) /\
        (mc_read_sym (r9,REPLACE_INPUT_IO (cs) io,dg,g) =
           (r9,n2w (LENGTH cs1),REPLACE_INPUT_IO (cs2) io,dg,g2)) /\
        (one_string r9 cs1 * p) (fun2set (g2,dg))``,
  SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [mc_read_sym_def]
  \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `IO_READ (REPLACE_INPUT_IO cs io) = 0x7Cw`
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC THEN1
   (Cases_on `cs` \\ FULL_SIMP_TAC wstd_ss [MAP,IO_INPUT_LEMMA,word_1comp_n2w,
      n2w_11,str2sym_def,HD,w2w_def,w2n_n2w]
    \\ Cases_on `h` \\ FULL_SIMP_TAC wstd_ss [CHR_11,NOT_CONS_NIL,ORD_CHR_RWT,TL]
    \\ `?x1 x2. str2sym_aux t F = (x1,x2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ EXPAND_TAC
    \\ ASSUME_TAC (GEN_ALL (Q.SPECL [`cs`,`F`,`cs1`,`cs2`,`0w`] mc_read_barsym_thm))
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_0]
    \\ SEP_I_TAC "mc_read_barsym" \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`p`,`xs`])
    \\ ASM_SIMP_TAC wstd_ss [w2n_n2w] \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `cs` THEN1
   (FULL_SIMP_TAC std_ss [MAP,IO_INPUT_LEMMA,EVAL ``0xFFw <+ ~0x0w:word64``,EVAL ``str2sym ""``]
    \\ EXPAND_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,MAP] \\ METIS_TAC [])
  \\ STRIP_ASSUME_TAC (Q.SPEC `identifier_char` (Q.ISPEC `t:string` read_while_SPLIT))
  \\ `~(0xFFw <+ IO_READ (REPLACE_INPUT_IO ((STRING h t)) io))` by ALL_TAC THEN1
   (FULL_SIMP_TAC wstd_ss [MAP,IO_INPUT_LEMMA,w2w_def,w2n_n2w,word_lo_n2w]
    \\ FULL_SIMP_TAC wstd_ss [DECIDE ``~(255<n) = (n<256)``])
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC wstd_ss [MAP,IO_INPUT_LEMMA,w2w_def,w2n_n2w,word_lo_n2w,WORD_ADD_0]
  \\ `str2sym (h::t) = (MAP upper_case (h::xs1),xs2)` by ALL_TAC THEN1
   (Cases_on `h`
    \\ Q.PAT_ASSUM `bbb = (cs1,cs2)` MP_TAC
    \\ FULL_SIMP_TAC wstd_ss [str2sym_def,HD,NOT_CONS_NIL,LET_DEF,MAP,IO_INPUT_LEMMA,
          w2w_def,w2n_n2w,n2w_11,CHR_11,ORD_CHR_RWT])
  \\ FULL_SIMP_TAC std_ss [APPEND] \\ EXPAND_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_MAP,MAP,LENGTH]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ASSUME_TAC (GEN_ALL (Q.SPECL [`cs1`,`cs2`,`1w`] mc_read_stdsym_thm))
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,LENGTH_MAP]
  \\ SEP_I_TAC "mc_read_stdsym" \\ POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * one_string r9 [upper_case h]`,`t'`])
  \\ ASM_SIMP_TAC wstd_ss [w2n_n2w]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ (c ==> d) ==> ((b ==> c) ==> d)``)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC wstd_ss [one_string_def,one_byte_list_def,MAP,SEP_CLAUSES,
      mc_read_stdsym_0_thm,w2n_n2w] \\ SEP_WRITE_TAC)
  \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,one_byte_list_def,SEP_CLAUSES,MAP]
  \\ ASM_SIMP_TAC wstd_ss [w2n_n2w] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,AC ADD_ASSOC ADD_COMM]
  \\ SEP_R_TAC);

val mc_read_sym_overflow_thm = prove(
  ``!cs cs1 cs2 g p xs.
      (str2sym cs = (cs1,cs2)) /\
      255 <= LENGTH cs1 /\ (LENGTH xs = 255) ==>
      (one_string r9 xs * p) (fun2set (g,dg)) ==>
      ?g2 io2 xs2.
        mc_read_sym_pre (r9,REPLACE_INPUT_IO (cs) io,dg,g) /\
        (mc_read_sym (r9,REPLACE_INPUT_IO (cs) io,dg,g) =
           (r9,255w,io2,dg,g2)) /\
        (one_string r9 xs2 * p) (fun2set (g2,dg)) /\
        (LENGTH xs = LENGTH xs2)``,
  SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [mc_read_sym_def]
  \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `IO_READ (REPLACE_INPUT_IO cs io) = 0x7Cw`
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC THEN1
   (CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    \\ Cases_on `cs` \\ FULL_SIMP_TAC wstd_ss [MAP,IO_INPUT_LEMMA,word_1comp_n2w,
      n2w_11,str2sym_def,HD,w2w_def,w2n_n2w]
    \\ Cases_on `h` \\ FULL_SIMP_TAC wstd_ss [CHR_11,NOT_CONS_NIL,ORD_CHR_RWT,TL]
    \\ `?x1 x2. str2sym_aux t F = (x1,x2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ EXPAND_TAC
    \\ ASSUME_TAC (GEN_ALL (Q.SPECL [`cs`,`F`,`cs1`,`cs2`,`0w`] mc_read_barsym_overflow_thm))
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_0]
    \\ SEP_I_TAC "mc_read_barsym" \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`p`,`xs`])
    \\ `255 <= STRLEN x1` by DECIDE_TAC
    \\ `254 <= STRLEN x1` by DECIDE_TAC
    \\ ASM_SIMP_TAC wstd_ss [w2n_n2w] \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `xs2` \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `cs` THEN1
   (FULL_SIMP_TAC std_ss [MAP,IO_INPUT_LEMMA,EVAL ``0xFFw <+ ~0x0w:word64``,EVAL ``str2sym ""``]
    \\ EXPAND_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,MAP] \\ METIS_TAC [])
  \\ STRIP_ASSUME_TAC (Q.SPEC `identifier_char` (Q.ISPEC `t:string` read_while_SPLIT))
  \\ `~(0xFFw <+ IO_READ (REPLACE_INPUT_IO ((STRING h t)) io))` by ALL_TAC THEN1
   (FULL_SIMP_TAC wstd_ss [MAP,IO_INPUT_LEMMA,w2w_def,w2n_n2w,word_lo_n2w]
    \\ FULL_SIMP_TAC wstd_ss [DECIDE ``~(255<n) = (n<256)``])
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC wstd_ss [MAP,IO_INPUT_LEMMA,w2w_def,w2n_n2w,word_lo_n2w,WORD_ADD_0]
  \\ `str2sym (h::t) = (MAP upper_case (h::xs1),xs2)` by ALL_TAC THEN1
   (Cases_on `h`
    \\ Q.PAT_ASSUM `bbb = (cs1,cs2)` MP_TAC
    \\ FULL_SIMP_TAC wstd_ss [str2sym_def,HD,NOT_CONS_NIL,LET_DEF,MAP,IO_INPUT_LEMMA,
          w2w_def,w2n_n2w,n2w_11,CHR_11,ORD_CHR_RWT])
  \\ FULL_SIMP_TAC std_ss [APPEND] \\ EXPAND_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_MAP,MAP,LENGTH]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ASSUME_TAC (GEN_ALL (Q.SPECL [`cs1`,`cs2`,`1w`] mc_read_stdsym_overflow_thm))
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,LENGTH_MAP]
  \\ SEP_I_TAC "mc_read_stdsym" \\ POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * one_string r9 [upper_case h]`,`t'`])
  \\ ASM_SIMP_TAC wstd_ss [w2n_n2w]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ (c ==> d) ==> ((b ==> c) ==> d)``)
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ (c ==> d) ==> ((b ==> c) ==> d)``)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC wstd_ss [one_string_def,one_byte_list_def,MAP,SEP_CLAUSES,
      mc_read_stdsym_0_thm,w2n_n2w] \\ SEP_WRITE_TAC)
  \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,one_byte_list_def,SEP_CLAUSES,MAP]
  \\ ASM_SIMP_TAC wstd_ss [w2n_n2w] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,AC ADD_ASSOC ADD_COMM]
  \\ SEP_R_TAC \\ Q.EXISTS_TAC `upper_case h::xs2'` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,one_byte_list_def,SEP_CLAUSES,MAP,LENGTH]);


(* string eq for insert symbol (below) *)

val (thm,mc_string_eq_def) = basic_decompile_strings x64_tools "mc_string_eq"
  (SOME (``(r8:word64,r9:word64,r11:word64,dg:word64 set,g:word64->word8)``,
         ``(r0:word64,r8:word64,r9:word64,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
START:
       test r11,r11
       je TRUE
       movzx r0,BYTE [r8+r11]
       cmp r0b,BYTE [r9+r11]
       jne FALSE
       dec r11
       jmp START
TRUE:
       xor r0,r0
       jmp EXIT
FALSE:
       mov r0d,1
EXIT:  `)

val mc_string_eq_blast = blastLib.BBLAST_PROVE
  ``!w. w2w ((w2w (w:word8)):word64) = w``

val APPEND_11_LEMMA = prove(
  ``!s1 t1 s2 t2.
      (LENGTH s1 = LENGTH t1) ==> ((s1 ++ s2 = t1 ++ t2) = (s1 = t1) /\ (s2 = t2))``,
  Induct \\ Cases_on `t1` \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,ADD1,CONS_11]
  \\ METIS_TAC []);

val mc_string_eq_thm = prove(
  ``!s t p.
      (LENGTH s = LENGTH t) /\ LENGTH t < 256 /\
      (one_string (a+1w) s * one_string (b+1w) t * p) (fun2set (g,dg)) ==>
      mc_string_eq_pre (a,b,n2w (LENGTH t),dg,g) /\
      (mc_string_eq (a,b,n2w (LENGTH t),dg,g) =
          ((if s = t then 0w else 1w),a,b,dg,g))``,
  HO_MATCH_MP_TAC rich_listTheory.SNOC_INDUCT \\ NTAC 3 STRIP_TAC
  THEN1 (Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_SNOC]
         \\ ONCE_REWRITE_TAC [mc_string_eq_def] \\ SIMP_TAC std_ss [LET_DEF])
  \\ NTAC 3 STRIP_TAC
  \\ `(t = []) \/ ?h2 tt. t = SNOC h2 tt` by METIS_TAC [rich_listTheory.SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_SNOC]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss [one_string_def,one_byte_list_def,MAP,MAP_APPEND,
       APPEND,one_byte_list_APPEND,SEP_CLAUSES,STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [GSYM one_string_def,LENGTH_MAP,word_arith_lemma1]
  \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [mc_string_eq_def] \\ SIMP_TAC std_ss [LET_DEF]
  \\ `(LENGTH tt + 1) < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC wstd_ss [n2w_11,CONS_11]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB,mc_string_eq_blast]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,AC ADD_ASSOC ADD_COMM]
  \\ Q.PAT_ASSUM `LENGTH s = LENGTH tt` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SEP_R_TAC \\ ASM_SIMP_TAC wstd_ss [n2w_11,ORD_11]
  \\ FULL_SIMP_TAC std_ss [APPEND_11_LEMMA,CONS_11]
  \\ Cases_on `x = h2` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!t.bbb` MATCH_MP_TAC
  \\ Q.EXISTS_TAC `one (a + n2w (STRLEN tt + 1),n2w (ORD h2)) *
                   one (b + n2w (STRLEN tt + 1),n2w (ORD h2)) * p`
  \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ DECIDE_TAC);


(* insert symbol *)

val (thm,mc_insert_sym_def) = basic_decompile_strings x64_tools "mc_insert_sym"
  (SOME (``(r7:word64,r8:word64,r9:word64,r10:word64,r15:word64,dg:word64 set,g:word64->word8,df:word64 set,f:word64->word32)``,
         ``(r7:word64,r8:word64,r9:word64,dg:word64 set,g:word64->word8,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
START:
       movzx r11, BYTE [r8]
       test r11,r11
       je INSERT
       cmp r15,r11
       je EQ
       add r8,r11
       inc r10
       jmp START
EQ:
       dec r11
       insert mc_string_eq
       test r0,r0
       je FOUND
       add r8,r15
       inc r10
       jmp START
INSERT:
       cmp r15,254
       ja ERROR
       mov r0,[r7-208]
       sub r0,[r7-216]
       sub r0,r15
       cmp r0,520
       jna ERROR2
       cmp r10,536870910
       ja ERROR2
       mov BYTE [r8],r15b
       mov BYTE [r8+r15],0
       mov r0,[r7-216]
       add r0,r15
       mov [r7-216],r0
FOUND:
       mov r8,r10
       shl r8,3
       or r8,3
       mov r9d,1
       jmp EXIT
ERROR2:
       mov r8d,29
       mov r9d,3
       jmp EXIT
ERROR:
       mov r8d,25
       mov r9d,3
EXIT:     `)

val mc_insert_sym_lemma1 = prove(
  ``!xs n k p a.
      (LIST_FIND n s xs = SOME k) /\ EVERY (\x. STRLEN x < 255) xs /\ LENGTH s < 256 /\
      (one_byte_list a (symbol_list xs) * one_string (r9+1w) s * p) (fun2set (g,dg)) ==>
      mc_insert_sym_pre (r7,a,r9,n2w n,n2w (LENGTH s + 1),dg,g,df,f) /\
      (mc_insert_sym (r7,a,r9,n2w n,n2w (LENGTH s + 1),dg,g,df,f) = (r7,n2w k << 3 !! 3w,1w,dg,g,df,f))``,
  Induct \\ SIMP_TAC std_ss [LIST_FIND_def]
  \\ SIMP_TAC std_ss [symbol_list_def,string_data_def,one_byte_list_def,
       one_byte_list_APPEND,LENGTH,LENGTH_MAP,ADD1]
  \\ FULL_SIMP_TAC std_ss [GSYM one_string_def,EVERY_DEF]
  \\ NTAC 6 STRIP_TAC
  \\ ONCE_REWRITE_TAC [mc_insert_sym_def]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ SEP_R_TAC
  \\ `LENGTH h + 1 < 256` by DECIDE_TAC
  \\ `LENGTH s + 1 < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,n2w_11]
  \\ ASM_SIMP_TAC wstd_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ REVERSE (Cases_on `LENGTH s = LENGTH h`) \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.PAT_ASSUM `!x.bb` MATCH_MP_TAC
    \\ Cases_on `s = h` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `one (a,n2w (STRLEN h + 1)) * one_string (a + 0x1w) h * p`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ ASSUME_TAC (GEN_ALL (Q.SPECL [`s1`,`s2`] mc_string_eq_thm))
  \\ Q.PAT_ASSUM `STRLEN s = STRLEN h` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [] \\ SEP_I_TAC "mc_string_eq"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`h`,`one (a,n2w (STRLEN h + 1)) *
       one_byte_list (a + n2w (STRLEN h + 1)) (symbol_list xs) * p`])
  \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ STRIP_TAC
  \\ REVERSE (Cases_on `h = s`) \\ FULL_SIMP_TAC wstd_ss [n2w_11] THEN1
   (Q.PAT_ASSUM `!x.bb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `one (a,n2w (STRLEN h + 1)) * one_string (a + 0x1w) h * p`
    \\ FULL_SIMP_TAC (std_ss++star_ss) []));

val mc_insert_sym_lemma2_blast = blastLib.BBLAST_PROVE
  ``(w2w ((w2w (w >>> 32)):word32) << 32 !! w2w ((w2w (w:word64)):word32) = w) /\
    ((63 >< 32) w = (w2w (w >>> 32)):word32) /\ ((31 >< 0) w = (w2w w):word32)``;

val mc_insert_sym_lemma2 = prove(
  ``!xs n k p a x r9.
      Abbrev (r9 = a + n2w (LENGTH (symbol_list xs)) - 1w) /\ (r7 && 3w = 0w) /\
      (LIST_FIND n s xs = NONE) /\ EVERY (\x. STRLEN x < 255) xs /\ LENGTH s < 256 /\
      (ref_static (r7 - 0xD8w) [sa2;sa3] * q) (fun2set (f,df)) /\
      (one_byte_list a (symbol_list xs) * one_string (r9+1w) s * one (r9+1w+n2w(LENGTH s),x) * p) (fun2set (g,dg)) ==>
      ?fail g2 f2 toosmall.
          mc_insert_sym_pre (r7,a,r9,n2w n,n2w (LENGTH s + 1),dg,g,df,f) /\
          (mc_insert_sym (r7,a,r9,n2w n,n2w (LENGTH s + 1),dg,g,df,f) =
             if fail then (r7,if toosmall then 25w else 29w,3w,dg,g,df,f) else
               (r7,n2w (n+LENGTH xs) << 3 !! 3w,1w,dg,g2,df,f2)) /\
          (~fail ==> 0x208w <+ sa3 - sa2 - n2w (STRLEN s + 1) /\
                     ~(536870910w <+ (n2w (n + LENGTH xs):word64)) /\
                     (ref_static (r7 - 0xD8w) [sa2+n2w (LENGTH s + 1);sa3] * q) (fun2set (f2,df)) /\
                     (one_byte_list a (symbol_list (xs ++ [s])) * p) (fun2set (g2,dg)))``,
  REVERSE Induct \\ SIMP_TAC std_ss [LIST_FIND_def] THEN1
   (STRIP_TAC \\ Cases_on `h = s` \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
    \\ SIMP_TAC std_ss [symbol_list_def,string_data_def,one_byte_list_def,
         one_byte_list_APPEND,LENGTH,LENGTH_MAP,ADD1]
    \\ FULL_SIMP_TAC std_ss [GSYM one_string_def,EVERY_DEF]
    \\ ONCE_REWRITE_TAC [mc_insert_sym_def]
    \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ SEP_R_TAC
    \\ `LENGTH h + 1 < 256` by DECIDE_TAC
    \\ `(STRLEN s + 1) < 18446744073709551616` by DECIDE_TAC
    \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,n2w_11]
    \\ REVERSE (Cases_on `LENGTH h = LENGTH s`) \\ ASM_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [word_add_n2w,APPEND,symbol_list_def]
      \\ FULL_SIMP_TAC std_ss [string_data_def,one_byte_list_def,
            one_byte_list_APPEND,LENGTH,LENGTH_APPEND,LENGTH_MAP]
      \\ FULL_SIMP_TAC std_ss [GSYM one_string_def]
      \\ `n + (LENGTH xs + 1) = (n+1) + LENGTH xs` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [ADD1]
      \\ SEP_I_TAC "mc_insert_sym"
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * (one (a,n2w (STRLEN h + 1)) * one_string (a + 0x1w) h)`,`x`])
      \\ FULL_SIMP_TAC (std_ss++star_ss) []
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,AC ADD_COMM ADD_ASSOC,ADD1]
      \\ FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def])
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
    \\ ASSUME_TAC (GEN_ALL (Q.SPECL [`s1`,`s2`] mc_string_eq_thm))
    \\ SEP_I_TAC "mc_string_eq"
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`h`,`one (a,n2w (STRLEN h + 1)) *
         one (r9 + 0x1w + n2w (STRLEN h),x) *
         one_byte_list (a + n2w (STRLEN h + 1)) (symbol_list xs) * p`])
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,word_add_n2w,AC ADD_ASSOC ADD_COMM]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ STRIP_TAC
    \\ FULL_SIMP_TAC wstd_ss [n2w_11] THEN1
     (FULL_SIMP_TAC std_ss [word_add_n2w,APPEND,symbol_list_def]
      \\ FULL_SIMP_TAC std_ss [string_data_def,one_byte_list_def,
            one_byte_list_APPEND,LENGTH,LENGTH_APPEND,LENGTH_MAP]
      \\ FULL_SIMP_TAC std_ss [GSYM one_string_def]
      \\ `n + (LENGTH xs + 1) = (n+1) + LENGTH xs` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [ADD1]
      \\ SEP_I_TAC "mc_insert_sym"
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * (one (a,n2w (STRLEN h + 1)) * one_string (a + 0x1w) h)`,`x`])
      \\ FULL_SIMP_TAC (std_ss++star_ss) []
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,AC ADD_COMM ADD_ASSOC,ADD1]
      \\ FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]))
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,symbol_list_def,one_byte_list_def,SEP_CLAUSES,
       word_arith_lemma1,AC ADD_ASSOC ADD_COMM,LENGTH,WORD_ADD_0,APPEND,string_data_def,
       one_byte_list_APPEND,LENGTH_MAP]
  \\ FULL_SIMP_TAC std_ss [GSYM one_string_def]
  \\ ONCE_REWRITE_TAC [mc_insert_sym_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ SEP_R_TAC
  \\ `(STRLEN s + 1) < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,word_lo_n2w]
  \\ Cases_on `254 < STRLEN s + 1` \\ ASM_SIMP_TAC std_ss []
  THEN1 (Q.EXISTS_TAC `T` \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [GSYM w2w_def]
  \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,word64_3232_def,word_arith_lemma1,
       word_arith_lemma2,word_arith_lemma3,word_arith_lemma4,SEP_CLAUSES,STAR_ASSOC,
       INSERT_SUBSET,EMPTY_SUBSET]
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [mc_insert_sym_lemma2_blast]
  \\ FULL_SIMP_TAC std_ss [align_add_blast,align_blast,n2w_and_3]
  \\ REVERSE (Cases_on `0x208w <+ sa3 - sa2 - n2w (STRLEN s + 1)`)
  THEN1 (ASM_SIMP_TAC std_ss [] \\ METIS_TAC []) \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `536870910 < n MOD 18446744073709551616`
  THEN1 (ASM_SIMP_TAC std_ss [] \\ METIS_TAC []) \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `F` \\ FULL_SIMP_TAC std_ss [word_add_n2w]
  \\ Q.UNABBREV_TAC `r9`
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [mc_insert_sym_lemma2_blast]
  \\ REPEAT STRIP_TAC \\ SEP_R_TAC \\ SEP_WRITE_TAC);

val mc_insert_sym_lemma3 = prove(
  ``!xs n p a r9.
      (r7 && 3w = 0w) /\ EVERY (\x. STRLEN x < 255) xs /\
      (one_byte_list a (symbol_list xs) * p) (fun2set (g,dg)) ==>
      ?toosmall.
          mc_insert_sym_pre (r7,a,r9,n2w n,256w,dg,g,df,f) /\
          (mc_insert_sym (r7,a,r9,n2w n,256w,dg,g,df,f) =
             (r7,if toosmall then 25w else 29w,3w,dg,g,df,f))``,
  REVERSE Induct \\ SIMP_TAC std_ss [LIST_FIND_def] THEN1
   (STRIP_TAC \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
    \\ SIMP_TAC std_ss [symbol_list_def,string_data_def,one_byte_list_def,
         one_byte_list_APPEND,LENGTH,LENGTH_MAP,ADD1]
    \\ FULL_SIMP_TAC std_ss [GSYM one_string_def,EVERY_DEF]
    \\ ONCE_REWRITE_TAC [mc_insert_sym_def]
    \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ SEP_R_TAC
    \\ `LENGTH h + 1 < 256` by DECIDE_TAC
    \\ `~(256 = STRLEN h + 1)` by DECIDE_TAC
    \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [ADD1,word_add_n2w]
    \\ SEP_I_TAC "mc_insert_sym"
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`p * (one (a,n2w (STRLEN h + 1)) * one_string (a + 0x1w) h)`])
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [string_data_def,one_byte_list_def,
            one_byte_list_APPEND,LENGTH,LENGTH_APPEND,LENGTH_MAP]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,ADD1,WORD_ADD_ASSOC]
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,symbol_list_def,one_byte_list_def,SEP_CLAUSES,
       word_arith_lemma1,AC ADD_ASSOC ADD_COMM,LENGTH,WORD_ADD_0,APPEND,string_data_def,
       one_byte_list_APPEND,LENGTH_MAP]
  \\ FULL_SIMP_TAC std_ss [GSYM one_string_def]
  \\ ONCE_REWRITE_TAC [mc_insert_sym_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ SEP_R_TAC
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,word_lo_n2w]
  \\ METIS_TAC []);


(* read next token *)

val (mc_next_token_spec,mc_next_token_def) = basic_decompile_strings x64_tools "mc_next_token"
  (SOME (``(r7:word64,r15:word64,io:io_streams,dg:word64 set,g:word64->word8,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r7:word64,r8:word64,r9:word64,r10:word64,r11:word64,r15:word64,io:io_streams,dg:word64 set,g:word64->word8,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
START:
       insert io_read
       cmp r0,32
       ja NOT_SPACE
       insert io_next
       jmp START
NOT_SPACE:
       cmp r0,40
       je OPEN
       cmp r0,41
       je CLOSE
       cmp r0,39
       je QUOTE
       cmp r0,46
       je DOT
       cmp r0,35
       je HASH
       cmp r0,59
       je COMMENT
       cmp r0,57
       ja SYMBOL
       cmp r0,48
       jb SYMBOL
NUMBER:
       sub r0,48
       mov r8,r0
       insert io_next
       insert mc_read_num
       mov r9d,1
       cmp r8,1073741823
       ja TOOLARGENUM
       shl r8,2
       inc r8
       jmp EXIT
COMMENT:
       mov r0d,0
       insert io_next
       insert mc_read_until_newline
       mov r0d,0
       jmp START
TOOLARGENUM:
       mov r8d,37
       mov r9d,3
       jmp EXIT
SYMBOL:
       cmp r0,255
       ja END
       mov r9,[r7-216]
       insert mc_read_sym
       mov r8,[r7-224]
       dec r9
       inc r15
       xor r10,r10
       insert mc_insert_sym
       mov r15,[r7-240]
       add r15,r15
       jmp EXIT
END:
       mov r8d,41
       mov r9d,3
       jmp EXIT
HASH:
       insert io_next
       xor r8,r8
       insert mc_read_num
       insert io_read
       cmp r0,255
       ja HASH_ERR
       insert io_next
       cmp r0,35
       jne HASH1
       cmp r8,1073741823
       ja TOOLARGENUM
       shl r8,2
       inc r8
       mov r9d,13
       jmp EXIT
HASH1:
       cmp r0,61
       jne HASH_ERR
       cmp r8,1073741823
       ja TOOLARGENUM
       shl r8,2
       inc r8
       mov r9d,9
       jmp EXIT
HASH_ERR:
       mov r8d,33
       mov r9d,3
       jmp EXIT
OPEN:
       mov r0d,1
       jmp BASIC
CLOSE:
       mov r0d,9
       jmp BASIC
DOT:
       mov r0d,5
       jmp BASIC
QUOTE:
       mov r0d,13
BASIC:
       mov r8,r0
       mov r0d,5
       mov r9,r0
       insert io_next
EXIT:
       mov r0d,3
       mov r10,r0
       mov r11,r0
     `);

val _ = save_thm("mc_next_token_spec",mc_next_token_spec);

val lisp_inv_Val0  = Q.SPEC `0`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val1  = Q.SPEC `1`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val2  = Q.SPEC `2`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val3  = Q.SPEC `3`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val4  = Q.SPEC `4`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val5  = Q.SPEC `5`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val6  = Q.SPEC `6`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val7  = Q.SPEC `7`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val8  = Q.SPEC `8`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val9  = Q.SPEC `9`  lisp_inv_Val_n2w |> SIMP_RULE std_ss [];
val lisp_inv_Val10 = Q.SPEC `10` lisp_inv_Val_n2w |> SIMP_RULE std_ss [];

val lisp_inv_Val_lemma = LIST_CONJ [lisp_inv_Val0,lisp_inv_Val1,lisp_inv_Val2,lisp_inv_Val3,lisp_inv_Val4,lisp_inv_Val5,lisp_inv_Val10];

val IF_OR = METIS_PROVE [] ``(if b then x else if c then x else y) =
                             (if b \/ c then x else y)``

val next_token_blast = blastLib.BBLAST_PROVE
  ``(w << 3 !! 3w = (w << 3) + 3w:word64) /\
    (v << 3 !! 3w = (v << 3) + 3w:word32)``

val LIST_FIND_NONE_SOME = prove(
  ``!xs n s x.
      (LIST_FIND n s xs = NONE) ==> (LIST_FIND n s (xs ++ [s]) = SOME (n + LENGTH xs))``,
  Induct \\ ASM_SIMP_TAC std_ss [LIST_FIND_def,APPEND,LENGTH]
  \\ REPEAT STRIP_TAC \\ Cases_on `s = h` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ADD1] \\ DECIDE_TAC);

val LIST_FIND_NONE_IMP = prove(
  ``!xs n s x. (LIST_FIND n s xs = NONE) ==> ~MEM s xs``,
  Induct \\ ASM_SIMP_TAC std_ss [LIST_FIND_def,APPEND,LENGTH,MEM]
  \\ REPEAT STRIP_TAC \\ Cases_on `s = h` \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []);

val LIST_FIND_SOME_LESS_LENGTH = prove(
  ``!xs n s k. (LIST_FIND n s xs = SOME k) ==> k < n + LENGTH xs``,
  Induct \\ SIMP_TAC std_ss [LIST_FIND_def,LENGTH] \\ SRW_TAC [] []
  \\ RES_TAC \\ DECIDE_TAC);

val LENGTH_symbol_list_SNOC = prove(
  ``!xs x. LENGTH (symbol_list (xs ++ [x])) = LENGTH (symbol_list xs) + LENGTH x + 1``,
  Induct \\ ASM_SIMP_TAC std_ss [symbol_list_def,APPEND,LENGTH,
      string_data_def,ADD1,LENGTH_APPEND,LENGTH_MAP,AC ADD_ASSOC ADD_COMM]);

val one_byte_list_IMP = prove(
  ``!f df p a xs.
      (one_byte_list a xs * p) (fun2set (f,df)) ==>
       LENGTH xs <= 18446744073709551616``,
  REPEAT STRIP_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ IMP_RES_TAC SPLIT_LIST
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND]
  \\ Cases_on `xs1` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_def]
  \\ `~(a = a + 0x10000000000000000w)` by SEP_NEQ_TAC
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [] \\ Cases_on `a`
  \\ FULL_SIMP_TAC wstd_ss [word_add_n2w,n2w_11,ADD_MODULUS_LEFT]);

val tw0_lemma = prove(
  ``^LISP ==> (tw0 = 3w)``,
  SIMP_TAC std_ss [lisp_inv_def] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []);

val gc_w2w_lemma = prove(
  ``!w. ((w2w:word64->word32) ((w2w:word32->word64) w) = w) /\
        ((31 -- 0) ((w2w:word32->word64) w) = w2w w) /\
        ((31 >< 0) bp = (w2w bp):word32) /\
        ((63 >< 32) bp = (w2w (bp >>> 32)):word32) /\
        (w2w ((w2w (bp >>> 32)):word32) << 32 !! w2w ((w2w bp):word32) = bp:word64)``,
  blastLib.BBLAST_TAC);

val lisp_inv_3NIL = prove(
  ``^LISP ==> let (x1,x2,x3,w1,w2,w3) = (Sym "NIL",Sym "NIL",Sym "NIL",3w,3w,3w) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC lisp_inv_swap1
  \\ MATCH_MP_TAC lisp_inv_NIL
  \\ Q.LIST_EXISTS_TAC [`x1`,`w1`]
  \\ MATCH_MP_TAC lisp_inv_swap1
  \\ MATCH_MP_TAC lisp_inv_swap2
  \\ MATCH_MP_TAC lisp_inv_NIL
  \\ Q.LIST_EXISTS_TAC [`x2`,`w2`]
  \\ MATCH_MP_TAC lisp_inv_swap2
  \\ MATCH_MP_TAC lisp_inv_swap3
  \\ MATCH_MP_TAC lisp_inv_NIL
  \\ Q.LIST_EXISTS_TAC [`x3`,`w3`]
  \\ MATCH_MP_TAC lisp_inv_swap3
  \\ ASM_SIMP_TAC std_ss []) |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_2NIL = prove(
  ``^LISP ==> let (x2,x3,w2,w3) = (Sym "NIL",Sym "NIL",3w,3w) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC lisp_inv_swap2
  \\ MATCH_MP_TAC lisp_inv_NIL
  \\ Q.LIST_EXISTS_TAC [`x2`,`w2`]
  \\ MATCH_MP_TAC lisp_inv_swap2
  \\ MATCH_MP_TAC lisp_inv_swap3
  \\ MATCH_MP_TAC lisp_inv_NIL
  \\ Q.LIST_EXISTS_TAC [`x3`,`w3`]
  \\ MATCH_MP_TAC lisp_inv_swap3
  \\ ASM_SIMP_TAC std_ss []) |> SIMP_RULE std_ss [LET_DEF];

val my_next_token_ind = prove(
  ``!P. P "" /\
        (!h zs.
          ((h = #";") ==> P (SND (read_while (\x. x <> #"\n") zs ""))) /\
           (space_char h ==> P zs) ==>
           P (STRING h zs)) ==>
        !zs. P zs``,
  NTAC 2 STRIP_TAC \\ HO_MATCH_MP_TAC (SIMP_RULE std_ss [] next_token_ind)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `!h zs. bbb` (MP_TAC o Q.SPECL [`c`,`cs`])
  \\ Cases_on `c = #";"` \\ FULL_SIMP_TAC wstd_ss [CHR_11]
  \\ FULL_SIMP_TAC std_ss [EVAL ``~space_char #";" /\ ~number_char #";"``]);

(* allow for failure, e.g. too large number, too long symbol, not enough symtable space *)
val mc_next_token_lemma = prove(
  ``!zs z zs2.
      (next_token zs = (z,zs2)) ==>
      (lisp_inv ^STAT (x0,x1,x2,x3,x4,x5,^VAR_REST)
         (w0,w1,w2,w3,w4,w5,df,f,^REST)) ==>
      ?ok1 zX z0 z1 w0i w1i w2i w3i io2 gi fi sa2.
        mc_next_token_pre (sp,we,REPLACE_INPUT_IO zs io,dg,g,df,f) /\
        (mc_next_token (sp,we,REPLACE_INPUT_IO zs io,dg,g,df,f) =
          (tw0,sp,w2w w0i,w2w w1i,w2w w2i,w2w w3i,we,io2,dg,gi,df,fi)) /\
        (lisp_inv ^STAT
          (if ok1 then z0 else zX,if ok1 then z1 else Sym "NIL",Sym "NIL",Sym "NIL",x4,x5,^VAR_REST)
          (w0i,w1i,w2i,w3i,w4,w5,df,fi,let g = gi in ^REST)) /\
        (ok1 ==> (REPLACE_INPUT_IO zs2 io = io2)) /\
        (if ok1 then (z = (z0,z1)) else isVal zX)``,

  SIMP_TAC std_ss [LET_DEF]
  \\ HO_MATCH_MP_TAC my_next_token_ind \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `next_token xxx = yyy` (MP_TAC o GSYM)
  \\ SIMP_TAC std_ss [next_token_def] \\ STRIP_TAC
  \\ SIMP_TAC std_ss [MAP] \\ ONCE_REWRITE_TAC [mc_next_token_def]
  \\ `ORD h < 256` by METIS_TAC [ORD_BOUND]
  \\ `ORD h < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,IO_INPUT_LEMMA,w2w_def,w2n_n2w,
       n2w_11,word_lo_n2w,space_char_def,DECIDE ``n < 33 = n <= 32:num``]
  \\ ONCE_REWRITE_TAC [GSYM (EVAL ``ORD #"("``)]
  \\ ONCE_REWRITE_TAC [GSYM (EVAL ``ORD #")"``)]
  \\ ONCE_REWRITE_TAC [GSYM (EVAL ``ORD #"."``)]
  \\ ONCE_REWRITE_TAC [GSYM (EVAL ``ORD #"'"``)]
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [ORD_11,CHR_ORD] THEN1
   (SIMP_TAC (std_ss++SIZES_ss) ([word_1comp_n2w,word_lo_n2w,n2w_11,w2n_n2w]
       @ map EVAL [``ORD #"("``,``ORD #")"``,``ORD #"."``,``ORD #"'"``])
    \\ `tw0 = 3w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `F`
    \\ Q.EXISTS_TAC `Val 10` \\ ASM_SIMP_TAC std_ss [isVal_def]
    \\ Q.LIST_EXISTS_TAC [`41w`,`3w`,`3w`,`3w`]
    \\ SIMP_TAC wstd_ss [w2n_n2w]
    \\ Q.EXISTS_TAC `sa2`
    \\ MATCH_MP_TAC lisp_inv_3NIL
    \\ IMP_RES_TAC lisp_inv_Val_lemma)
  \\ Q.PAT_ASSUM `(z,zs2) = xxx` MP_TAC
  \\ Cases_on `ORD h <= 32` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ASM_SIMP_TAC std_ss [DECIDE ``32 < ORD h = ~(ORD h <= 32)``,GSYM w2w_def,space_char_def]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,space_char_def] \\ METIS_TAC [tw0_lemma])
  \\ Q.PAT_ASSUM `space_char h ==> bbb` (K ALL_TAC)
  \\ `32 < ORD h` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `h = #";"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ASM_SIMP_TAC (srw_ss()) [EVAL ``ORD #";"``,EVAL ``number_char #";"``]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,EVAL ``space_char #";"``,
         mc_read_until_newline_thm] \\ METIS_TAC [w2w_def])
  \\ Q.PAT_ASSUM `(h = #";") ==> bbb` (K ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [space_char_def]
  \\ Cases_on `h = #"("` \\ ASM_SIMP_TAC std_ss [] THEN1
   (REPEAT STRIP_TAC \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `T` \\ FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`1w`,`5w`,`3w`,`3w`]
    \\ SIMP_TAC wstd_ss [w2n_n2w] \\ Q.EXISTS_TAC `sa2`
    \\ MATCH_MP_TAC lisp_inv_2NIL
    \\ METIS_TAC [lisp_inv_Val_lemma,lisp_inv_swap1,tw0_lemma])
  \\ Cases_on `h = #")"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,CHR_11]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `T` \\ FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`9w`,`5w`,`3w`,`3w`]
    \\ SIMP_TAC wstd_ss [w2n_n2w] \\ Q.EXISTS_TAC `sa2`
    \\ MATCH_MP_TAC lisp_inv_2NIL
    \\ METIS_TAC [lisp_inv_Val_lemma,lisp_inv_swap1,tw0_lemma])
  \\ Cases_on `h = #"'"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,CHR_11]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `T` \\ FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`0xDw`,`5w`,`3w`,`3w`]
    \\ SIMP_TAC wstd_ss [w2n_n2w] \\ Q.EXISTS_TAC `sa2`
    \\ MATCH_MP_TAC lisp_inv_2NIL
    \\ METIS_TAC [lisp_inv_Val_lemma,lisp_inv_swap1,tw0_lemma])
  \\ Cases_on `h = #"."` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,CHR_11]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `T` \\ FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`0x5w`,`5w`,`3w`,`3w`]
    \\ SIMP_TAC wstd_ss [w2n_n2w] \\ Q.EXISTS_TAC `sa2`
    \\ MATCH_MP_TAC lisp_inv_2NIL
    \\ METIS_TAC [lisp_inv_Val_lemma,lisp_inv_swap1,tw0_lemma])
  \\ `~(255 < ORD h)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `number_char h` THEN1
   (`~(h = #"#") /\ ~(ORD h = 35) /\ ~(ORD h = 59) /\ ~(57 < ORD h) /\ ~(ORD h < 48)`by
     (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [EVAL ``number_char #"#"``]
      \\ FULL_SIMP_TAC std_ss [number_char_def] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ STRIP_ASSUME_TAC (Q.SPECL [`zs`,`number_char`] read_while_SPLIT)
    \\ FULL_SIMP_TAC std_ss [APPEND,word_arith_lemma2,mc_read_num_thm]
    \\ Cases_on `str2num (STRING h xs1') < 1073741824` \\ ASM_SIMP_TAC std_ss [] THEN1
     (SIMP_TAC (std_ss++SIZES_ss) [WORD_MUL_LSL,word_mul_n2w,word_add_n2w,word_lo_n2w,w2n_n2w]
      \\ `~(1073741823 < str2num (STRING h xs1'))` by DECIDE_TAC
      \\ `(str2num (STRING h xs1')) < 18446744073709551616` by DECIDE_TAC
      \\ `(4 * str2num (STRING h xs1') + 1) < 18446744073709551616` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `T`
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_add_n2w,word_lo_n2w,w2n_n2w]
      \\ Q.LIST_EXISTS_TAC [`n2w (4 * str2num (STRING h xs1') + 1)`,`1w`,`3w`,`3w`]
      \\ Q.EXISTS_TAC `sa2` \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC wstd_ss [w2n_n2w]
      \\ `(4 * str2num (STRING h xs1') + 1) < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC lisp_inv_2NIL
      \\ MATCH_MP_TAC lisp_inv_Val_n2w \\ ASM_SIMP_TAC std_ss []
      \\ METIS_TAC [lisp_inv_Val_lemma,lisp_inv_swap1])
    \\ ASM_SIMP_TAC std_ss [EVAL ``0x3FFFFFFFw <+ ~n2w (str2num ""):word64``]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `F` \\ ASM_SIMP_TAC std_ss []
    \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_add_n2w,word_lo_n2w,w2n_n2w]
    \\ Q.EXISTS_TAC `Val 9` \\ ASM_SIMP_TAC std_ss [isVal_def]
    \\ Q.LIST_EXISTS_TAC [`0x25w`,`3w`,`3w`,`3w`,`sa2`]
    \\ SIMP_TAC wstd_ss [w2n_n2w]
    \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC lisp_inv_3NIL
    \\ IMP_RES_TAC lisp_inv_Val9)
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `h = #"#"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,EVAL ``ORD #"#"``]
    \\ STRIP_ASSUME_TAC (Q.SPECL [`zs`,`number_char`] read_while_SPLIT)
    \\ FULL_SIMP_TAC std_ss [APPEND,word_arith_lemma2,mc_read_num_thm0]
    \\ Cases_on `xs2` \\ ASM_SIMP_TAC std_ss [IO_INPUT_LEMMA,MAP] THEN1
     (ASM_SIMP_TAC (std_ss++SIZES_ss) [EVAL ``0xFFw <+ ~0x0w:word64``]
      \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`F`,`Val 8`]
      \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`0x21w`,`3w`,`3w`,`3w`,`sa2`]
      \\ SIMP_TAC wstd_ss [w2n_n2w,isVal_def]
      \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC lisp_inv_3NIL
      \\ IMP_RES_TAC lisp_inv_Val8)
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,ORD_BOUND]
    \\ `~(0xFFw <+ n2w (ORD h'):word64)` by ALL_TAC THEN1
      (`ORD h' < 256` by ASM_SIMP_TAC std_ss [ORD_BOUND]
       \\ `ORD h' < 18446744073709551616` by DECIDE_TAC
       \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,ORD_BOUND,word_lo_n2w]
       \\ DECIDE_TAC) \\ ASM_SIMP_TAC std_ss []
    \\ `ORD h' < 256` by ASM_SIMP_TAC std_ss [ORD_BOUND]
    \\ `ORD h' < 18446744073709551616` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [NOT_CONS_NIL,n2w_11,HD]
    \\ Cases_on `h' = #"#"` \\ ASM_SIMP_TAC std_ss [EVAL ``ORD #"#"``] THEN1
     (REVERSE (Cases_on `str2num xs1' < 1073741824`) \\ ASM_SIMP_TAC std_ss []
      \\ ASM_SIMP_TAC std_ss [EVAL ``0x3FFFFFFFw <+ ~0x0w:word64``,NOT_CONS_NIL,TL]
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [HD,w2w_def,w2n_n2w,ORD_BOUND]
      \\ REPEAT STRIP_TAC THEN1
       (IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
        \\ Q.EXISTS_TAC `F` \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `Val 9`
        \\ Q.LIST_EXISTS_TAC [`0x25w`,`3w`,`3w`,`3w`,`sa2`]
        \\ SIMP_TAC wstd_ss [w2n_n2w,isVal_def]
        \\ ASM_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC lisp_inv_3NIL
        \\ IMP_RES_TAC lisp_inv_Val9)
      \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
      \\ `str2num xs1' < 18446744073709551616` by DECIDE_TAC
      \\ `~(1073741823 < str2num xs1')` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,TL,w2n_n2w]
      \\ Q.EXISTS_TAC `T`
      \\ ASM_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
      \\ Q.LIST_EXISTS_TAC [`n2w (4 * str2num xs1' + 1)`,`0xDw`,`3w`,`3w`,`sa2`]
      \\ SIMP_TAC wstd_ss [w2n_n2w,isVal_def]
      \\ ASM_SIMP_TAC std_ss []
      \\ `(4 * str2num xs1' + 1) < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC lisp_inv_2NIL
      \\ MATCH_MP_TAC lisp_inv_Val_n2w \\ ASM_SIMP_TAC std_ss []
      \\ METIS_TAC [lisp_inv_Val_lemma,lisp_inv_swap1])
    \\ ASM_SIMP_TAC std_ss []
    \\ `~(ORD h' = 35)` by FULL_SIMP_TAC std_ss [GSYM ORD_11,EVAL ``ORD #"#"``]
    \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `h' = #"="` \\ ASM_SIMP_TAC std_ss [EVAL ``ORD #"="``] THEN1
     (REVERSE (Cases_on `str2num xs1' < 1073741824`) \\ ASM_SIMP_TAC std_ss []
      \\ ASM_SIMP_TAC std_ss [EVAL ``0x3FFFFFFFw <+ ~0x0w:word64``,NOT_CONS_NIL,TL]
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [HD,w2w_def,w2n_n2w,ORD_BOUND]
      \\ REPEAT STRIP_TAC THEN1
       (IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
        \\ Q.EXISTS_TAC `F` \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `Val 9`
        \\ Q.LIST_EXISTS_TAC [`0x25w`,`3w`,`3w`,`3w`,`sa2`]
        \\ SIMP_TAC wstd_ss [w2n_n2w,isVal_def]
        \\ ASM_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC lisp_inv_3NIL
        \\ IMP_RES_TAC lisp_inv_Val9)
      \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
      \\ `str2num xs1' < 18446744073709551616` by DECIDE_TAC
      \\ `~(1073741823 < str2num xs1')` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,TL,w2n_n2w]
      \\ Q.EXISTS_TAC `T`
      \\ ASM_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
      \\ Q.LIST_EXISTS_TAC [`n2w (4 * str2num xs1' + 1)`,`0x9w`,`3w`,`3w`,`sa2`]
      \\ SIMP_TAC wstd_ss [w2n_n2w,isVal_def]
      \\ ASM_SIMP_TAC std_ss []
      \\ `(4 * str2num xs1' + 1) < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC lisp_inv_2NIL
      \\ MATCH_MP_TAC lisp_inv_Val_n2w \\ ASM_SIMP_TAC std_ss []
      \\ METIS_TAC [lisp_inv_Val_lemma,lisp_inv_swap1])
    \\ `~(ORD h' = 61)` by FULL_SIMP_TAC std_ss [GSYM ORD_11,EVAL ``ORD #"="``]
    \\ ASM_SIMP_TAC std_ss [TL]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,TL,w2n_n2w]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`F`,`Val 8`]
    \\ IMP_RES_TAC tw0_lemma \\ FULL_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [isVal_def]
    \\ Q.LIST_EXISTS_TAC [`0x21w`,`3w`,`3w`,`3w`,`sa2`]
    \\ SIMP_TAC wstd_ss [w2n_n2w,isVal_def]
    \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC lisp_inv_3NIL
    \\ IMP_RES_TAC lisp_inv_Val8)
  \\ `~(ORD h = 35)` by FULL_SIMP_TAC std_ss [GSYM ORD_11,EVAL ``ORD #"#"``]
  \\ `~(ORD h = 59)` by FULL_SIMP_TAC std_ss [GSYM ORD_11,EVAL ``ORD #";"``]
  \\ ASM_SIMP_TAC std_ss [IF_OR]
  \\ `57 < ORD h \/ ORD h < 48 = ~number_char h` by ALL_TAC THEN1
       (FULL_SIMP_TAC std_ss [number_char_def] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [GSYM w2w_def]
  \\ `?cs1 cs2. str2sym (STRING h zs) = (cs1,cs2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ `w2w (f (sp - 0xDCw)) << 32 !! w2w (f (sp - 0xE0w)) = sa1` by ALL_TAC THEN1
        (IMP_RES_TAC lisp_inv_cs_read \\ ASM_SIMP_TAC std_ss [])
  \\ `w2w (f (sp - 0xD4w)) << 32 !! w2w (f (sp - 0xD8w)) = sa2` by ALL_TAC THEN1
        (IMP_RES_TAC lisp_inv_cs_read \\ ASM_SIMP_TAC std_ss [])
  \\ `w2w (f (sp - 236w)) << 32 !! w2w (f (sp - 240w)) = (n2w e):word64` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [lisp_inv_def]
    \\ Q.PAT_ASSUM `xxx (fun2set (f,df))` MP_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,ref_full_stack_def]
    \\ NTAC 4 (ONCE_REWRITE_TAC [ref_static_def])
    \\ FULL_SIMP_TAC std_ss [word64_3232_def,LET_DEF,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3] \\ STRIP_TAC \\ SEP_R_TAC
    \\ FULL_SIMP_TAC std_ss [gc_w2w_lemma])
  \\ ASM_SIMP_TAC std_ss [word_add_n2w,DECIDE ``n+n=2*n``]
  \\ REVERSE (Cases_on `LENGTH cs1 < 255`) THEN1
   (Q.PAT_ASSUM `lisp_inv xxx yyy zzz` (STRIP_ASSUME_TAC o RW [lisp_inv_def])
    \\ FULL_SIMP_TAC std_ss [symtable_inv_def,one_symbol_list_def,SEP_EXISTS_THM,cond_STAR]
    \\ Q.ABBREV_TAC `sll = LENGTH (symbol_list (INIT_SYMBOLS ++ sym))`
    \\ `255 < LENGTH ys` by DECIDE_TAC
    \\ IMP_RES_TAC SPLIT_LIST
    \\ MP_TAC (Q.SPECL [`h::zs`,`cs1`,`cs2`,`g`,`one_byte_list sa1 (symbol_list (INIT_SYMBOLS ++ sym)) *
         one (sa1 + n2w (sll + 255),x) *
         one_byte_list (sa1 + n2w (sll + 256)) xs2`,`MAP (CHR o w2n) (xs1':word8 list)`] (Q.INST [`r9`|->`sa1 + n2w sll`] mc_read_sym_overflow_thm))
    \\ ASM_SIMP_TAC std_ss [LENGTH_MAP]
    \\ FULL_SIMP_TAC std_ss [one_byte_list_def,one_byte_list_APPEND,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ ASM_SIMP_TAC std_ss [LENGTH_MAP,one_string_def,MAP_MAP_LEMMA]
    \\ `255 <= STRLEN cs1` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 FULL_SIMP_TAC (std_ss++star_ss) []
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [word_add_n2w]
    \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC (Q.GEN `r7` (Q.GEN `g` (Q.SPEC `INIT_SYMBOLS ++ sym` mc_insert_sym_lemma3)))
    \\ SEP_I_TAC "mc_insert_sym" \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ SEP_F_TAC
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `F` \\ ASM_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`Val (if toosmall then 6 else 7)`,
         `if toosmall then 0x19w else 0x1Dw`,`3w`,`3w`,`3w`,`sa2`]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,isVal_def,word_add_n2w,
         DECIDE ``n+n=2*n:num``]
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (REVERSE STRIP_TAC THEN1 (Cases_on `toosmall` \\ EVAL_TAC)
      \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,ref_full_stack_def,STAR_ASSOC,
        ref_static_def,LET_DEF,APPEND,word64_3232_def,word_arith_lemma3,
        INSERT_SUBSET,EMPTY_SUBSET]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [])
    \\ Cases_on `toosmall` \\ ASM_SIMP_TAC wstd_ss [w2n_n2w] THEN1
     (MATCH_MP_TAC lisp_inv_Val6
      \\ MATCH_MP_TAC lisp_inv_3NIL
      \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
      \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
      \\ FULL_SIMP_TAC std_ss []
      \\ ASM_SIMP_TAC std_ss [symtable_inv_def,SEP_EXISTS_THM,one_symbol_list_def,cond_STAR]
      \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_PLUS]
      \\ Q.EXISTS_TAC `MAP (n2w o ORD) xs2' ++ x::xs2`
      \\ `255 <= LENGTH cs1` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_MAP,LENGTH_APPEND,LENGTH_TAKE]
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,one_byte_list_APPEND,LENGTH_MAP,LENGTH_TAKE]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,word_arith_lemma1])
    THEN1
     (MATCH_MP_TAC lisp_inv_Val7
      \\ MATCH_MP_TAC lisp_inv_3NIL
      \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
      \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
      \\ FULL_SIMP_TAC std_ss []
      \\ ASM_SIMP_TAC std_ss [symtable_inv_def,SEP_EXISTS_THM,one_symbol_list_def,cond_STAR]
      \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_PLUS]
      \\ Q.EXISTS_TAC `MAP (n2w o ORD) xs2' ++ x::xs2`
      \\ `255 <= LENGTH cs1` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_MAP,LENGTH_APPEND,LENGTH_TAKE]
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,one_byte_list_APPEND,LENGTH_MAP,LENGTH_TAKE]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,word_arith_lemma1]))
  \\ Q.PAT_ASSUM `lisp_inv xxx yyy zzz` (STRIP_ASSUME_TAC o RW [lisp_inv_def])
  \\ FULL_SIMP_TAC std_ss [symtable_inv_def,one_symbol_list_def,SEP_EXISTS_THM,cond_STAR]
  \\ `LENGTH cs1 < LENGTH ys` by DECIDE_TAC
  \\ IMP_RES_TAC SPLIT_LIST
  \\ FULL_SIMP_TAC std_ss [one_byte_list_def,one_byte_list_APPEND,STAR_ASSOC]
  \\ Q.ABBREV_TAC `sll = LENGTH (symbol_list (INIT_SYMBOLS ++ sym))`
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
  \\ MP_TAC (Q.SPECL [`h::zs`,`cs1`,`cs2`,`g`,`one_byte_list sa1 (symbol_list (INIT_SYMBOLS ++ sym)) *
        one (sa1 + n2w (sll + STRLEN cs1),x) *
        one_byte_list (sa1 + n2w (sll + (STRLEN cs1 + 1))) xs2`,`MAP (CHR o w2n) (xs1':word8 list)`] (Q.INST [`r9`|->`sa1 + n2w sll`] mc_read_sym_thm))
  \\ `LENGTH cs1 < 256` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LENGTH_MAP,one_string_def,MAP_MAP_LEMMA]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 FULL_SIMP_TAC (std_ss++star_ss) []
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [word_arith_lemma1]
  \\ REVERSE (Cases_on `LIST_FIND 0 cs1 (INIT_SYMBOLS ++ sym)`) THEN1
   (MP_TAC (Q.SPECL [`INIT_SYMBOLS ++ sym`,`0`,`x'`,`
         one (sa1 + n2w (sll + STRLEN cs1),x) *
         one_byte_list (sa1 + n2w (sll + (STRLEN cs1 + 1))) xs2`,`sa1`] (Q.INST [`s`|->`cs1`,`g`|->`g2`,`r9`|->`sa1 + n2w sll - 1w`,`r7`|->`sp`] mc_insert_sym_lemma1))
    \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [WORD_SUB_ADD]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,word_arith_lemma1])
    \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `T`
    \\ SIMP_TAC std_ss [next_token_blast,WORD_MUL_LSL,word_add_n2w,word_mul_n2w]
    \\ Q.LIST_EXISTS_TAC [`n2w (8 * x' + 3)`,`1w`,`3w`,`3w`,`sa2`]
    \\ SIMP_TAC wstd_ss [w2w_def,w2n_n2w] \\ SIMP_TAC std_ss [GSYM w2w_def]
    \\ IMP_RES_TAC LIST_FIND_SOME_LESS_LENGTH
    \\ `x' < 536870912` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
    \\ `(8 * x' + 3) < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [word_add_n2w,DECIDE ``n+n=2*n``]
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,ref_full_stack_def,STAR_ASSOC,
        ref_static_def,LET_DEF,APPEND,word64_3232_def,word_arith_lemma3]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [])
    \\ MATCH_MP_TAC lisp_inv_2NIL
    \\ MATCH_MP_TAC lisp_inv_swap1
    \\ MATCH_MP_TAC (GEN_ALL lisp_inv_Val0)
    \\ Q.LIST_EXISTS_TAC [`x1`,`w1`]
    \\ MATCH_MP_TAC lisp_inv_swap1
    \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
    \\ Q.LIST_EXISTS_TAC [`H_DATA (INR (n2w x'))`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF,lisp_x_def,MAP,CONS_11,ref_heap_addr_def]
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [APPEND,ok_split_heap_def,ADDR_SET_THM,UNION_SUBSET]
      \\ MATCH_MP_TAC SUBSET_TRANS
      \\ Q.EXISTS_TAC `ADDR_SET (s0::s1::s2::s3::s4::s5::(ss++ss1))`
      \\ ASM_SIMP_TAC std_ss []
      \\ Cases_on `s0`
      \\ FULL_SIMP_TAC std_ss [ADDR_SET_THM,SUBSET_DEF,IN_INSERT])
    THEN1
     (`(8 * x' + 3) < 18446744073709551616` by DECIDE_TAC
      \\ ASM_SIMP_TAC wstd_ss [next_token_blast,WORD_MUL_LSL,word_add_n2w,w2w_def,
            w2n_n2w,word_mul_n2w])
    THEN1 (FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_PLUS])
    \\ FULL_SIMP_TAC std_ss [symtable_inv_def,one_symbol_list_def,SEP_EXISTS_THM,cond_STAR]
    \\ Q.EXISTS_TAC `MAP (n2w o ORD) cs1 ++ x::xs2`
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,LENGTH_MAP]
    \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,LENGTH_MAP,one_byte_list_def]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [word_arith_lemma1])
  \\ MP_TAC (Q.SPECL [`INIT_SYMBOLS ++ sym`,`0`,`x'`,`
         one_byte_list (sa1 + n2w (sll + (STRLEN cs1 + 1))) xs2`,`sa1`,`x`,`sa1 + n2w sll - 1w`]
            (Q.INST [`s`|->`cs1`,`g`|->`g2`,`r7`|->`sp`,`q`|->`
         ref_mem bp m 0 e * ref_mem bp2 (\x. H_EMP) 0 e *
         ref_stack (sp + 0x4w * wsp) (ss ++ ss1) *
         ref_stack_space (sp + 0x4w * wsp) (w2n wsp + 6) *
         ref_static (sp - 256w) ([a1; a2; n2w e; bp2; sa1]) *
         ref_stack_space_above
           (sp + 0x4w * wsp + n2w (4 * (LENGTH ss + LENGTH ss1)))
           (sl1 - LENGTH ss1) *
         ref_static (sp - 0xC8w) ([ex] ++ cs ++ ds)`] mc_insert_sym_lemma2))
  \\ ASM_SIMP_TAC std_ss [markerTheory.Abbrev_def]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [WORD_SUB_ADD,STAR_ASSOC]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,word_arith_lemma1]
    \\ `[a1; a2; n2w e; bp2; sa1; sa1 + n2w sll; sa3; ex] ++ cs ++ ds =
        [a1; a2; n2w e; bp2; sa1] ++ [sa1 + n2w sll; sa3] ++ ([ex] ++ cs ++ ds)`
            by ALL_TAC THEN1 SIMP_TAC std_ss [APPEND]
    \\ Q.PAT_ASSUM `xxx (fun2set (f,df))` MP_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.SPEC_TAC (`[ex]++cs++ds`,`xxs`) \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,ref_static_APPEND]
    \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND,word_arith_lemma3]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,word_arith_lemma1])
  \\ STRIP_TAC \\ Cases_on `fail` THEN1
   (FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `F` \\ ASM_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`Val (if toosmall then 6 else 7)`,`(if toosmall then 0x19w else 0x1Dw)`,`3w`,`3w`,`3w`,`sa2`]
    \\ ASM_SIMP_TAC wstd_ss [isVal_def,w2w_def,w2n_n2w,word_add_n2w,DECIDE ``n+n=2*n``]
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (REVERSE STRIP_TAC THEN1 (Cases_on `toosmall` \\ EVAL_TAC)
      \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,ref_full_stack_def,STAR_ASSOC,
        ref_static_def,LET_DEF,APPEND,word64_3232_def,word_arith_lemma3,
        INSERT_SUBSET,EMPTY_SUBSET]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [])
    \\ MATCH_MP_TAC lisp_inv_3NIL
    \\ Cases_on `toosmall` \\ ASM_SIMP_TAC wstd_ss [w2n_n2w] THEN1
     (MATCH_MP_TAC lisp_inv_Val6
      \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
      \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
      \\ ASM_SIMP_TAC std_ss [symtable_inv_def,SEP_EXISTS_THM,one_symbol_list_def,cond_STAR]
      \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_PLUS]
      \\ Q.EXISTS_TAC `MAP (n2w o ORD) cs1 ++ x::xs2`
      \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_MAP,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,one_byte_list_APPEND,LENGTH_MAP]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,word_arith_lemma1])
    THEN1
     (MATCH_MP_TAC lisp_inv_Val7
      \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
      \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
      \\ ASM_SIMP_TAC std_ss [symtable_inv_def,SEP_EXISTS_THM,one_symbol_list_def,cond_STAR]
      \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_PLUS]
      \\ Q.EXISTS_TAC `MAP (n2w o ORD) cs1 ++ x::xs2`
      \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_MAP,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,one_byte_list_APPEND,LENGTH_MAP]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def,word_arith_lemma1]))
  \\ FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `T` \\ ASM_SIMP_TAC std_ss []
  \\ `w2w (f2 (sp - 236w)) << 32 !! w2w (f2 (sp - 240w)) = (n2w e):word64` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [lisp_inv_def]
    \\ Q.PAT_ASSUM `xxx (fun2set (f2,df))` MP_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,ref_full_stack_def]
    \\ NTAC 4 (ONCE_REWRITE_TAC [ref_static_def])
    \\ FULL_SIMP_TAC std_ss [word64_3232_def,LET_DEF,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3] \\ STRIP_TAC \\ SEP_R_TAC
    \\ FULL_SIMP_TAC std_ss [gc_w2w_lemma])
  \\ ASM_SIMP_TAC std_ss [GSYM w2w_def,word_add_n2w,DECIDE ``n+n=2*n``]
  \\ ASM_SIMP_TAC std_ss [next_token_blast,WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ Q.LIST_EXISTS_TAC [`n2w (8 * LENGTH (INIT_SYMBOLS ++ sym) + 3)`,`1w`,`3w`,`3w`]
  \\ Q.EXISTS_TAC `sa1 + n2w (sll + (STRLEN cs1 + 1))`
  \\ `(8 * LENGTH (INIT_SYMBOLS ++ sym) + 3) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,ref_full_stack_def,STAR_ASSOC,
      ref_static_def,LET_DEF,APPEND,word64_3232_def,word_arith_lemma3,
      INSERT_SUBSET,EMPTY_SUBSET] \\ SEP_R_TAC \\ SIMP_TAC std_ss [])
  \\ MATCH_MP_TAC lisp_inv_2NIL
  \\ MATCH_MP_TAC lisp_inv_swap1
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_Val0) \\ Q.LIST_EXISTS_TAC [`x1`,`w1`]
  \\ MATCH_MP_TAC lisp_inv_swap1
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ Q.LIST_EXISTS_TAC [`H_DATA (INR (n2w (LENGTH (INIT_SYMBOLS ++ sym))))`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym ++ [cs1]`,`b`]
  \\ `code_heap code (INIT_SYMBOLS ++ (sym ++ [cs1]),EL 4 cs,EL 2 ds,EL 3 ds,dd,d)` by
        METIS_TAC [code_heap_add_symbol,APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,ref_heap_addr_def,GSYM w2w_def]
  \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [APPEND,ok_split_heap_def,ADDR_SET_THM,UNION_SUBSET]
      \\ MATCH_MP_TAC SUBSET_TRANS
      \\ Q.EXISTS_TAC `ADDR_SET (s0::s1::s2::s3::s4::s5::(ss++ss1))`
      \\ ASM_SIMP_TAC std_ss []
      \\ Cases_on `s0`
      \\ FULL_SIMP_TAC std_ss [ADDR_SET_THM,SUBSET_DEF,IN_INSERT])
  THEN1
   (ONCE_REWRITE_TAC [EVERY_DEF] \\ REPEAT STRIP_TAC THEN1
     (SIMP_TAC std_ss [lisp_x_def]
      \\ Q.EXISTS_TAC `LENGTH (INIT_SYMBOLS ++ sym)`
      \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
      \\ METIS_TAC [LIST_FIND_NONE_SOME,ADD_CLAUSES])
    \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] MONO_EVERY))
    \\ Q.EXISTS_TAC `lisp_x (m,INIT_SYMBOLS ++ (sym))`
    \\ REVERSE STRIP_TAC THEN1 FULL_SIMP_TAC std_ss [EVERY_DEF]
    \\ Cases \\ Q.SPEC_TAC (`q`,`q`) \\ Induct_on `r`
    \\ FULL_SIMP_TAC std_ss [lisp_x_def] THEN1 (REPEAT STRIP_TAC \\ METIS_TAC [])
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `k`
    \\ ASM_SIMP_TAC std_ss [APPEND_ASSOC]
    \\ Q.PAT_ASSUM `xxx = SOME k` MP_TAC
    \\ Q.SPEC_TAC (`INIT_SYMBOLS ++ sym`,`syms`)
    \\ Q.SPEC_TAC (`0`,`n`)
    \\ Induct_on `syms` \\ ASM_SIMP_TAC std_ss [LIST_FIND_def,APPEND] \\ METIS_TAC [])
  THEN1
   (`((8 * LENGTH (INIT_SYMBOLS ++ sym) + 3) < 18446744073709551616)` by DECIDE_TAC
    \\ ASM_SIMP_TAC wstd_ss [next_token_blast,w2w_def,w2n_n2w,WORD_MUL_LSL,
         word_mul_n2w,word_add_n2w])
  THEN1
   (FULL_SIMP_TAC std_ss [word_arith_lemma1])
  THEN1
   (FULL_SIMP_TAC std_ss [ref_full_stack_def]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ `[a1; a2; n2w e; bp2; sa1; sa1 + n2w (sll + (STRLEN cs1 + 1)); sa3; ex] ++ cs ++ ds =
        [a1; a2; n2w e; bp2; sa1] ++ [sa1 + n2w (sll + (STRLEN cs1 + 1)); sa3] ++ ([ex] ++ cs ++ ds)`
            by ALL_TAC THEN1 SIMP_TAC std_ss [APPEND]
    \\ Q.PAT_ASSUM `xxx (fun2set (f2,df))` MP_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.SPEC_TAC (`[ex]++cs++ds`,`xxs`) \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ref_static_APPEND,LENGTH,LENGTH_APPEND,word_arith_lemma3]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ Q.UNABBREV_TAC `sll`
  \\ SIMP_TAC std_ss [symtable_inv_def,LENGTH_APPEND,APPEND_ASSOC]
  \\ SIMP_TAC std_ss [LENGTH_symbol_list_SNOC,ADD_ASSOC]
  \\ SIMP_TAC std_ss [one_symbol_list_def,SEP_EXISTS_THM,cond_STAR,one_byte_list_APPEND]
  \\ Q.EXISTS_TAC `xs2`
  \\ Q.PAT_ASSUM `xxx = w2n sa3 - w2n sa1` (ASSUME_TAC o GSYM)
  \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_symbol_list_SNOC,LENGTH,ADD1]
  \\ FULL_SIMP_TAC std_ss [EVERY_APPEND,EVERY_DEF,AC ADD_ASSOC ADD_COMM]
  \\ ASM_SIMP_TAC std_ss [RW [SNOC_APPEND] rich_listTheory.ALL_DISTINCT_SNOC]
  \\ IMP_RES_TAC LIST_FIND_NONE_IMP \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1
   (Q.PAT_ASSUM `xx <+ yyy` MP_TAC \\ Q.PAT_ASSUM `w2n sa3 - w2n sa2 = xxx` MP_TAC
    \\ Q.SPEC_TAC (`sa1`,`sa1`) \\ Q.SPEC_TAC (`sa3`,`sa3`) \\ Cases \\ Cases
    \\ FULL_SIMP_TAC std_ss [w2n_n2w,LENGTH_APPEND,LENGTH,ADD1,word_add_n2w]
    \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
    \\ SIMP_TAC std_ss [SUB_RIGHT_EQ]
    \\ SIMP_TAC std_ss [word_arith_lemma2,ADD_ASSOC,DECIDE ``~(m + n < m:num)``]
    \\ SIMP_TAC std_ss [DECIDE ``n + m + 1 - (n + 1):num = m``]
    \\ SIMP_TAC wstd_ss [word_lo_n2w]
    \\ `LENGTH (x::xs2) <= 18446744073709551616` by ALL_TAC THEN1
      (MATCH_MP_TAC one_byte_list_IMP
       \\ Q.LIST_EXISTS_TAC [`g`,`dg`,
          `one_byte_list sa1 (symbol_list (INIT_SYMBOLS ++ sym)) *
           one_byte_list (sa1 + n2w (LENGTH (symbol_list (INIT_SYMBOLS ++ sym)))) xs1'`,
          `sa1 + n2w (STRLEN cs1 + LENGTH (symbol_list (INIT_SYMBOLS ++ sym)))`]
       \\ FULL_SIMP_TAC (std_ss++star_ss) [one_byte_list_def,word_arith_lemma1,
            AC ADD_ASSOC ADD_COMM])
    \\ FULL_SIMP_TAC std_ss [LENGTH,GSYM LESS_EQ] \\ DECIDE_TAC)
  \\ Q.PAT_ASSUM `~(xxx <+ yy)` MP_TAC
  \\ FULL_SIMP_TAC wstd_ss [word_lo_n2w]
  \\ `LENGTH (INIT_SYMBOLS ++ sym) < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [NOT_LESS,LENGTH_APPEND]
  \\ DECIDE_TAC) |> SIMP_RULE std_ss [LET_DEF];

val mc_next_token_thm = mc_next_token_lemma
         |> Q.SPECL [`getINPUT io`,`FST (next_token (getINPUT io))`,`(SND o next_token) (getINPUT io)`]
         |> RW [IO_INPUT_LEMMA,GSYM IO_INPUT_APPLY_def]
         |> SIMP_RULE std_ss []
         |> (fn th => save_thm("mc_next_token_thm",th));


(* num2str *)

val (thm,mc_num2strlen_def) = basic_decompile_strings x64_tools "mc_num2strlen"
  (SOME (``(r0:word64,r8:word64,r9:word64)``,
         ``(r8:word64,r9:word64)``))
  (assemble "x64" `
START:
       inc r9
       cmp r8,r0
       jb EXIT
       lea r0,[4*r0+r0]
       add r0,r0
       jmp START
EXIT: `)

val mc_num2strlen_blast = prove(
  ``!w. 4w * w + w + (4w * w + w) = 10w * w:word64``,
  blastLib.BBLAST_TAC);

val mc_num2strlen_lemma = mc_num2strlen_def
  |> SIMP_RULE std_ss [LET_DEF,mc_num2strlen_blast]

val mc_num2strlen_thm = prove(
  ``n < 2**30 ==>
    (mc_num2strlen (10w,n2w n,n2w i) = (n2w n, n2w (i + LENGTH (num2str n)))) /\
    mc_num2strlen_pre (10w,n2w n,n2w i) /\
    LENGTH (num2str n) <= 10``,
  SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ `n < 18446744073709551616` by DECIDE_TAC
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w]
  \\ Cases_on `n < 10` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,GSYM ADD_ASSOC,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w,DIV_LT_X]
  \\ Cases_on `n < 100` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,GSYM ADD_ASSOC,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w,DIV_LT_X]
  \\ Cases_on `n < 1000` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,GSYM ADD_ASSOC,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w,DIV_LT_X]
  \\ Cases_on `n < 10000` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,GSYM ADD_ASSOC,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w,DIV_LT_X]
  \\ Cases_on `n < 100000` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,GSYM ADD_ASSOC,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w,DIV_LT_X]
  \\ Cases_on `n < 1000000` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,GSYM ADD_ASSOC,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w,DIV_LT_X]
  \\ Cases_on `n < 10000000` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,GSYM ADD_ASSOC,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w,DIV_LT_X]
  \\ Cases_on `n < 100000000` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,GSYM ADD_ASSOC,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w,DIV_LT_X]
  \\ Cases_on `n < 1000000000` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ ONCE_REWRITE_TAC [mc_num2strlen_lemma,num2str_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w,DIV_EQ_X,GSYM ADD_ASSOC,
       LENGTH_APPEND,dec2str_def,LENGTH,word_add_n2w,word_mul_n2w,DIV_LT_X]
  \\ Cases_on `n < 10000000000` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ `F` by DECIDE_TAC);

val (thm,mc_num2str_loop_def) = basic_decompile_strings x64_tools "mc_num2str_loop"
  (SOME (``(r8:word64,r9:word64,r10:word64,dg:word64 set,g:word64->word8)``,
         ``(dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
START:
       dec r9
       cmp r8,10
       jb EXIT
       mov eax,r10d
       mul r8d       (* r2 has r8 div 10 *)
       lea r0,[4*r2+r2]
       add r0,r0     (* r0 has r8 div 10 * 10 *)
       sub r8,r0     (* r8 has r8 div 10 *)
       add r8,48
       mov BYTE [r9],r8b
       mov r8,r2
       jmp START
EXIT:  add r8,48
       mov BYTE [r9],r8b`)

val FAST_DIV_10 = prove(
  ``!x. x < 2**30 ==> (0x1999999A * x DIV 2**32 = x DIV 10)``,
  REPEAT STRIP_TAC
  \\ `?z. x DIV 10 = z` by METIS_TAC [] \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC);

val SPLIT = METIS_PROVE [] ``b /\ (b1 ==> b2) ==> ((b ==> b1) ==> b2)``;

val mc_num2str_loop_thm = prove(
  ``!n a xs p g.
      ((one_byte_list a xs * p) (fun2set (g,dg))) /\ n < 2**30 ==>
      (LENGTH (num2str n) = LENGTH xs) ==>
      ?g1. mc_num2str_loop_pre(n2w n,a + n2w (LENGTH (num2str n)),0x1999999Aw,dg,g) /\
           (mc_num2str_loop(n2w n,a + n2w (LENGTH (num2str n)),0x1999999Aw,dg,g) = (dg,g1)) /\
           (one_string a (num2str n) * p) (fun2set (g1,dg))``,
  completeInduct_on `n` \\ NTAC 5 STRIP_TAC
  \\ ONCE_REWRITE_TAC [mc_num2str_loop_def]
  \\ `n < 18446744073709551616` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,word_lo_n2w]
  \\ Cases_on `n < 10` THEN1
   (ONCE_REWRITE_TAC [num2str_def] \\ ASM_SIMP_TAC std_ss [DIV_EQ_X]
    \\ SIMP_TAC std_ss [dec2str_def,one_string_def,LENGTH,MAP]
    \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `n + 48 < 256 /\ (n + 48) < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [ORD_CHR]
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,one_byte_list_def,SEP_CLAUSES]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_ADD_SUB,w2w_def,w2n_n2w]
    \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ `n < 4294967296` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_bits_n2w,bitTheory.BITS_THM,w2n_n2w]
  \\ FULL_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [SIMP_RULE std_ss [] FAST_DIV_10,
       mc_num2strlen_blast,word_mul_n2w]
  \\ SIMP_TAC std_ss [word_arith_lemma2]
  \\ `~(n < 10 * (n DIV 10)) /\ (n - 10 * (n DIV 10) = n MOD 10)` by
   (ASSUME_TAC (Q.SPEC `n` (SIMP_RULE std_ss [] (Q.SPEC `10` DIVISION)))
    \\ DECIDE_TAC) \\ ASM_SIMP_TAC std_ss [word_add_n2w]
  \\ ONCE_REWRITE_TAC [num2str_def]
  \\ ASM_SIMP_TAC std_ss [DIV_EQ_X,LENGTH_APPEND,LENGTH,dec2str_def]
  \\ `(xs = []) \/ ?x l. xs = SNOC x l` by METIS_TAC [rich_listTheory.SNOC_CASES]
  \\ ASM_SIMP_TAC std_ss [LENGTH,LENGTH_SNOC,ADD1]
  \\ ASM_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB,WORD_ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [one_string_def,MAP_APPEND,MAP,one_byte_list_APPEND,
       LENGTH_MAP,one_byte_list_def,SEP_CLAUSES,SNOC_APPEND]
  \\ `n MOD 10 < 10` by METIS_TAC [MOD_LESS,DECIDE ``0<10``]
  \\ `n MOD 10 + 48 < 256` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [ORD_CHR]
  \\ `n MOD 10 + 48 < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_add_n2w,w2w_def,w2n_n2w] \\ STRIP_TAC
  \\ Q.ABBREV_TAC `g6 = (a + n2w (LENGTH l) =+ n2w (n MOD 10 + 48)) g`
  \\ Q.PAT_ASSUM `!m.bb` (MP_TAC o Q.SPEC `n DIV 10`)
  \\ MATCH_MP_TAC SPLIT \\ STRIP_TAC
  THEN1 (ASM_SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`a`,`l`,`one (a + n2w (LENGTH (l:word8 list)),n2w (n MOD 10 + 48)) * p`,`g6`])
  \\ MATCH_MP_TAC SPLIT \\ STRIP_TAC THEN1
   (REVERSE STRIP_TAC THEN1 (SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
    \\ Q.UNABBREV_TAC `g6` \\ FULL_SIMP_TAC std_ss [STAR_ASSOC] \\ SEP_W_TAC)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
  \\ SEP_R_TAC \\ EVAL_TAC);

val (mc_num2str_spec,mc_num2str_def) = basic_decompile_strings x64_tools "mc_num2str"
  (SOME (``(r8:word64,r11:word64,dg:word64 set,g:word64->word8)``,
         ``(r11:word64,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
     shr r8,2
     mov r0d,10
     mov r9,r11
     insert mc_num2strlen
     mov r10d,429496730
     mov r11,r9
     insert mc_num2str_loop
  `)

val mc_num2str_blast2 = blastLib.BBLAST_PROVE
  ``(w2w w << 2 !! 0x1w) >>> 2 = (w2w (w:word30)):word64``;

val mc_num2str_thm = prove(
  ``!a.
      (one_byte_list a xs * p) (fun2set (g,dg)) /\ n < 2**30 /\
      (LENGTH (num2str n) = LENGTH xs) ==>
      ?g1. mc_num2str_pre(n2w n << 2 !! 1w,a,dg,g) /\
           (mc_num2str(n2w n << 2 !! 1w,a,dg,g) = (a + n2w (LENGTH (num2str n)),dg,g1)) /\
           (one_string a (num2str n) * p) (fun2set (g1,dg))``,
  Cases \\ SIMP_TAC std_ss [mc_num2str_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ `(n2w n) = (w2w ((n2w n):word30)):word64` by ALL_TAC THEN1
    ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ ASM_SIMP_TAC std_ss [mc_num2str_blast2] \\ POP_ASSUM (K ALL_TAC)
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ ASM_SIMP_TAC std_ss [SIMP_RULE std_ss [] mc_num2strlen_thm]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] mc_num2str_loop_thm)
  \\ FULL_SIMP_TAC std_ss [word_add_n2w]);


(* sym2str
    - find symbol string
    - check if sym2str_aux is needed
    - run wither copy or sym2str_aux
*)

val (thm,mc_sym2str_aux_def) = basic_decompile_strings x64_tools "mc_sym2str_aux"
  (SOME (``(r8:word64,r9:word64,r10:word64,r11:word64,dg:word64 set,g:word64->word8)``,
         ``(r8:word64,r9:word64,r10:word64,r11:word64,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
START:
     cmp r8,r10
     je EXIT
     movzx r0,BYTE [r9+r8]
     inc r8
     cmp r0,0
     je ZERO
     cmp r0,92
     je SLASH
     cmp r0,124
     je BAR
     mov BYTE [r11],r0b
     inc r11
     jmp START
BAR:
     mov BYTE [r11+1],124
     jmp FINISH
SLASH:
     mov BYTE [r11+1],92
     jmp FINISH
ZERO:
     mov BYTE [r11+1],48
FINISH:
     mov BYTE [r11],92
     add r11,2
     jmp START
EXIT:
  `)

val (thm,mc_sym2str_ok_loop_def) = basic_decompile_strings x64_tools "mc_sym2str_ok_loop"
  (SOME (``(r0:word64,r8:word64,r9:word64,r10:word64,dg:word64 set,g:word64->word8)``,
         ``(r0:word64,r8:word64,r9:word64,r10:word64,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
START:
     cmp r8,r10
     je TRUE
     movzx r0,BYTE [r9+r8]
     inc r8
     cmp r0,42
     jb FALSE
     cmp r0,46
     je FALSE
     cmp r0,59
     je FALSE
     cmp r0,124
     je FALSE
     cmp r0,97
     jb START
     cmp r0,122
     ja START
FALSE:
     xor r0,r0
TRUE:
  `)

val (thm,mc_sym2str_ok_def) = basic_decompile_strings x64_tools "mc_sym2str_ok"
  (SOME (``(r8:word64,r9:word64,r10:word64,dg:word64 set,g:word64->word8)``,
         ``(r0:word64,r8:word64,r9:word64,r10:word64,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
START:
     cmp r10,0
     je FALSE
     movzx r0,BYTE [r9]
     cmp r0,57
     ja CONTINUE
     cmp r0,47
     ja FALSE
CONTINUE:
     mov r0d,1
     xor r8,r8
     insert mc_sym2str_ok_loop
     jmp EXIT
FALSE:
     xor r0,r0
EXIT:
  `)

val (thm,mc_sym2str_copy_def) = basic_decompile_strings x64_tools "mc_sym2str_copy"
  (SOME (``(r8:word64,r9:word64,r10:word64,r11:word64,dg:word64 set,g:word64->word8)``,
         ``(r8:word64,r9:word64,r10:word64,r11:word64,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
START:
     movzx r0,BYTE [r9+r8]
     inc r8
     mov BYTE [r11],r0b
     inc r11
     cmp r8,r10
     jne START
  `)

val (thm,mc_lookup_sym_def) = basic_decompile_strings x64_tools "mc_lookup_sym"
  (SOME (``(r8:word64,r9:word64,dg:word64 set,g:word64->word8)``,
         ``(r8:word64,r9:word64,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
L1:  test r8,r8
     je L2
     movzx r0,BYTE [r9]
     add r9,r0
     dec r8
     jmp L1
L2:  `)

val (thm,mc_sym2str_main_def) = basic_decompile_strings x64_tools "mc_sym2str_main"
  (SOME (``(r8:word64,r9:word64,r10:word64,r11:word64,dg:word64 set,g:word64->word8)``,
         ``(r8:word64,r9:word64,r10:word64,r11:word64,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
     insert mc_sym2str_ok
     xor r8,r8
     test r0,r0
     je AUX
     insert mc_sym2str_copy
     jmp EXIT
AUX:
     mov BYTE [r11],124
     inc r11
     insert mc_sym2str_aux
     mov BYTE [r11],124
     inc r11
EXIT:
  `)

val (thm,mc_sym2str_def) = basic_decompile_strings x64_tools "mc_sym2str"
  (SOME (``(r8:word64,r9:word64,r11:word64,dg:word64 set,g:word64->word8)``,
         ``(r8:word64,r9:word64,r11:word64,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
     shr r8,3
     insert mc_lookup_sym
     movzx r10,BYTE [r9]
     inc r9
     dec r10
     insert mc_sym2str_main
  `)

val upper_identifier_char_def = Define `
  upper_identifier_char c = identifier_char c /\ ~(is_lower_case c)`;

val mc_sym2str_ok_loop_thm = prove(
  ``!s n p a.
      (one_string (n2w n + r9) s * p) (fun2set (f,df)) /\
      n + LENGTH s < 256 /\ ~(a = 0w) ==>
      ?ax r8i.
        mc_sym2str_ok_loop_pre (a,n2w n,r9,n2w (n + LENGTH s),df,f) /\
        (mc_sym2str_ok_loop (a,n2w n,r9,n2w (n + LENGTH s),df,f) =
           (ax,r8i,r9,n2w (n + LENGTH s),df,f)) /\
        (~(ax = 0w) = EVERY upper_identifier_char s)``,
  Induct \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL,LENGTH]
  \\ SIMP_TAC std_ss [one_string_def,MAP,one_byte_list_def]
  \\ SIMP_TAC std_ss [GSYM one_string_def]
  \\ ONCE_REWRITE_TAC [mc_sym2str_ok_loop_def]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [EVERY_DEF,LET_DEF]
  \\ `(n + SUC (STRLEN s)) < 18446744073709551616` by DECIDE_TAC
  \\ `n < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,DECIDE ``~(n=n+SUC m)``]
  \\ SEP_R_TAC
  \\ `ORD h < 256` by ASM_SIMP_TAC std_ss [ORD_BOUND]
  \\ `ORD h < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,ORD_BOUND,word_lo_n2w,n2w_11]
  \\ REVERSE (Cases_on `upper_identifier_char h` \\ ASM_SIMP_TAC std_ss [])
  THEN1 (FULL_SIMP_TAC std_ss [upper_identifier_char_def,char_le_def,
           identifier_char_def,GSYM NOT_LESS,is_lower_case_def,
           EVAL ``ORD #"a"``,EVAL ``ORD #"z"``])
  \\ FULL_SIMP_TAC std_ss [upper_identifier_char_def,char_le_def,
           identifier_char_def,GSYM NOT_LESS,is_lower_case_def,
           EVAL ``ORD #"a"``,EVAL ``ORD #"z"``]
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,DECIDE ``n+SUC m = (n+1)+m``]
  \\ SEP_I_TAC "mc_sym2str_ok_loop"
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ SEP_F_TAC \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  \\ `~(ORD h = 0)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  |> Q.SPECL [`s`,`0`,`p`,`1w`] |> SIMP_RULE wstd_ss [WORD_ADD_0,ADD_CLAUSES,n2w_11]
  |> GEN_ALL;

val upper_identifier_char_thm = prove(
  ``!s. EVERY upper_identifier_char s =
        EVERY identifier_char s /\ EVERY (\c. ~is_lower_case c) s``,
  Induct \\ ASM_SIMP_TAC std_ss [EVERY_DEF,upper_identifier_char_def]
  \\ SIMP_TAC std_ss [AC CONJ_ASSOC CONJ_COMM]);

val mc_sym2str_ok_thm = prove(
  ``(one_string r9 s * p) (fun2set (f,df)) /\ LENGTH s < 256 ==>
    ?ax r8i.
      mc_sym2str_ok_pre (r8,r9,n2w (LENGTH s),df,f) /\
      (mc_sym2str_ok (r8,r9,n2w (LENGTH s),df,f) =
         (ax,r8i,r9,n2w (LENGTH s),df,f)) /\
      (~(ax = 0w) = identifier_string s /\ EVERY (\c. ~is_lower_case c) s)``,
  SIMP_TAC wstd_ss [mc_sym2str_ok_def,n2w_11,LENGTH_NIL]
  \\ Cases_on `s = ""` \\ ASM_SIMP_TAC std_ss [LET_DEF] THEN1 EVAL_TAC
  \\ ASM_SIMP_TAC std_ss [identifier_string_def] \\ REPEAT STRIP_TAC
  \\ `r9 IN df /\ (f r9 = n2w (ORD (HD s)))` by ALL_TAC THEN1
   (Cases_on `s` \\ FULL_SIMP_TAC std_ss [one_string_def,one_byte_list_def,MAP,HD]
    \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,word_lo_n2w]
  \\ Cases_on `number_char (HD s)` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [number_char_def] \\ ASM_SIMP_TAC std_ss [LESS_EQ]
    \\ `~(58 <= ORD (HD s))` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [number_char_def]
  \\ IMP_RES_TAC mc_sym2str_ok_loop_thm \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LESS_EQ,upper_identifier_char_thm]);

val mc_sym2str_copy_thm = prove(
  ``!s t n p r11 f.
      (one_string (n2w n + r9) s * one_string r11 t * p) (fun2set (f,df)) /\
      n + LENGTH s < 256 /\ (LENGTH t = LENGTH s) /\ ~(s = "") ==>
      ?fi.
        mc_sym2str_copy_pre (n2w n,r9,n2w (n + LENGTH s),r11,df,f) /\
        (mc_sym2str_copy (n2w n,r9,n2w (n + LENGTH s),r11,df,f) =
           (n2w (n + LENGTH s),r9,n2w (n + LENGTH s),r11 + n2w (LENGTH s),df,fi)) /\
        (one_string (n2w n + r9) s * one_string r11 s * p) (fun2set (fi,df))``,
  Induct \\ SIMP_TAC std_ss [] \\ Cases_on `t` \\ SIMP_TAC std_ss [ADD1,LENGTH]
  \\ ONCE_REWRITE_TAC [DECIDE ``n+1=1+n:num``] \\ SIMP_TAC std_ss [NOT_CONS_NIL]
  \\ SIMP_TAC std_ss [one_string_def,MAP,one_byte_list_def]
  \\ SIMP_TAC std_ss [GSYM one_string_def,STAR_ASSOC,ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [mc_sym2str_copy_def] \\ REPEAT STRIP_TAC
  \\ `n+1 < 256` by DECIDE_TAC
  \\ SEP_R_TAC \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,LET_DEF,word_add_n2w,n2w_11]
  \\ SEP_W_TAC \\ ASM_SIMP_TAC std_ss [DECIDE ``(n=n+k)=(k=0:num)``,LENGTH_NIL]
  \\ Cases_on `s = ""` \\ ASM_SIMP_TAC std_ss []
  THEN1 (Cases_on `t' = ""` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_NIL])
  \\ SEP_I_TAC "mc_sym2str_copy"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`t'`,`one (n2w n + r9,n2w (ORD h')) *
       one (r11,n2w (ORD h')) * p`])
  \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM word_add_n2w,AC WORD_ADD_COMM WORD_ADD_ASSOC])
  |> Q.SPECL [`s`,`t`,`0`,`p`] |> SIMP_RULE wstd_ss [WORD_ADD_0,ADD_CLAUSES,n2w_11]
  |> GEN_ALL;

val ORD_CHR_IMP = prove(``n<256 ==> (ORD (CHR n) = n)``,METIS_TAC [ORD_CHR]);

val mc_sym2str_aux_thm = prove(
  ``!s t n p r11 f.
      (one_string (n2w n + r9) s * one_string r11 t * p) (fun2set (f,df)) /\
      n + LENGTH s < 256 /\ (LENGTH t = LENGTH (sym2str_aux s)) ==>
      ?fi.
        mc_sym2str_aux_pre (n2w n,r9,n2w (n + LENGTH s),r11,df,f) /\
        (mc_sym2str_aux (n2w n,r9,n2w (n + LENGTH s),r11,df,f) =
           (n2w (n + LENGTH s),r9,n2w (n + LENGTH s),r11 + n2w (LENGTH (sym2str_aux s)),df,fi)) /\
        (one_string (n2w n + r9) s * one_string r11 (sym2str_aux s) * p) (fun2set (fi,df))``,
  Induct \\ SIMP_TAC std_ss [sym2str_aux_def,LENGTH,LENGTH_NIL]
  THEN1 (ONCE_REWRITE_TAC [mc_sym2str_aux_def] \\ SIMP_TAC std_ss [WORD_ADD_0])
  \\ STRIP_TAC \\ Cases_on `ORD h = 0` THEN1
   (Cases_on `t` \\ ASM_SIMP_TAC std_ss [ADD1,LENGTH]
    \\ Cases_on `t'` \\ ASM_SIMP_TAC std_ss [ADD1,LENGTH]
    \\ ONCE_REWRITE_TAC [DECIDE ``n+1=1+n:num``]
    \\ SIMP_TAC std_ss [one_string_def,MAP,one_byte_list_def]
    \\ SIMP_TAC std_ss [GSYM one_string_def,STAR_ASSOC,ADD_ASSOC,word_arith_lemma1]
    \\ ONCE_REWRITE_TAC [mc_sym2str_aux_def] \\ REPEAT STRIP_TAC
    \\ `n < 256` by DECIDE_TAC
    \\ SEP_R_TAC \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,LET_DEF,word_add_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [DECIDE ``~(n=n+1+k)``,LENGTH_NIL]
    \\ ASM_SIMP_TAC std_ss [ORD_CHR_IMP]
    \\ SEP_W_TAC
    \\ SEP_I_TAC "mc_sym2str_aux"
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t`,`one (n2w n + r9,0x0w) *
         one (r11,0x5Cw) * one (r11 + 0x1w,0x30w) * p`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (Q.PAT_ASSUM `ORD h = 0` ASSUME_TAC
      \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM word_add_n2w,AC WORD_ADD_COMM WORD_ADD_ASSOC]
      \\ SEP_WRITE_TAC)
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [word_add_n2w]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM word_add_n2w,AC WORD_ADD_COMM WORD_ADD_ASSOC])
  \\ ASM_SIMP_TAC std_ss [MEM]
  \\ Cases_on `h = #"|"` THEN1
   (Cases_on `t` \\ ASM_SIMP_TAC std_ss [ADD1,LENGTH]
    \\ Cases_on `t'` \\ ASM_SIMP_TAC std_ss [ADD1,LENGTH]
    \\ ONCE_REWRITE_TAC [DECIDE ``n+1=1+n:num``]
    \\ SIMP_TAC std_ss [one_string_def,MAP,one_byte_list_def]
    \\ SIMP_TAC std_ss [GSYM one_string_def,STAR_ASSOC,ADD_ASSOC,word_arith_lemma1]
    \\ ONCE_REWRITE_TAC [mc_sym2str_aux_def] \\ REPEAT STRIP_TAC
    \\ `n < 256` by DECIDE_TAC
    \\ SEP_R_TAC \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,LET_DEF,word_add_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [DECIDE ``~(n=n+1+k)``,LENGTH_NIL]
    \\ FULL_SIMP_TAC std_ss [ORD_CHR_IMP]
    \\ SEP_W_TAC
    \\ SEP_I_TAC "mc_sym2str_aux"
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t`,`one (n2w n + r9,0x7Cw) *
         one (r11,0x5Cw) * one (r11 + 0x1w,0x7Cw) * p`])
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM word_add_n2w,AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [word_add_n2w])
  \\ Cases_on `h = #"\\"` THEN1
   (Cases_on `t` \\ ASM_SIMP_TAC std_ss [ADD1,LENGTH]
    \\ Cases_on `t'` \\ ASM_SIMP_TAC std_ss [ADD1,LENGTH]
    \\ ONCE_REWRITE_TAC [DECIDE ``n+1=1+n:num``]
    \\ SIMP_TAC std_ss [one_string_def,MAP,one_byte_list_def]
    \\ SIMP_TAC std_ss [GSYM one_string_def,STAR_ASSOC,ADD_ASSOC,word_arith_lemma1]
    \\ ONCE_REWRITE_TAC [mc_sym2str_aux_def] \\ REPEAT STRIP_TAC
    \\ `n < 256` by DECIDE_TAC
    \\ SEP_R_TAC \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,LET_DEF,word_add_n2w,n2w_11]
    \\ ASM_SIMP_TAC std_ss [DECIDE ``~(n=n+1+k)``,LENGTH_NIL]
    \\ FULL_SIMP_TAC std_ss [ORD_CHR_IMP]
    \\ SEP_W_TAC
    \\ SEP_I_TAC "mc_sym2str_aux"
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t`,`one (n2w n + r9,0x5Cw) *
         one (r11,0x5Cw) * one (r11 + 0x1w,0x5Cw) * p`])
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM word_add_n2w,AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [word_add_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `t` \\ SIMP_TAC std_ss [ADD1,LENGTH]
  \\ ONCE_REWRITE_TAC [DECIDE ``n+1=1+n:num``] \\ SIMP_TAC std_ss [NOT_CONS_NIL]
  \\ SIMP_TAC std_ss [one_string_def,MAP,one_byte_list_def]
  \\ SIMP_TAC std_ss [GSYM one_string_def,STAR_ASSOC,ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [mc_sym2str_aux_def] \\ REPEAT STRIP_TAC
  \\ `n < 256` by DECIDE_TAC
  \\ ASM_SIMP_TAC wstd_ss [DECIDE ``~(n=n+1+k)``,LENGTH_NIL,n2w_11,LET_DEF]
  \\ SEP_R_TAC \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,LET_DEF,word_add_n2w,n2w_11]
  \\ FULL_SIMP_TAC std_ss [GSYM ORD_11,ORD_CHR_IMP]
  \\ SEP_W_TAC \\ ASM_SIMP_TAC std_ss [LENGTH_NIL]
  \\ SEP_I_TAC "mc_sym2str_aux"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`t'`,`one (n2w n + r9,n2w (ORD h)) *
       one (r11,n2w (ORD h)) * p`])
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM word_add_n2w,AC WORD_ADD_COMM WORD_ADD_ASSOC]);

val mc_sym2str_thm = prove(
  ``(one_string r9 s * one_string r11 t * p) (fun2set (f,df)) /\
    LENGTH s < 256 /\ (LENGTH t = LENGTH (sym2str s)) ==>
    ?fi r8i r9i.
      mc_sym2str_main_pre (r8,r9,n2w (LENGTH s),r11,df,f) /\
      (mc_sym2str_main (r8,r9,n2w (LENGTH s),r11,df,f) =
         (r8i,r9i,n2w (LENGTH s),r11 + n2w (LENGTH (sym2str s)),df,fi)) /\
      (one_string r9 s * one_string r11 (sym2str s) * p) (fun2set (fi,df))``,
  SIMP_TAC std_ss [mc_sym2str_main_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC]
  \\ IMP_RES_TAC mc_sym2str_ok_thm \\ POP_ASSUM (MP_TAC o Q.SPEC `r8`)
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ `sym2str s = if ax = 0w then "|" ++ sym2str_aux s ++ "|" else s` by
      (SIMP_TAC std_ss [sym2str_def] \\ METIS_TAC [])
  \\ `~(ax = 0w) ==> ~(s = "")` by
        (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [identifier_string_def])
  \\ Q.PAT_ASSUM `ax <> 0x0w <=> bbb` (K ALL_TAC)
  \\ REVERSE (Cases_on `ax = 0w`) \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
  THEN1 (IMP_RES_TAC mc_sym2str_copy_thm \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [APPEND,APPEND_ASSOC,LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ Cases_on `t' = []` THEN1 (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND,ADD1])
  \\ `?h2 ts. t' = SNOC h2 ts` by METIS_TAC [rich_listTheory.SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,LENGTH_APPEND,LENGTH]
  \\ FULL_SIMP_TAC std_ss [one_string_def,one_byte_list_APPEND,MAP,MAP_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,GSYM one_string_def,SEP_CLAUSES,LENGTH_MAP]
  \\ SIMP_TAC std_ss [ORD_CHR_RWT]
  \\ `(one_string r9 s * one_string (r11 + 0x1w) ts * (one (r11,0x7Cw) *
       one (r11 + 0x1w + n2w (STRLEN (sym2str_aux s)),n2w (ORD h2)) * p))
        (fun2set ((r11 =+ 0x7Cw) f,df))` by SEP_WRITE_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [WORD_ADD_0] (Q.SPECL [`s`,`t`,`0`] mc_sym2str_aux_thm))
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,AC ADD_ASSOC ADD_COMM]
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC);


(* printing lemmas *)

val LENGTH_EXPAND = prove(
  ``((LENGTH xs = 1) ==> (?x0. xs = [x0])) /\
    ((LENGTH xs = 2) ==> (?x0 x1. xs = [x0;x1])) /\
    ((LENGTH xs = 3) ==> (?x0 x1 x2. xs = [x0;x1;x2])) /\
    ((LENGTH xs = 4) ==> (?x0 x1 x2 x3. xs = [x0;x1;x2;x3]))``,
  Cases_on `xs` \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL] \\ DECIDE_TAC);

val null_term_str_CONS_NOT_NIL = prove(
  ``!a s t. null_term_str a dg g (x::xs) /\ null_term_str a dg g "" ==> (HD [2] = 5)``,
  SIMP_TAC std_ss [null_term_str_def,APPEND]
  \\ SIMP_TAC std_ss [one_string_def,MAP,EVERY_DEF,one_byte_list_def,
       ORD_CHR_RWT,SEP_CLAUSES]
  \\ REPEAT STRIP_TAC
  \\ `g a = 0w` by SEP_READ_TAC
  \\ `g a = n2w (ORD x)` by SEP_READ_TAC
  \\ FULL_SIMP_TAC wstd_ss [n2w_11]
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [ORD_CHR_RWT])
  |> SIMP_RULE std_ss [HD];

val null_term_str_CONS = prove(
  ``null_term_str a dg g (x::xs) ==> null_term_str (a+1w) dg g xs /\ (g a = n2w (ORD x))``,
  SIMP_TAC std_ss [null_term_str_def,APPEND,one_string_def,
    one_byte_list_def,MAP,EVERY_DEF] \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `p * one (a,n2w (ORD x))` \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ SEP_R_TAC);

val null_term_str_unique = prove(
  ``!a s t. null_term_str a dg g s /\ null_term_str a dg g t ==> (s = t)``,
  Induct_on `s` THEN1
   (Cases_on `t` \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL]
    \\ METIS_TAC [null_term_str_CONS_NOT_NIL])
  \\ Cases_on `t` THEN1
   (ASM_SIMP_TAC std_ss [NOT_CONS_NIL]
    \\ METIS_TAC [null_term_str_CONS_NOT_NIL])
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [CONS_11]
  \\ IMP_RES_TAC null_term_str_CONS \\ RES_TAC
  \\ FULL_SIMP_TAC wstd_ss [n2w_11,ORD_11]);

val null_term_str_IMP = prove(
  ``null_term_str a dg g s ==> (mem2string a dg g = s) /\ exists_null_term_str a dg g``,
  SIMP_TAC std_ss [mem2string_def,exists_null_term_str_def]
  \\ METIS_TAC [null_term_str_unique]);


(* print a newline character *)

val (mc_print_nl_spec,mc_print_nl_def) = basic_decompile_strings x64_tools "mc_print_nl"
  (SOME (``(ior:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r0:word64,r1:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       mov r1,[r7-192]
       mov r0,[r7-216]
       mov BYTE [r0], 10
       mov BYTE [r0+1], 0
       insert io_write
       mov r0d,3
       mov r1d,1
     `);

val _ = save_thm("mc_print_nl_spec",mc_print_nl_spec);

val mc_print_nl_thm = store_thm("mc_print_nl_thm",
  ``^LISP ==>
    ?g2. mc_print_nl_pre (EL 0 cs,sp,df,f,dg,g,io) /\
         (mc_print_nl (EL 0 cs,sp,df,f,dg,g,io) =
           (EL 0 cs,tw0,tw1,sp,df,f,dg,g2,IO_WRITE io "\n")) /\
         let (g,io) = (g2,IO_WRITE io "\n") in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,mc_print_nl_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`2`,`[10w;0w]`] lisp_inv_temp_string))
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.ABBREV_TAC `g3 = (sa2 + 0x1w =+ 0x0w) ((sa2 =+ 0xAw) g)`
  \\ IMP_RES_TAC LENGTH_EXPAND
  \\ `(one_byte_list sa2 [0xAw; 0x0w] * p) (fun2set (g3,dg)) /\
      sa2 IN dg /\ sa2+1w IN dg` by ALL_TAC THEN1
     (Q.UNABBREV_TAC `g3`
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,SEP_CLAUSES,STAR_ASSOC]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ `null_term_str sa2 dg g3 "\n"` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [null_term_str_def,one_string_def,MAP,APPEND,
      ORD_CHR_RWT,EVERY_DEF,CHR_11] \\ METIS_TAC [])
  \\ IMP_RES_TAC null_term_str_IMP
  \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [lisp_inv_ignore_io]);


(* print num *)

val (thm,mc_print_num_def) = basic_decompile_strings x64_tools "mc_print_num"
  (SOME (``(ior:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       mov r11,[r7-216]
       insert mc_num2str
       mov BYTE [r11], 0
       mov r1,[r7-192]
       mov r0,[r7-216]
       insert io_write
     `);

val mc_print_num_thm = prove(
  ``^LISP ==>
    n < 2**30 ==>
    ?g2. mc_print_num_pre (EL 0 cs,sp,n2w n << 2 !! 1w,df,f,dg,g,io)/\
         (mc_print_num (EL 0 cs,sp,n2w n << 2 !! 1w,df,f,dg,g,io) =
           (EL 0 cs,sp,df,f,dg,g2,IO_WRITE io (num2str n))) /\
         let (g,io) = (g2,IO_WRITE io (num2str n)) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,mc_print_num_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ Q.PAT_ASSUM `lisp_inv xx yyy zzz` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`LENGTH (num2str n) + 1`,`MAP (n2w o ORD) (num2str n) ++ [0w]`] lisp_inv_temp_string))
  \\ POP_ASSUM (MP_TAC o Q.SPEC `n`)
  \\ `LENGTH (num2str n) <= 10` by METIS_TAC [EVAL ``(2**30):num``,mc_num2strlen_thm]
  \\ `STRLEN (num2str n) + 1 <= 520` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ `(str = []) \/ ?x l. str = SNOC x l` by METIS_TAC [rich_listTheory.SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,SNOC_APPEND,LENGTH_APPEND,one_byte_list_APPEND]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_def,SEP_CLAUSES,LENGTH_MAP,GSYM STAR_ASSOC]
  \\ ASSUME_TAC (GEN_ALL mc_num2str_thm)
  \\ SEP_I_TAC "mc_num2str"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`l`,`one (sa2 + n2w (STRLEN (num2str n)),x) * p`])
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `LENGTH l = sss` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `g3 = (sa2 + n2w (STRLEN (num2str n)) =+ 0x0w) g1`
  \\ `(one_string sa2 (num2str n) *
        (one (sa2 + n2w (STRLEN (num2str n)),0w) * p)) (fun2set (g3,dg))` by
       (Q.UNABBREV_TAC `g3` \\ SEP_WRITE_TAC)
  \\ `null_term_str sa2 dg g3 (num2str n)` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [null_term_str_def,one_string_def,one_byte_list_APPEND,
       MAP_APPEND,MAP,SEP_CLAUSES,LENGTH_MAP,one_byte_list_def,ORD_CHR_RWT]
    \\ Q.EXISTS_TAC `p` \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ STRIP_ASSUME_TAC (Q.SPEC `n` str2num_num2str)
    \\ POP_ASSUM MP_TAC \\ MATCH_MP_TAC MONO_EVERY \\ Cases
    \\ FULL_SIMP_TAC std_ss [number_char_def,CHR_11,ORD_CHR_RWT] \\ DECIDE_TAC)
  \\ IMP_RES_TAC null_term_str_IMP \\ ASM_SIMP_TAC std_ss []
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def] \\ SEP_R_TAC
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_io) \\ Q.EXISTS_TAC `io`
  \\ Q.PAT_ASSUM `!g2. bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def])
  |> SIMP_RULE std_ss [LET_DEF];

val (mc_print_num_full_spec,mc_print_num_full_def) = basic_decompile_strings x64_tools "mc_print_num_full"
  (SOME (``(ior:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r0:word64,r1:word64,r2:word64,r7:word64,r8:word64,r9:word64,r10:word64,r11:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       insert mc_print_num
       mov r0d,3
       mov r1d,1
       mov r2d,r0d
       mov r8d,r0d
       mov r9d,r0d
       mov r10d,r0d
       mov r11d,r0d
     `);

val _ = save_thm("mc_print_num_full_spec",mc_print_num_full_spec);

val mc_print_num_full_blast = blastLib.BBLAST_PROVE
  ``w2w (w !! 0x1w) = w2w (w:word32) !! 1w:word64``

val lisp_inv_nil_lemma = el 1 (CONJUNCTS lisp_inv_Sym)
  |> UNDISCH |> CONJUNCTS |> hd |> DISCH_ALL |> GEN_ALL

val mc_print_num_full_thm = prove(
  ``^LISP ==>
    isVal x0 ==>
    ?g2 v0 v1 v2 v3 v4.
       mc_print_num_full_pre (EL 0 cs,sp,w2w w0,df,f,dg,g,io)/\
      (mc_print_num_full (EL 0 cs,sp,w2w w0,df,f,dg,g,io) =
         (EL 0 cs,tw0,tw1,tw0,sp,w2w v0,w2w v1,w2w v2,w2w v3,df,f,dg,g2,IO_WRITE io (num2str (getVal x0)))) /\
         let (g,io,w0,w1,w2,w3,x0,x1,x2,x3,tw2) =
             (g2,IO_WRITE io (num2str (getVal x0)),v0,v1,v2,v3,Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",tw0)
         in ^LISP``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [isVal_thm] \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [mc_print_num_full_def,LET_DEF,EVAL ``(31 -- 0) 3w:word64``]
  \\ `(w0 = n2w a << 2 !! 1w) /\ a < 2**30` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [lisp_inv_def,MAP,EVERY_DEF,CONS_11,lisp_x_def]
     \\ Q.PAT_ASSUM `ref_heap_addr s0 = w0` (ASSUME_TAC o GSYM)
     \\ FULL_SIMP_TAC wstd_ss [ref_heap_addr_def,w2w_def,w2n_n2w])
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,mc_print_num_full_blast]
  \\ `(4 * a) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [WORD_MUL_LSL,word_mul_n2w] mc_print_num_thm)
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [getVal_def]
  \\ Q.LIST_EXISTS_TAC [`3w`,`3w`,`3w`,`3w`] \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
  \\ MATCH_MP_TAC lisp_inv_nil_lemma \\ Q.LIST_EXISTS_TAC [`x3`,`w3`]
  \\ MATCH_MP_TAC lisp_inv_swap3
  \\ MATCH_MP_TAC lisp_inv_nil_lemma \\ Q.LIST_EXISTS_TAC [`x2`,`w2`]
  \\ MATCH_MP_TAC lisp_inv_swap2
  \\ MATCH_MP_TAC lisp_inv_nil_lemma \\ Q.LIST_EXISTS_TAC [`x1`,`w1`]
  \\ MATCH_MP_TAC lisp_inv_swap1
  \\ MATCH_MP_TAC lisp_inv_nil_lemma
  \\ Q.LIST_EXISTS_TAC [`Val a`,`n2w (4 * a) !! 1w`]
  \\ MATCH_MP_TAC lisp_inv_ignore_tw2 \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_print_num_full_thm",mc_print_num_full_thm);


(* print symbol *)

val (thm,mc_print_sym_def) = basic_decompile_strings x64_tools "mc_print_sym"
  (SOME (``(ior:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       shr r8,3
       mov r9,[r7-224]
       insert mc_lookup_sym
       movzx r10,BYTE [r9]
       inc r9
       dec r10
       mov r11,[r7-216]
       insert mc_sym2str_main
       mov BYTE [r11], 0
       mov r1,[r7-192]
       mov r0,[r7-216]
       insert io_write
     `);

val mc_lookup_sym_thm = prove(
  ``!xs a k i p.
      (LIST_FIND k s xs = SOME (k+i)) /\ i < 2**32 /\
      EVERY (\x. LENGTH x < 255) xs /\
      (one_byte_list a (symbol_list xs) * p) (fun2set (g,dg)) ==>
      ?a2 q. mc_lookup_sym_pre (n2w i,a,dg,g) /\
             (mc_lookup_sym (n2w i,a,dg,g) = (0w,a2,dg,g)) /\
             (one_byte_list a2 (string_data s) * q * p) (fun2set (g,dg)) /\
             (one_byte_list a2 (string_data s) * q = one_byte_list a (symbol_list xs))``,
  Induct \\ SIMP_TAC std_ss [LIST_FIND_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `s = h` \\ FULL_SIMP_TAC std_ss [] THEN1
   (`i = 0` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [mc_lookup_sym_def] \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [one_symbol_list_def,SEP_CLAUSES,
          SEP_EXISTS_THM,cond_STAR,symbol_list_def,one_byte_list_APPEND]
    \\ Q.EXISTS_TAC `one_byte_list (a + n2w (LENGTH (string_data h)))
         (symbol_list xs)`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [one_symbol_list_def,SEP_CLAUSES,
        SEP_EXISTS_THM,cond_STAR,symbol_list_def,RW1[STAR_COMM]one_byte_list_APPEND]
  \\ ONCE_REWRITE_TAC [mc_lookup_sym_def] \\ FULL_SIMP_TAC std_ss []
  \\ `i < 18446744073709551616` by DECIDE_TAC
  \\ IMP_RES_TAC LIST_FIND_LESS_EQ
  \\ `~(i = 0)` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF]
  \\ Cases_on `i` \\ FULL_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [string_data_def,one_byte_list_def,STAR_ASSOC]
  \\ SEP_R_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,EVERY_DEF]
  \\ `(STRLEN h + 1) < 256` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `n < 4294967296` by DECIDE_TAC
  \\ SEP_I_TAC "mc_lookup_sym" \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `k+1`)
  \\ FULL_SIMP_TAC std_ss [DECIDE ``k + SUC n = k + 1 + n``]
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_MAP,ADD1] \\ SEP_F_TAC
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ POP_ASSUM (MP_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `q * one (a,n2w (STRLEN h + 1)) * one_byte_list (a + 0x1w) (MAP (n2w o ORD) h)`
  \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val mc_print_sym_blast = blastLib.BBLAST_PROVE
  ``w2w (w2w (w:29 word) << 3 !! 0x3w:word32) >>> 3 = (w2w w):word64``

val LENGTH_sym2str = prove(
  ``!s. LENGTH (sym2str s) <= 2 * LENGTH s + 2``,
  SIMP_TAC std_ss [sym2str_def] \\ SRW_TAC [] [] THEN1 DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC] \\ POP_ASSUM (K ALL_TAC)
  \\ Induct_on `s` \\ ASM_SIMP_TAC std_ss [LENGTH,sym2str_aux_def]
  \\ SRW_TAC [] [LENGTH] \\ DECIDE_TAC);

val one_string_MAP = prove(
  ``!xs a. one_string a (MAP (CHR o w2n) xs) = one_byte_list a xs``,
  Induct \\ FULL_SIMP_TAC std_ss [one_string_def,MAP,one_byte_list_def]
  \\ REPEAT STRIP_TAC \\ `n2w (ORD (CHR (w2n h))) = h` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `h`
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,ORD_CHR_RWT]);

val EVERY_NOT_NULL_sym2str = prove(
  ``!s. EVERY (\x. x <> CHR 0) (sym2str s)``,
  SIMP_TAC std_ss [sym2str_def] \\ SRW_TAC [] [] THEN1
   (FULL_SIMP_TAC std_ss [identifier_string_def]
    \\ Q.PAT_ASSUM `EVERY identifier_char s` MP_TAC \\ MATCH_MP_TAC MONO_EVERY
    \\ FULL_SIMP_TAC std_ss [identifier_char_def,ORD_CHR_RWT])
  \\ POP_ASSUM (K ALL_TAC) \\ Induct_on `s`
  \\ SRW_TAC [] [sym2str_aux_def,EVERY_DEF,CHR_11]
  \\ SRW_TAC [] [sym2str_aux_def,EVERY_DEF,CHR_11]
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [ORD_CHR_RWT,CHR_11]);

val mc_print_sym_thm = prove(
  ``(let x0 = Sym s in ^LISP) ==>
    ?g2. mc_print_sym_pre (EL 0 cs,sp,w2w w0,df,f,dg,g,io) /\
         (mc_print_sym (EL 0 cs,sp,w2w w0,df,f,dg,g,io) =
                       (EL 0 cs,sp,df,f,dg,g2,IO_WRITE io (sym2str s))) /\
         (let (x0,g,io) = (Sym s,g2,IO_WRITE io (sym2str s)) in ^LISP)``,
  SIMP_TAC std_ss [LET_DEF,mc_print_sym_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ Q.PAT_ASSUM `lisp_inv xx yyy zzz` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `lisp_inv xx yyy zzz` MP_TAC
  \\ SIMP_TAC std_ss [Once lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [symtable_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [one_symbol_list_def,SEP_EXISTS_THM,cond_STAR]
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,lisp_x_def]
  \\ Q.PAT_ASSUM `MAP ref_heap_addr xx = yy` (MP_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,mc_print_sym_blast]
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,one_byte_list_APPEND]
  \\ ASSUME_TAC (GEN_ALL (SIMP_RULE std_ss [ADD_CLAUSES] (Q.SPECL [`xs`,`a`,`0`] mc_lookup_sym_thm)))
  \\ SEP_I_TAC "mc_lookup_sym"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`INIT_SYMBOLS ++ sym`,`s`,`one_byte_list
          (sa1 + n2w (LENGTH (symbol_list (INIT_SYMBOLS ++ sym)))) ys`])
  \\ `k < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [string_data_def,one_byte_list_def,STAR_ASSOC]
  \\ `(n2w (w2n (g a2')) - 0x1w = (n2w (LENGTH s)):word64) /\
      LENGTH s < 256` by ALL_TAC THEN1
   (SEP_R_TAC \\ FULL_SIMP_TAC wstd_ss [w2n_n2w] \\ IMP_RES_TAC LIST_FIND_MEM
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ RES_TAC
    \\ `LENGTH s + 1 < 256 /\ LENGTH s < 256` by DECIDE_TAC
    \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,GSYM word_add_n2w,WORD_ADD_SUB])
  \\ FULL_SIMP_TAC std_ss [GSYM one_string_def]
  \\ Q.ABBREV_TAC `syml = LENGTH (symbol_list (INIT_SYMBOLS ++ sym))`
  \\ `LENGTH (sym2str s) < LENGTH ys` by ALL_TAC THEN1
   (MATCH_MP_TAC LESS_EQ_LESS_TRANS \\ Q.EXISTS_TAC `2 * LENGTH s + 2`
    \\ ASM_SIMP_TAC std_ss [LENGTH_sym2str] \\ DECIDE_TAC)
  \\ IMP_RES_TAC SPLIT_LIST
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def,STAR_ASSOC]
  \\ ASSUME_TAC (GEN_ALL mc_sym2str_thm)
  \\ SEP_I_TAC "mc_sym2str_main"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`MAP (CHR o w2n) (xs1':word8 list)`,`one (a2',n2w (STRLEN s + 1)) * q *
        one (sa1 + n2w syml + n2w (STRLEN (sym2str s)),x) *
        one_byte_list (sa1 + n2w syml + n2w (STRLEN (sym2str s)) + 0x1w)
          xs2`])
  \\ FULL_SIMP_TAC (std_ss++star_ss) [LENGTH_MAP,one_string_MAP]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `gi = ((sa1 + n2w syml + n2w (STRLEN (sym2str s)) =+ 0x0w) fi)`
  \\ `(q * one_string (sa1 + n2w syml) (sym2str s) *
        one_string (a2' + 0x1w) s * one (a2',n2w (STRLEN s + 1)) *
        one (sa1 + n2w syml + n2w (STRLEN (sym2str s)),0w) *
        one_byte_list (sa1 + n2w syml + n2w (STRLEN (sym2str s)) + 0x1w)
          xs2) (fun2set (gi,dg))`
       by (Q.UNABBREV_TAC `gi` \\ SEP_WRITE_TAC)
  \\ SEP_R_TAC
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ `null_term_str (sa1 + n2w syml) dg gi (sym2str s)` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [null_term_str_def]
    \\ Q.EXISTS_TAC `q *
        one_string (a2' + 0x1w) s * one (a2',n2w (STRLEN s + 1)) *
        one_byte_list (sa1 + n2w syml + n2w (STRLEN (sym2str s)) + 0x1w)
          xs2`
    \\ FULL_SIMP_TAC std_ss [one_string_def,one_byte_list_APPEND,LENGTH_MAP,
        one_byte_list_def,SEP_CLAUSES,MAP,ORD_CHR_RWT,MAP_APPEND]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [LENGTH_MAP,one_string_MAP,
         EVERY_NOT_NULL_sym2str])
  \\ IMP_RES_TAC null_term_str_IMP \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_io) \\ Q.EXISTS_TAC `io`
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11,ref_heap_addr_def]
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,lisp_x_def]
  \\ FULL_SIMP_TAC std_ss [symtable_inv_def,one_symbol_list_def,SEP_EXISTS_THM,
       cond_STAR,one_byte_list_APPEND]
  \\ Q.EXISTS_TAC `MAP (n2w o ORD) (sym2str s) ++ 0w::xs2`
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_MAP,MAP,LENGTH,
       one_byte_list_APPEND,one_byte_list_def]
  \\ Q.UNABBREV_TAC `syml`
  \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM one_string_def])
  |> SIMP_RULE std_ss [LET_DEF];

val (mc_print_sym_full_spec,mc_print_sym_full_def) = basic_decompile_strings x64_tools "mc_print_sym_full"
  (SOME (``(ior:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r0:word64,r1:word64,r7:word64,r8:word64,r9:word64,r10:word64,r11:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       insert mc_print_sym
       mov r0d,3
       mov r1d,1
       mov r8d,r0d
       mov r9d,r0d
       mov r10d,r0d
       mov r11d,r0d
     `);

val _ = save_thm("mc_print_sym_full_spec",mc_print_sym_full_spec);

val mc_print_sym_full_blast = blastLib.BBLAST_PROVE
  ``w2w (w !! 0x1w) = w2w (w:word32) !! 1w:word64``

val lisp_inv_nil_lemma = el 1 (CONJUNCTS lisp_inv_Sym)
  |> UNDISCH |> CONJUNCTS |> hd |> DISCH_ALL |> GEN_ALL

val mc_print_sym_full_thm = prove(
  ``^LISP ==>
    isSym x0 ==>
    ?g2 v0 v1 v2 v3 v4.
       mc_print_sym_full_pre (EL 0 cs,sp,w2w w0,df,f,dg,g,io)/\
      (mc_print_sym_full (EL 0 cs,sp,w2w w0,df,f,dg,g,io) =
         (EL 0 cs,tw0,tw1,sp,w2w v0,w2w v1,w2w v2,w2w v3,df,f,dg,g2,IO_WRITE io (sym2str (getSym x0)))) /\
         let (g,io,w0,w1,w2,w3,x0,x1,x2,x3) =
             (g2,IO_WRITE io (sym2str (getSym x0)),v0,v1,v2,v3,Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL")
         in ^LISP``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [isSym_thm] \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [mc_print_sym_full_def,LET_DEF,EVAL ``(31 -- 0) 3w:word64``]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [WORD_MUL_LSL,word_mul_n2w] mc_print_sym_thm)
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [getSym_def]
  \\ Q.LIST_EXISTS_TAC [`3w`,`3w`,`3w`,`3w`] \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
  \\ MATCH_MP_TAC lisp_inv_nil_lemma \\ Q.LIST_EXISTS_TAC [`x3`,`w3`]
  \\ MATCH_MP_TAC lisp_inv_swap3
  \\ MATCH_MP_TAC lisp_inv_nil_lemma \\ Q.LIST_EXISTS_TAC [`x2`,`w2`]
  \\ MATCH_MP_TAC lisp_inv_swap2
  \\ MATCH_MP_TAC lisp_inv_nil_lemma \\ Q.LIST_EXISTS_TAC [`x1`,`w1`]
  \\ MATCH_MP_TAC lisp_inv_swap1
  \\ MATCH_MP_TAC lisp_inv_nil_lemma \\ Q.LIST_EXISTS_TAC [`Sym a`,`w0`]
  \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_print_sym_full_thm",mc_print_sym_full_thm);


(* print " " *)

val (mc_print_sp_spec,mc_print_sp_def) = basic_decompile_strings x64_tools "mc_print_sp"
  (SOME (``(ior:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r0:word64,r1:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       mov r1,[r7-192]
       mov r0,[r7-216]
       mov BYTE [r0], 32
       mov BYTE [r0+1], 0
       insert io_write
       mov r0d,3
       mov r1d,1 `);

val _ = save_thm("mc_print_sp_spec",mc_print_sp_spec);

val mc_print_sp_thm = store_thm("mc_print_sp_thm",
  ``^LISP ==>
    ?g2. mc_print_sp_pre (EL 0 cs,sp,df,f,dg,g,io) /\
         (mc_print_sp (EL 0 cs,sp,df,f,dg,g,io) =
           (EL 0 cs,tw0,tw1,sp,df,f,dg,g2,IO_WRITE io " ")) /\
         let (g,io) = (g2,IO_WRITE io " ") in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,mc_print_sp_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`2`,`[32w;0w]`] lisp_inv_temp_string))
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.ABBREV_TAC `g3 = (sa2 + 0x1w =+ 0x0w) ((sa2 =+ 32w) g)`
  \\ IMP_RES_TAC LENGTH_EXPAND
  \\ `(one_byte_list sa2 [32w; 0x0w] * p) (fun2set (g3,dg)) /\
      sa2 IN dg /\ sa2+1w IN dg` by ALL_TAC THEN1
     (Q.UNABBREV_TAC `g3`
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,SEP_CLAUSES,STAR_ASSOC]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ `null_term_str sa2 dg g3 " "` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [null_term_str_def,one_string_def,MAP,APPEND,
      ORD_CHR_RWT,EVERY_DEF,CHR_11] \\ METIS_TAC [])
  \\ IMP_RES_TAC null_term_str_IMP
  \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [lisp_inv_ignore_io]);


(* print "'" *)

val (mc_print_qt_spec,mc_print_qt_def) = basic_decompile_strings x64_tools "mc_print_qt"
  (SOME (``(ior:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r0:word64,r1:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       mov r1,[r7-192]
       mov r0,[r7-216]
       mov BYTE [r0], 39
       mov BYTE [r0+1], 0
       insert io_write
       mov r0d,3
       mov r1d,1 `);

val _ = save_thm("mc_print_qt_spec",mc_print_qt_spec);

val mc_print_qt_thm = store_thm("mc_print_qt_thm",
  ``^LISP ==>
    ?g2. mc_print_qt_pre (EL 0 cs,sp,df,f,dg,g,io) /\
         (mc_print_qt (EL 0 cs,sp,df,f,dg,g,io) =
           (EL 0 cs,tw0,tw1,sp,df,f,dg,g2,IO_WRITE io "'")) /\
         let (g,io) = (g2,IO_WRITE io "'") in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,mc_print_qt_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`2`,`[39w;0w]`] lisp_inv_temp_string))
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.ABBREV_TAC `g3 = (sa2 + 0x1w =+ 0x0w) ((sa2 =+ 39w) g)`
  \\ IMP_RES_TAC LENGTH_EXPAND
  \\ `(one_byte_list sa2 [39w; 0x0w] * p) (fun2set (g3,dg)) /\
      sa2 IN dg /\ sa2+1w IN dg` by ALL_TAC THEN1
     (Q.UNABBREV_TAC `g3`
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,SEP_CLAUSES,STAR_ASSOC]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ `null_term_str sa2 dg g3 "'"` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [null_term_str_def,one_string_def,MAP,APPEND,
      ORD_CHR_RWT,EVERY_DEF,CHR_11] \\ METIS_TAC [])
  \\ IMP_RES_TAC null_term_str_IMP
  \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [lisp_inv_ignore_io]);


(* print "(" *)

val (mc_print_open_spec,mc_print_open_def) = basic_decompile_strings x64_tools "mc_print_open"
  (SOME (``(ior:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r0:word64,r1:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       mov r1,[r7-192]
       mov r0,[r7-216]
       mov BYTE [r0], 40
       mov BYTE [r0+1], 0
       insert io_write
       mov r0d,3
       mov r1d,1 `);

val _ = save_thm("mc_print_open_spec",mc_print_open_spec);

val mc_print_open_thm = store_thm("mc_print_open_thm",
  ``^LISP ==>
    ?g2. mc_print_open_pre (EL 0 cs,sp,df,f,dg,g,io) /\
         (mc_print_open (EL 0 cs,sp,df,f,dg,g,io) =
           (EL 0 cs,tw0,tw1,sp,df,f,dg,g2,IO_WRITE io "(")) /\
         let (g,io) = (g2,IO_WRITE io "(") in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,mc_print_open_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`2`,`[40w;0w]`] lisp_inv_temp_string))
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.ABBREV_TAC `g3 = (sa2 + 0x1w =+ 0x0w) ((sa2 =+ 40w) g)`
  \\ IMP_RES_TAC LENGTH_EXPAND
  \\ `(one_byte_list sa2 [40w; 0x0w] * p) (fun2set (g3,dg)) /\
      sa2 IN dg /\ sa2+1w IN dg` by ALL_TAC THEN1
     (Q.UNABBREV_TAC `g3`
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,SEP_CLAUSES,STAR_ASSOC]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ `null_term_str sa2 dg g3 "("` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [null_term_str_def,one_string_def,MAP,APPEND,
      ORD_CHR_RWT,EVERY_DEF,CHR_11] \\ METIS_TAC [])
  \\ IMP_RES_TAC null_term_str_IMP
  \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [lisp_inv_ignore_io]);


(* print ")" *)

val (mc_print_close_spec,mc_print_close_def) = basic_decompile_strings x64_tools "mc_print_close"
  (SOME (``(ior:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r0:word64,r1:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       mov r1,[r7-192]
       mov r0,[r7-216]
       mov BYTE [r0], 41
       mov BYTE [r0+1], 0
       insert io_write
       mov r0d,3
       mov r1d,1 `);

val _ = save_thm("mc_print_close_spec",mc_print_close_spec);

val mc_print_close_thm = store_thm("mc_print_close_thm",
  ``^LISP ==>
    ?g2. mc_print_close_pre (EL 0 cs,sp,df,f,dg,g,io) /\
         (mc_print_close (EL 0 cs,sp,df,f,dg,g,io) =
           (EL 0 cs,tw0,tw1,sp,df,f,dg,g2,IO_WRITE io ")")) /\
         let (g,io) = (g2,IO_WRITE io ")") in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,mc_print_close_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`2`,`[41w;0w]`] lisp_inv_temp_string))
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.ABBREV_TAC `g3 = (sa2 + 0x1w =+ 0x0w) ((sa2 =+ 41w) g)`
  \\ IMP_RES_TAC LENGTH_EXPAND
  \\ `(one_byte_list sa2 [41w; 0x0w] * p) (fun2set (g3,dg)) /\
      sa2 IN dg /\ sa2+1w IN dg` by ALL_TAC THEN1
     (Q.UNABBREV_TAC `g3`
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,SEP_CLAUSES,STAR_ASSOC]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ `null_term_str sa2 dg g3 ")"` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [null_term_str_def,one_string_def,MAP,APPEND,
      ORD_CHR_RWT,EVERY_DEF,CHR_11] \\ METIS_TAC [])
  \\ IMP_RES_TAC null_term_str_IMP
  \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [lisp_inv_ignore_io]);


(* print " . " *)

val (mc_print_dot_spec,mc_print_dot_def) = basic_decompile_strings x64_tools "mc_print_dot"
  (SOME (``(ior:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``,
         ``(ior:word64,r0:word64,r1:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8,io:io_streams)``))
  (assemble "x64" `
       mov r1,[r7-192]
       mov r0,[r7-216]
       mov BYTE [r0], 32
       mov BYTE [r0+1], 46
       mov BYTE [r0+2], 32
       mov BYTE [r0+3], 0
       insert io_write
       mov r0d,3
       mov r1d,1 `);

val _ = save_thm("mc_print_dot_spec",mc_print_dot_spec);

val mc_print_dot_thm = store_thm("mc_print_dot_thm",
  ``^LISP ==>
    ?g2. mc_print_dot_pre (EL 0 cs,sp,df,f,dg,g,io) /\
         (mc_print_dot (EL 0 cs,sp,df,f,dg,g,io) =
           (EL 0 cs,tw0,tw1,sp,df,f,dg,g2,IO_WRITE io " . ")) /\
         let (g,io) = (g2,IO_WRITE io " . ") in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,mc_print_dot_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`4`,`[32w;46w;32w;0w]`] lisp_inv_temp_string))
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.ABBREV_TAC `g3 = (sa2+3w =+ 0x0w) ((sa2+2w =+ 32w) ((sa2+1w =+ 46w) ((sa2 =+ 32w) g)))`
  \\ IMP_RES_TAC LENGTH_EXPAND
  \\ `(one_byte_list sa2 [32w; 46w; 32w; 0x0w] * p) (fun2set (g3,dg)) /\
      sa2 IN dg /\ sa2+1w IN dg /\ sa2+2w IN dg /\ sa2+3w IN dg` by ALL_TAC THEN1
     (Q.UNABBREV_TAC `g3`
      \\ FULL_SIMP_TAC std_ss [one_byte_list_def,SEP_CLAUSES,STAR_ASSOC]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ `null_term_str sa2 dg g3 " . "` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [null_term_str_def,one_string_def,MAP,APPEND,
      ORD_CHR_RWT,EVERY_DEF,CHR_11] \\ METIS_TAC [])
  \\ IMP_RES_TAC null_term_str_IMP
  \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [lisp_inv_ignore_io]);


(* call stats function 1 *)

val (mc_print_stats1_spec,mc_print_stats1_def) = basic_decompile_strings x64_tools "mc_print_stats1"
  (SOME (``(iod:word64,r0:word64,r6:word64,r7:word64,r8:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32,io:io_streams)``,
         ``(iod:word64,r0:word64,r1:word64,r2:word64,r6:word64,r7:word64,r8:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32,io:io_streams)``))
  (assemble "x64" `
       mov r1,[r7-176]
       xchg rdi,r0
       xchg rsi,r14
       mov rdx,r15
       shr rdx,1
       shr rsi,1
       mov edi, 1
       insert io_stats
       shl rsi,1
       xchg rsi,r14
       mov rdi,r0
       mov r1d,1
       mov r0d,3 `);

val _ = save_thm("mc_print_stats1_spec",mc_print_stats1_spec);

val mc_print_stats1_thm = store_thm("mc_print_stats1_thm",
  ``^LISP ==>
    ?g2. mc_print_stats1_pre (EL 2 cs,tw0,bp,sp,w2w w0,wi,we,df,f,io) /\
         (mc_print_stats1 (EL 2 cs,tw0,bp,sp,w2w w0,wi,we,df,f,io) =
           (EL 2 cs,tw0,tw1,we >>> 1,bp,sp,w2w w0,wi,we,df,f,IO_STATS 1 io)) /\
         let (io,tw2) = (IO_STATS 1 io,we >>> 1) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,mc_print_stats1_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3] \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 (METIS_TAC [lisp_inv_ignore_io,lisp_inv_ignore_tw2])
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,GSYM word_mul_n2w]
  \\ Q.SPEC_TAC (`(n2w i):word64`,`w`) \\ blastLib.BBLAST_TAC);


(* call stats function 2 *)

val (mc_print_stats2_spec,mc_print_stats2_def) = basic_decompile_strings x64_tools "mc_print_stats2"
  (SOME (``(iod:word64,r0:word64,r6:word64,r7:word64,r8:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32,io:io_streams)``,
         ``(iod:word64,r0:word64,r1:word64,r2:word64,r6:word64,r7:word64,r8:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32,io:io_streams)``))
  (assemble "x64" `
       mov r1,[r7-176]
       xchg rdi,r0
       xchg rsi,r14
       mov rdx,r15
       shr rdx,1
       shr rsi,1
       mov edi, 2
       insert io_stats
       shl rsi,1
       xchg rsi,r14
       mov rdi,r0
       mov r1d,1
       mov r0d,3 `);

val _ = save_thm("mc_print_stats2_spec",mc_print_stats2_spec);

val mc_print_stats2_thm = store_thm("mc_print_stats2_thm",
  ``^LISP ==>
    ?g2. mc_print_stats2_pre (EL 2 cs,tw0,bp,sp,w2w w0,wi,we,df,f,io) /\
         (mc_print_stats2 (EL 2 cs,tw0,bp,sp,w2w w0,wi,we,df,f,io) =
           (EL 2 cs,tw0,tw1,we >>> 1,bp,sp,w2w w0,wi,we,df,f,IO_STATS 2 io)) /\
         let (io,tw2) = (IO_STATS 2 io,we >>> 1) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,mc_print_stats2_def] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3] \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 (METIS_TAC [lisp_inv_ignore_io,lisp_inv_ignore_tw2])
  \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,GSYM word_mul_n2w]
  \\ Q.SPEC_TAC (`(n2w i):word64`,`w`) \\ blastLib.BBLAST_TAC);


(* is_quote *)

val (thm,mc_is_quote_def) = basic_decompile_strings x64_tools "mc_is_quote"
  (SOME (``(r0:word64,r6:word64,df:word64 set,f:word64->word32)``,
         ``(r1:word64,r6:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       test r0,1
       jne FALSE
       mov r1d,[r6+4*r0]
       mov r0d,[r6+4*r0+4]
       cmp r1,19
       jne FALSE
       test r0,1
       jne FALSE
       mov r1d,[r6+4*r0+4]
       cmp r1,3
       jne FALSE
TRUE:  mov r1d,1
       jmp EXIT
FALSE: xor r1,r1
EXIT:`)

val mc_is_quote_blast = blastLib.BBLAST_PROVE
  ``((31 -- 0) (w2w (w:word32)):word64 = w2w w) /\
    ((w2w w && 0x1w = 0x0w:word64) = (w && 0x1w = 0x0w))``

val mc_is_quote_thm = prove(
  ``^LISP ==>
    mc_is_quote_pre (w2w w0,bp,df,f) /\
    (mc_is_quote (w2w w0,bp,df,f) = (if isQuote x0 then 1w else 0w,bp,df,f))``,
  SIMP_TAC std_ss [isQuote_def,mc_is_quote_def,LET_DEF,mc_is_quote_blast]
  \\ STRIP_TAC \\ IMP_RES_TAC lisp_inv_type \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `isDot x0` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC lisp_inv_car
  \\ IMP_RES_TAC (el 3 (CONJUNCTS lisp_inv_Sym))
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
  \\ Cases_on `CAR x0 = Sym "QUOTE"`  \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC lisp_inv_cdr
  \\ IMP_RES_TAC lisp_inv_type \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
  \\ Cases_on `isDot (CDR x0)`  \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC lisp_inv_cdr
  \\ IMP_RES_TAC (el 1 (CONJUNCTS lisp_inv_Sym))
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
  \\ Cases_on `CDR (CDR x0) = Sym "NIL"`  \\ ASM_SIMP_TAC std_ss []);

val (mc_is_quote_full_spec,mc_is_quote_full_def) = basic_decompile_strings x64_tools "mc_is_quote_full"
  (SOME (``(r8:word64,r6:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r1:word64,r8:word64,r6:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
      mov r0,r8
      insert mc_is_quote
      mov r0d,3
      mov r8d,11
      test r1,r1
      cmove r8,r0
      mov r1d,1
   `)

val _ = save_thm("mc_is_quote_full_spec",mc_is_quote_full_spec);

val mc_is_quote_full_thm = prove(
  ``^LISP ==>
    ?v0. mc_is_quote_full_pre (w2w w0,bp,df,f) /\
         (mc_is_quote_full (w2w w0,bp,df,f) = (tw0,tw1,w2w v0,bp,df,f)) /\
         let (w0,x0) = (v0,LISP_TEST (isQuote x0)) in ^LISP``,
  FULL_SIMP_TAC std_ss [mc_is_quote_full_def,LET_DEF] \\ STRIP_TAC
  \\ IMP_RES_TAC mc_is_quote_thm \\ ASM_SIMP_TAC std_ss []
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ Cases_on `isQuote x0` \\ FULL_SIMP_TAC wstd_ss [n2w_11,LISP_TEST_def]
  THEN1 (Q.EXISTS_TAC `0xBw` \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
    \\ IMP_RES_TAC (el 2 (CONJUNCTS lisp_inv_Sym)))
  THEN1 (Q.EXISTS_TAC `0x3w` \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
    \\ IMP_RES_TAC (el 1 (CONJUNCTS lisp_inv_Sym)))) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_is_quote_full_thm",mc_is_quote_full_thm);


(* lookup constant *)

val (mc_const_load_spec,mc_const_load_def) = basic_decompile_strings x64_tools "mc_const_load"
  (SOME (``(r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r2,[r7-64]
       mov r8d,[r2+r8]
   `)

val PULL_EXISTS_OVER_CONJ = METIS_PROVE []
  ``((?x. P x) /\ Q = ?x. P x /\ Q) /\ (Q /\ (?x. P x) = ?x. P x /\ Q)``

val ref_heap_addr_alt = store_thm("ref_heap_addr_alt",
  ``(ref_heap_addr (H_ADDR a) = n2w a << 1) /\
    (ref_heap_addr (H_DATA (INL w)) = w2w w << 2 + 0x1w) /\
    (ref_heap_addr (H_DATA (INR v)) = w2w v << 3 + 0x3w)``,
  SIMP_TAC std_ss [ref_heap_addr_def] \\ blastLib.BBLAST_TAC);

val mc_const_load_blast = prove(
  ``w2w ((0x1w:word32) + w2w w << 2) = (0x1w:word64) + w2w (w:word30) << 2``,
  blastLib.BBLAST_TAC);

val mc_const_load_thm = prove(
  ``^LISP ==> getVal x0 < LENGTH xs1 /\ isVal x0 ==>
    ?w0i tw2i.
      mc_const_load_pre (tw2,sp,w2w w0,df,f) /\
      (mc_const_load (tw2,sp,w2w w0,df,f) = (tw2i,sp,w2w w0i,df,f)) /\
      let (x0,tw2,w0) = (EL (getVal x0) xs1, tw2i, w0i) in ^LISP``,
  FULL_SIMP_TAC std_ss [LET_DEF,mc_const_load_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,gc_w2w_lemma]
  \\ `sp && 0x3w = 0x0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,isVal_thm,getVal_def]
  \\ Q.EXISTS_TAC `f (w2w w0 + EL 6 ds)` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `lisp_inv xxx yyy zzz` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,PULL_EXISTS_OVER_CONJ,EVERY_DEF,lisp_x_def]
  \\ Q.LIST_EXISTS_TAC [`EL a ss1`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF,LENGTH,ADD1,ZIP,EVERY_DEF,getVal_def]
  \\ `?ss3 s ss4. (ss1 = ss3 ++ s::ss4) /\ (LENGTH ss3 = a)` by METIS_TAC [SPLIT_LIST,APPEND_ASSOC,APPEND]
  \\ `?xs3 x xs4. (xs1 = xs3 ++ x::xs4) /\ (LENGTH xs3 = a)` by METIS_TAC [SPLIT_LIST,APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [ZIP_APPEND,ZIP,EVERY_DEF,EVERY_APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [ZIP,APPEND,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,LENGTH_APPEND,LENGTH,EL,HD]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n] \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_ASSUM `EVERY xx yy` MP_TAC
  \\ FULL_SIMP_TAC std_ss [ZIP_APPEND,EVERY_APPEND,ZIP,EVERY_DEF] \\ STRIP_TAC
  \\ Q.PAT_ASSUM `ref_heap_addr (H_DATA (INL (n2w a))) = w0` (MP_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [RW1 [WORD_ADD_COMM] ref_heap_addr_alt,mc_const_load_blast]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC,WORD_SUB_ADD] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [ref_stack_def,Once ref_stack_APPEND,APPEND]
  \\ Cases_on `wsp`
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_mul_n2w,word_arith_lemma1,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL,word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [GSYM LEFT_ADD_DISTRIB,LENGTH_APPEND,word_arith_lemma1]
  \\ Q.PAT_ASSUM `LENGTH ss + n = sl` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC] \\ SEP_R_TAC
  \\ ASM_SIMP_TAC std_ss [align_add_blast,n2w_and_3,RW1[MULT_COMM]MOD_EQ_0])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_const_load_spec",mc_const_load_spec);
val _ = save_thm("mc_const_load_thm",mc_const_load_thm);


(* store new constant *)

val (mc_const_store_spec,mc_const_store_def) = basic_decompile_strings x64_tools "mc_const_store"
  (SOME (``(r0:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r0,[r7-48]
       mov r2,[r7-64]
       shl r0,2
       inc r2
       dec QWORD [r7-56]
       inc QWORD [r7-48]
       mov [r0+r2],r8d
       xor r8,r8
       not r8
       mov [r0+r2+4],r8d
       inc r0
       mov r8d,r0
       mov r0d,3
   `)

val EL_UPDATE_NTH = store_thm("EL_UPDATE_NTH",
  ``!xs n k x. EL n (UPDATE_NTH k x xs) =
               if (k = n) /\ k < LENGTH xs then x else EL n xs``,
  Induct \\ Cases_on `k` \\ SIMP_TAC std_ss [LENGTH,UPDATE_NTH_def]
  THEN1 (Cases_on `n` \\ FULL_SIMP_TAC std_ss [EL,HD,TL] \\ FULL_SIMP_TAC std_ss [ADD1])
  \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [EL,HD,TL]
  \\ FULL_SIMP_TAC std_ss [ADD1]);

val mc_const_store_blast = blastLib.BBLAST_PROVE
  ``(31 -- 0) (w:word64) = w2w ((w2w w):word32)``

val mc_const_store_thm = prove(
  ``~(EL 7 ds = 0w) /\ ^LISP ==>
    ?w0i tw2i fi.
      mc_const_store_pre (tw0,tw2,sp,w2w w0,df,f) /\
      (mc_const_store (tw0,tw2,sp,w2w w0,df,f) = (tw0,tw2i,sp,w2w w0i,df,fi)) /\
      let (x0,xs1,tw2,w0,f,ds) = (Val (LENGTH xs1), xs1 ++ [x0],
             tw2i, w0i, fi, UPDATE_NTH 7 (EL 7 ds - 1w) (UPDATE_NTH 8 (EL 8 ds + 1w) ds)) in ^LISP``,
  FULL_SIMP_TAC std_ss [LET_DEF,mc_const_store_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,gc_w2w_lemma]
  \\ `sp && 0x3w = 0x0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,isVal_thm,getVal_def]
  \\ Q.EXISTS_TAC `w2w (EL 8 ds) << 2 + 0x1w` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `lisp_inv xxx yyy zzz` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,PULL_EXISTS_OVER_CONJ,EVERY_DEF,lisp_x_def]
  \\ Q.LIST_EXISTS_TAC [`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1 ++ [s0]`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [LENGTH_UPDATE_NTH,EL_UPDATE_NTH]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,LENGTH_APPEND,WORD_SUB_ADD,LENGTH]
  \\ FULL_SIMP_TAC std_ss [n2w_11,MAP,CONS_11,ref_heap_addr_alt,word_arith_lemma2]
  \\ `(sl1 - LENGTH ss1) < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ `~(sl1 < LENGTH ss1 + 1) /\ LENGTH ss1 + 1 <= sl1` by DECIDE_TAC
  \\ Q.PAT_ASSUM `LENGTH xs = LENGTH ss` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [SUB_PLUS,ZIP_APPEND,EVERY_APPEND,EVERY_DEF,ZIP]
  \\ `sp + n2w (4 * sl) - 0x1w + n2w (LENGTH ss1) << 2 + 0x1w =
      sp + n2w (4 * sl) + n2w (LENGTH ss1) << 2` by WORD_DECIDE_TAC
  \\ `LENGTH ss1 < 1073741824 /\ LENGTH ss1 < 18446744073709551616` by DECIDE_TAC
  \\ `(4 * LENGTH ss1 + 1) < 18446744073709551616` by DECIDE_TAC
  \\ `0xFFFFFFFFFFFFFFFFw = 0xFFFFFFFFw:word32` by EVAL_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,GSYM LEFT_ADD_DISTRIB,
       align_add_blast,n2w_and_3,RW1[MULT_COMM]MOD_EQ_0,GSYM CONJ_ASSOC,
       EVAL ``w2n (~0x0w:word64)``,WORD_MUL_LSL,word_mul_n2w,word_arith_lemma1,
       mc_const_store_blast] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n] \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_ASSUM `LENGTH cs = 10` MP_TAC
  \\ IMP_RES_TAC expand_list
  \\ FULL_SIMP_TAC std_ss [UPDATE_NTH_CONS,
       GSYM (SIMP_RULE std_ss [word_mul_n2w] (Q.SPECL [`n2w a`,`32`] WORD_MUL_LSL))]
  \\ `(sl1 - LENGTH ss1 - 1) < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM w2w_def]
  \\ Q.PAT_ASSUM `xxx (fun2set (f,df))` MP_TAC
  \\ FULL_SIMP_TAC std_ss [EL_CONS] \\ NTAC 2 STRIP_TAC
  \\ Q.ABBREV_TAC `aa = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex]`
  \\ `LENGTH aa = 8` by (Q.UNABBREV_TAC `aa` \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,ref_static_APPEND,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,ref_static_def,LET_DEF,word64_3232_def,STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ Q.ABBREV_TAC `ss2 = ss ++ ss1`
  \\ SIMP_TAC std_ss [ref_stack_APPEND,ref_stack_def,STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [RW [APPEND_NIL,ref_stack_def] (Q.SPECL [`xs`,`[]`] ref_stack_APPEND)]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss)
      [APPLY_UPDATE_THM,RW [GSYM word_sub_def] (Q.SPECL [`w`,`-x`,`-y`] WORD_EQ_ADD_LCANCEL),
       WORD_EQ_NEG,n2w_11,word_add_n2w]
  \\ Cases_on `sl1 - LENGTH ss1` THEN1 (`F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `sp + 0x4w * wsp + n2w (4 * LENGTH ss2) =
      sp + n2w (4 * (sl + LENGTH ss1))` by ALL_TAC THEN1
   (Cases_on `wsp` \\ FULL_SIMP_TAC std_ss [word_mul_n2w,w2n_n2w]
    \\ Q.UNABBREV_TAC `ss2`
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,LENGTH_APPEND,GSYM LEFT_ADD_DISTRIB]
    \\ NTAC 3 AP_TERM_TAC \\ DECIDE_TAC)
  \\ Q.UNABBREV_TAC `ss2`
  \\ FULL_SIMP_TAC std_ss [ref_stack_space_above_def,STAR_ASSOC,
       SEP_CLAUSES,LEFT_ADD_DISTRIB,SEP_EXISTS_THM,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
  \\ REVERSE STRIP_TAC THEN1 SEP_READ_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD_ASSOC,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ SEP_W_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ `n < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_const_store_spec",mc_const_store_spec);
val _ = save_thm("mc_const_store_thm",mc_const_store_thm);


(* xbp set *)

val (mc_xbp_set_spec,mc_xbp_set_def) = basic_decompile_strings x64_tools "mc_xbp_set"
  (SOME (``(r2:word64,r3:word64,r7:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r3:word64,r7:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       lea r2,[4*r3+r7-1]
       mov [r7-104],r2
   `)

val UPDATE_NTH_1 = prove(``UPDATE_NTH 1 x (y1::y2::ys) = y1::x::ys``, EVAL_TAC);

val mc_xbp_set_thm = prove(
  ``^LISP ==>
    ?tw2i fi.
      mc_xbp_set_pre (tw2,wsp,sp,df,f) /\
      (mc_xbp_set (tw2,wsp,sp,df,f) = (tw2i,wsp,sp,df,fi)) /\
      let (xbp,tw2,ds,f) = (LENGTH xs, tw2i, UPDATE_NTH 1 (sp + 4w * wsp - 1w) ds, fi) in ^LISP``,
  SIMP_TAC std_ss [mc_xbp_set_def,LET_DEF,INSERT_SUBSET,EMPTY_SUBSET] \\ STRIP_TAC
  \\ `(sp - 0x64w IN df /\ sp - 0x68w IN df)` by ALL_TAC THEN1
      (IMP_RES_TAC lisp_inv_ds_read \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [LET_DEF,lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [LENGTH_UPDATE_NTH,EL_UPDATE_NTH]
  \\ Q.PAT_ASSUM `xxx = sl` (ASSUME_TAC o GSYM o RW1[ADD_COMM])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w,
      WORD_ADD_ASSOC,WORD_ADD_SUB,WORD_EQ_ADD_LCANCEL,WORD_EQ_ADD_RCANCEL]
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,n2w_w2n])
  \\ Cases_on `ds` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ Q.PAT_ASSUM `xxx (fun2set (f,df))` MP_TAC
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,ref_static_APPEND,LENGTH,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,UPDATE_NTH_1]
  \\ Q.ABBREV_TAC `xssss = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex]`
  \\ FULL_SIMP_TAC std_ss [ref_static_def,word64_3232_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma2,word_arith_lemma1,
       STAR_ASSOC,gc_w2w_lemma]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ REPEAT STRIP_TAC \\ SEP_WRITE_TAC) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_xbp_set_spec",mc_xbp_set_spec);
val _ = save_thm("mc_xbp_set_thm",mc_xbp_set_thm);


(* load based on xbp *)

val (mc_xbp_load_spec,mc_xbp_load_def) = basic_decompile_strings x64_tools "mc_xbp_load"
  (SOME (``(r2:word64,r7:word64,r9:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r7:word64,r9:word64,r12:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r2,[r7-104]
       mov r12d,[r2+r9]
   `)

val BLAST_LEMMA = prove(``w << 2 !! 1w = w << 2 + 1w:word32``,blastLib.BBLAST_TAC);

val EL_UPDATE_NTH = store_thm("EL_UPDATE_NTH",
  ``!xs n k x. EL n (UPDATE_NTH k x xs) =
               if (k = n) /\ k < LENGTH xs then x else EL n xs``,
  Induct \\ Cases_on `k` \\ SIMP_TAC std_ss [LENGTH,UPDATE_NTH_def]
  THEN1 (Cases_on `n` \\ FULL_SIMP_TAC std_ss [EL,HD,TL] \\ FULL_SIMP_TAC std_ss [ADD1])
  \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [EL,HD,TL]
  \\ FULL_SIMP_TAC std_ss [ADD1]);

val UPDATE_NTH_1 = prove(``UPDATE_NTH 1 x (y1::y2::ys) = y1::x::ys``, EVAL_TAC);

val mc_xbp_load_blast = blastLib.BBLAST_PROVE
  ``((31 -- 0) (w2w w1) = (w2w w2):word64) = (w1 = w2:word32)``

val mc_xbp_load_thm = prove(
  ``^LISP ==> isVal x1 /\ getVal x1 < xbp /\ xbp <= LENGTH xs ==>
    ?tw2i w4i.
      mc_xbp_load_pre (tw2,sp,w2w w1,df,f) /\
      (mc_xbp_load (tw2,sp,w2w w1,df,f) = (tw2i,sp,w2w w1,w2w w4i,df,f)) /\
      let (x4,tw2,w4) = (EL ((LENGTH xs + getVal x1) - xbp) xs,tw2i,w4i) in ^LISP``,
  Cases_on `isVal x1` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def] \\ STRIP_TAC
  \\ SIMP_TAC std_ss [mc_xbp_load_def,LET_DEF,INSERT_SUBSET,EMPTY_SUBSET]
  \\ IMP_RES_TAC lisp_inv_ds_read \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `lisp_inv xxx yyy zzz` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ NTAC 2 STRIP_TAC \\ FULL_SIMP_TAC std_ss [mc_xbp_load_blast]
  \\ Q.ABBREV_TAC `n = LENGTH xs + a - xbp`
  \\ `EL 1 ds + w2w w1 = sp + 0x4w * wsp + 0x4w * n2w n` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [lisp_inv_def,MAP,CONS_11,EVERY_DEF,lisp_x_def]
    \\ Q.PAT_ASSUM `ref_heap_addr s1 = w1` (MP_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,BLAST_LEMMA]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL]
    \\ `(4 * a + 1) < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_ADD,WORD_ADD_ASSOC]
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma3]
    \\ Q.PAT_ASSUM `LENGTH ss + w2n wsp = sl` (MP_TAC o GSYM)
    \\ ASM_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`wsp`,`w`)
    \\ Cases \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,word_mul_n2w,w2n_n2w]
    \\ `~(4 * (LENGTH ss + n') < 4 * xbp - 4 * a)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,word_arith_lemma4]
    \\ REPEAT STRIP_TAC \\ AP_TERM_TAC \\ Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ `n < LENGTH xs` by ALL_TAC THEN1 (Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ IMP_RES_TAC lisp_inv_swap4
  \\ IMP_RES_TAC (RW[AND_IMP_INTRO]lisp_inv_load_lemma)
  \\ ASM_SIMP_TAC std_ss []
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ MATCH_MP_TAC lisp_inv_swap4
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `tw2` \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_xbp_load_spec",mc_xbp_load_spec);
val _ = save_thm("mc_xbp_load_thm",mc_xbp_load_thm);


(* load amnt *)

val (mc_load_amnt_spec,mc_load_amnt_def) = basic_decompile_strings x64_tools "mc_load_amnt"
  (SOME (``(r7:word64,df:word64 set,f:word64->word32)``,
         ``(r7:word64,r9:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r9d,[r7-40]
       shl r9d,2
       inc r9d
   `)

val mc_load_amnt_thm = prove(
  ``^LISP ==>
    ?w1i.
      mc_load_amnt_pre (sp,df,f) /\
      (mc_load_amnt (sp,df,f) = (sp,w2w w1i,df,f)) /\
      let (x1,w1) = (Val amnt,w1i) in ^LISP``,
  FULL_SIMP_TAC std_ss [mc_load_amnt_def,LET_DEF,mc_xbp_load_blast] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_swap1
  \\ IMP_RES_TAC lisp_inv_amnt_read
  \\ Q.EXISTS_TAC `w2w ((w2w (f (sp - 0x24w)) << 32 !! (w2w:word32->word64) (f (sp - 0x28w))) << 2 + 0x1w)`
  \\ IMP_RES_TAC lisp_inv_swap1
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL]
  \\ Q.SPEC_TAC (`f (sp - 0x24w)`,`w`)
  \\ Q.SPEC_TAC (`f (sp - 0x28w)`,`w1`)
  \\ blastLib.BBLAST_TAC);

val _ = save_thm("mc_load_amnt_spec",mc_load_amnt_spec);
val _ = save_thm("mc_load_amnt_thm",mc_load_amnt_thm);


(* pops by x1 *)

val (mc_pops_by_var_spec,mc_pops_by_var_def) = basic_decompile_strings x64_tools "mc_pops_by_var"
  (SOME (``(r2:word64,r3:word64,r9:word64)``,
         ``(r2:word64,r3:word64,r9:word64)``))
  (assemble "x64" `
       mov r2,r9
       shr r2,2
       add r3,r2
   `)

val mc_pops_by_var_thm = prove(
  ``^LISP ==> isVal x1 /\ getVal x1 <= LENGTH xs ==>
    ?tw2i wspi.
      mc_pops_by_var_pre (tw2,wsp,w2w w1) /\
      (mc_pops_by_var (tw2,wsp,w2w w1) = (tw2i,wspi,w2w w1)) /\
      let (xs,wsp,tw2) = (DROP (getVal x1) xs,wspi,tw2i) in ^LISP``,
  Cases_on `isVal x1` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def,LET_DEF,mc_pops_by_var_def]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `tw2` \\ ASM_SIMP_TAC std_ss []
  \\ SUBGOAL `wsp + w2w w1 >>> 2 = wsp + n2w a` THEN1
   (ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC(RW[AND_IMP_INTRO]lisp_inv_pops_lemma)
    \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,MAP,CONS_11,EVERY_DEF,lisp_x_def]
  \\ Q.PAT_ASSUM `xxx = w1` (MP_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def]
  \\ SUBGOAL `n2w a = (w2w:word30->word64) (n2w a)` THEN1
   (FULL_SIMP_TAC std_ss []
    \\ Q.SPEC_TAC (`(n2w a):word30`,`w`) \\ blastLib.BBLAST_TAC)
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]);

val _ = save_thm("mc_pops_by_var_spec",mc_pops_by_var_spec);
val _ = save_thm("mc_pops_by_var_thm",mc_pops_by_var_thm);


(* store based on xbp *)

val (mc_xbp_store_spec,mc_xbp_store_def) = basic_decompile_strings x64_tools "mc_xbp_store"
  (SOME (``(r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r2,[r7-104]
       mov [r2+r9],r8d
   `)

val mc_xbp_store_blast = blastLib.BBLAST_PROVE
  ``w2w ((w2w w):word64) = (w:word32)``

val mc_xbp_store_thm = prove(
  ``^LISP ==> isVal x1 /\ getVal x1 < xbp /\ xbp <= LENGTH xs ==>
    ?tw2i fi.
      mc_xbp_store_pre (tw2,sp,w2w w0,w2w w1,df,f) /\
      (mc_xbp_store (tw2,sp,w2w w0,w2w w1,df,f) = (tw2i,sp,w2w w0,w2w w1,df,fi)) /\
      let (xs,tw2,f) = (UPDATE_NTH ((LENGTH xs + getVal x1) - xbp) x0 xs,tw2i,fi) in ^LISP``,
  Cases_on `isVal x1` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def] \\ STRIP_TAC
  \\ SIMP_TAC std_ss [mc_xbp_store_def,LET_DEF,INSERT_SUBSET,EMPTY_SUBSET]
  \\ IMP_RES_TAC lisp_inv_ds_read \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `lisp_inv xxx yyy zzz` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ NTAC 2 STRIP_TAC \\ FULL_SIMP_TAC std_ss [mc_xbp_load_blast]
  \\ Q.ABBREV_TAC `n = LENGTH xs + a - xbp`
  \\ `EL 1 ds + w2w w1 = sp + 0x4w * wsp + 0x4w * n2w n` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [lisp_inv_def,MAP,CONS_11,EVERY_DEF,lisp_x_def]
    \\ Q.PAT_ASSUM `ref_heap_addr s1 = w1` (MP_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,BLAST_LEMMA]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL]
    \\ `(4 * a + 1) < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_ADD,WORD_ADD_ASSOC]
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma3]
    \\ Q.PAT_ASSUM `LENGTH ss + w2n wsp = sl` (MP_TAC o GSYM)
    \\ ASM_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`wsp`,`w`)
    \\ Cases \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,word_mul_n2w,w2n_n2w]
    \\ `~(4 * (LENGTH ss + n') < 4 * xbp - 4 * a)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,word_arith_lemma4]
    \\ REPEAT STRIP_TAC \\ AP_TERM_TAC \\ Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ `n < LENGTH xs` by ALL_TAC THEN1 (Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ IMP_RES_TAC (RW[AND_IMP_INTRO]lisp_inv_store_lemma)
  \\ ASM_SIMP_TAC std_ss []
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,mc_xbp_store_blast]
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `tw2` \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_xbp_store_spec",mc_xbp_store_spec);
val _ = save_thm("mc_xbp_store_thm",mc_xbp_store_thm);


(* read code_ptr code *)

val (mc_read_snd_code_spec,mc_read_snd_code_def) = basic_decompile_strings x64_tools "mc_read_snd_code"
  (SOME (``(r7:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r7:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r8,[r7-96]
       sub r8,[r7-160]
       shl r8,2
       inc r8
   `)

val mc_read_snd_code_thm = prove(
  ``^LISP ==>
    ?v0.
      mc_read_snd_code_pre (sp,w2w w0,df,f) /\
      (mc_read_snd_code (sp,w2w w0,df,f) = (sp,w2w v0,df,f)) /\
      let (x0,w0) = (Val (code_ptr code),v0) in ^LISP``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_read_snd_code_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_cs_read \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ Q.EXISTS_TAC `n2w (4 * (code_ptr code) + 1)`
  \\ `code_ptr code < 1073741824` by ALL_TAC THEN1
      (FULL_SIMP_TAC std_ss [lisp_inv_def,code_heap_def] \\ DECIDE_TAC)
  \\ REVERSE STRIP_TAC
  THEN1 (MATCH_MP_TAC lisp_inv_Val_n2w \\ ASM_SIMP_TAC std_ss [])
  \\ `EL 2 ds - EL 4 cs = n2w (code_ptr code)` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [lisp_inv_def,code_heap_def]
     \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ SIMP_TAC std_ss [WORD_ADD_SUB])
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ `(4 * code_ptr code + 1) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_read_snd_code_spec",mc_read_snd_code_spec);
val _ = save_thm("mc_read_snd_code_thm",mc_read_snd_code_thm);


(* safe versions of car and cdr, i.e. total versions *)

val SAFE_CAR_def = Define `SAFE_CAR x = CAR x`;
val SAFE_CDR_def = Define `SAFE_CDR x = CDR x`;

val (mc_safe_car_spec,mc_safe_car_def) = basic_decompile_strings x64_tools "mc_safe_car"
  (SOME (``(r0:word64,r6:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r6:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       test r8,1
       cmovne r8,r0
       jne L
       mov r8d, [r6+4*r8]
L: `)

val (mc_safe_cdr_spec,mc_safe_cdr_def) = basic_decompile_strings x64_tools "mc_safe_cdr"
  (SOME (``(r0:word64,r6:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r6:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       test r8,1
       cmovne r8,r0
       jne L
       mov r8d, [r6+4*r8+4]
L: `)

val mc_safe_car_pre_def = CONJUNCT2 mc_safe_car_def
val mc_safe_cdr_pre_def = CONJUNCT2 mc_safe_cdr_def

val mc_safe_car_blast = blastLib.BBLAST_PROVE
  ``((w2w (w0:word32) && 0x1w = 0x0w:word64) = (w0 && 1w = 0w)) /\
    ((((31 -- 0) ((w2w w))) = (w2w (v:word32)):word64) = (w = v))``

val mc_safe_car_lemma = prove(
  ``^LISP ==>
    ?w0i.
      mc_safe_car_pre (tw0,bp,w2w w0,df,f) /\
      (mc_safe_car (tw0,bp,w2w w0,df,f) = (tw0,bp,w2w w0i,df,f)) /\
      let (x0,w0) = (SAFE_CAR x0,w0i) in ^LISP``,
  FULL_SIMP_TAC std_ss [SAFE_CAR_def,SAFE_CDR_def]
  \\ FULL_SIMP_TAC std_ss [mc_safe_car_def,mc_safe_cdr_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [mc_safe_car_blast] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_type \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `isDot x0` \\ ASM_SIMP_TAC std_ss [] THEN1
   (IMP_RES_TAC lisp_inv_car \\ IMP_RES_TAC lisp_inv_cdr
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,mc_safe_car_blast])
  \\ `(CAR x0 = Sym "NIL") /\ (CDR x0 = Sym "NIL")` by ALL_TAC THEN1
    (Cases_on `x0` \\ FULL_SIMP_TAC std_ss [isDot_def,CAR_def,CDR_def])
  \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `3w`
  \\ `tw0 = 3w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ IMP_RES_TAC lisp_inv_nil
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [LET_DEF];

val mc_safe_car_thm = prove(
  ``^LISP ==>
    (?w0i.
      mc_safe_car_pre (tw0,bp,w2w w0,df,f) /\
      (mc_safe_car (tw0,bp,w2w w0,df,f) = (tw0,bp,w2w w0i,df,f)) /\
      let (x0,w0) = (SAFE_CAR x0,w0i) in ^LISP) /\
    (?w1i.
      mc_safe_car_pre (tw0,bp,w2w w1,df,f) /\
      (mc_safe_car (tw0,bp,w2w w1,df,f) = (tw0,bp,w2w w1i,df,f)) /\
      let (x1,w1) = (SAFE_CAR x1,w1i) in ^LISP) /\
    (?w2i.
      mc_safe_car_pre (tw0,bp,w2w w2,df,f) /\
      (mc_safe_car (tw0,bp,w2w w2,df,f) = (tw0,bp,w2w w2i,df,f)) /\
      let (x2,w2) = (SAFE_CAR x2,w2i) in ^LISP) /\
    (?w3i.
      mc_safe_car_pre (tw0,bp,w2w w3,df,f) /\
      (mc_safe_car (tw0,bp,w2w w3,df,f) = (tw0,bp,w2w w3i,df,f)) /\
      let (x3,w3) = (SAFE_CAR x3,w3i) in ^LISP) /\
    (?w4i.
      mc_safe_car_pre (tw0,bp,w2w w4,df,f) /\
      (mc_safe_car (tw0,bp,w2w w4,df,f) = (tw0,bp,w2w w4i,df,f)) /\
      let (x4,w4) = (SAFE_CAR x4,w4i) in ^LISP) /\
    (?w5i.
      mc_safe_car_pre (tw0,bp,w2w w5,df,f) /\
      (mc_safe_car (tw0,bp,w2w w5,df,f) = (tw0,bp,w2w w5i,df,f)) /\
      let (x5,w5) = (SAFE_CAR x5,w5i) in ^LISP)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF]
  THEN1 (IMP_RES_TAC mc_safe_car_lemma \\ METIS_TAC [])
  THEN1 (IMP_RES_TAC lisp_inv_swap1 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap1])
  THEN1 (IMP_RES_TAC lisp_inv_swap2 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap2])
  THEN1 (IMP_RES_TAC lisp_inv_swap3 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap3])
  THEN1 (IMP_RES_TAC lisp_inv_swap4 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap4])
  THEN1 (IMP_RES_TAC lisp_inv_swap5 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap5]))
  |> SIMP_RULE std_ss [LET_DEF];

val mc_safe_cdr_lemma = prove(
  ``^LISP ==>
    ?w0i.
      mc_safe_cdr_pre (tw0,bp,w2w w0,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w0,df,f) = (tw0,bp,w2w w0i,df,f)) /\
      let (x0,w0) = (SAFE_CDR x0,w0i) in ^LISP``,
  FULL_SIMP_TAC std_ss [SAFE_CAR_def,SAFE_CDR_def]
  \\ FULL_SIMP_TAC std_ss [mc_safe_car_def,mc_safe_cdr_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [mc_safe_car_blast] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_type \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `isDot x0` \\ ASM_SIMP_TAC std_ss [] THEN1
   (IMP_RES_TAC lisp_inv_car \\ IMP_RES_TAC lisp_inv_cdr
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,mc_safe_car_blast])
  \\ `(CAR x0 = Sym "NIL") /\ (CDR x0 = Sym "NIL")` by ALL_TAC THEN1
    (Cases_on `x0` \\ FULL_SIMP_TAC std_ss [isDot_def,CAR_def,CDR_def])
  \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `3w`
  \\ `tw0 = 3w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ IMP_RES_TAC lisp_inv_nil
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [LET_DEF];

val mc_safe_cdr_thm = prove(
  ``^LISP ==>
    (?w0i.
      mc_safe_cdr_pre (tw0,bp,w2w w0,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w0,df,f) = (tw0,bp,w2w w0i,df,f)) /\
      let (x0,w0) = (SAFE_CDR x0,w0i) in ^LISP) /\
    (?w1i.
      mc_safe_cdr_pre (tw0,bp,w2w w1,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w1,df,f) = (tw0,bp,w2w w1i,df,f)) /\
      let (x1,w1) = (SAFE_CDR x1,w1i) in ^LISP) /\
    (?w2i.
      mc_safe_cdr_pre (tw0,bp,w2w w2,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w2,df,f) = (tw0,bp,w2w w2i,df,f)) /\
      let (x2,w2) = (SAFE_CDR x2,w2i) in ^LISP) /\
    (?w3i.
      mc_safe_cdr_pre (tw0,bp,w2w w3,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w3,df,f) = (tw0,bp,w2w w3i,df,f)) /\
      let (x3,w3) = (SAFE_CDR x3,w3i) in ^LISP) /\
    (?w4i.
      mc_safe_cdr_pre (tw0,bp,w2w w4,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w4,df,f) = (tw0,bp,w2w w4i,df,f)) /\
      let (x4,w4) = (SAFE_CDR x4,w4i) in ^LISP) /\
    (?w5i.
      mc_safe_cdr_pre (tw0,bp,w2w w5,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w5,df,f) = (tw0,bp,w2w w5i,df,f)) /\
      let (x5,w5) = (SAFE_CDR x5,w5i) in ^LISP)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF]
  THEN1 (IMP_RES_TAC mc_safe_cdr_lemma \\ METIS_TAC [])
  THEN1 (IMP_RES_TAC lisp_inv_swap1 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap1])
  THEN1 (IMP_RES_TAC lisp_inv_swap2 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap2])
  THEN1 (IMP_RES_TAC lisp_inv_swap3 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap3])
  THEN1 (IMP_RES_TAC lisp_inv_swap4 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap4])
  THEN1 (IMP_RES_TAC lisp_inv_swap5 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap5]))
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_safe_car_spec",mc_safe_car_spec);
val _ = save_thm("mc_safe_cdr_spec",mc_safe_cdr_spec);
val _ = save_thm("mc_safe_car_thm",mc_safe_car_thm);
val _ = save_thm("mc_safe_cdr_thm",mc_safe_cdr_thm);


(* code heap space test *)

val mc_code_heap_space_thm = prove(
  ``^LISP ==>
    (let tw2 = 3w in ^LISP) /\
    ((w2w (f (sp - 0x54w)) << 32 !! w2w (f (sp - 0x58w))) = EL 3 ds) /\
    {sp - 0x54w; sp - 0x58w} SUBSET df /\ (sp - 0x54w && 0x3w = 0x0w) /\
    (sp - 0x58w && 0x3w = 0x0w)``,
  STRIP_TAC \\ SIMP_TAC std_ss [LET_DEF]
  \\ IMP_RES_TAC lisp_inv_cs_read \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ MATCH_MP_TAC lisp_inv_ignore_tw2 \\ METIS_TAC [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_code_heap_space_thm",mc_code_heap_space_thm);


(* lemmas for code heap write *)

val expand_list = prove(
  ``!cs. (LENGTH cs = 10) ==>
         ?c0 c1 c2 c3 c4 c5 c6 c7 c8 c9. cs = [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9]``,
  Cases \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11,NOT_CONS_NIL]
  \\ DECIDE_TAC);

val expand_list2 = prove(
  ``!cs. (LENGTH cs = 10) ==> ?c0 c1 c2 c3 cs2. cs = (c0::c1::c2::c3::cs2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [CONS_11]);

val WRITE_CODE_APPEND = prove(
  ``!xs ys code.
       WRITE_CODE code (xs ++ ys) = WRITE_CODE (WRITE_CODE code xs) ys``,
  Induct \\ Cases_on `code` \\ Cases_on `p` \\ ASM_SIMP_TAC std_ss [WRITE_CODE_def,APPEND]);

val SND_WRITE_CODE = prove(
  ``!code x. code_ptr (WRITE_CODE code [x]) = code_ptr code + bc_length x``,
  Cases \\ Cases \\ Cases_on `p` \\ SIMP_TAC std_ss [WRITE_CODE_def,code_ptr_def]);

val bc_symbols_ok_APPEND = prove(
  ``!xs ys. bc_symbols_ok sym (xs ++ ys) =
            bc_symbols_ok sym xs /\ bc_symbols_ok sym ys``,
  Induct \\ SIMP_TAC std_ss [APPEND,bc_symbols_ok_def] \\ Cases_on `h`
  \\ ASM_SIMP_TAC std_ss [APPEND,bc_symbols_ok_def,CONJ_ASSOC]);

val code_length_def = Define `
  (code_length [] = 0) /\
  (code_length (x::xs) = bc_length x + code_length xs)`;

val bs2bytes_APPEND = prove(
  ``!xs ys k sym.
      bs2bytes (k,sym) (xs ++ ys) =
      bs2bytes (k,sym) xs ++ bs2bytes (k + code_length xs,sym) ys``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,bs2bytes_def,code_length_def]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,ADD_ASSOC]);

val bc_length_lemma = prove(
  ``0x100w <+ w /\ (LENGTH hs = w2n w) /\ n + w2n (w:word64) < 1073741824 ==>
    bc_length x <= LENGTH hs``,
  SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ `w2n w < 1073741824` by DECIDE_TAC
  \\ Cases_on `w` \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,word_lo_n2w]
  \\ Cases_on `x` \\ REPEAT (Cases_on `l`)
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,
        IMMEDIATE32_def,APPEND] \\ REPEAT DECIDE_TAC);

val SUC_EQ_LENGTH = prove(
  ``(SUC n <= LENGTH xs) = ?y ys. (xs = (y::ys)) /\ (n <= LENGTH ys)``,
  Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,NOT_CONS_NIL,CONS_11]);

val DROP_CONS = prove(
  ``DROP n (x::xs) = if n = 0 then x::xs else DROP (n-1) xs``,
  EVAL_TAC);

val LENGTH_bs2bytes = prove(
  ``!bs code.
       (WRITE_CODE (BC_CODE ((\x. NONE),0)) bs = code) ==>
       (LENGTH (bs2bytes (0,sym) bs) = code_ptr code)``,
  HO_MATCH_MP_TAC rich_listTheory.SNOC_INDUCT
  \\ SIMP_TAC std_ss [bs2bytes_def,WRITE_CODE_def,LENGTH,SNOC_APPEND]
  \\ SIMP_TAC std_ss [WRITE_CODE_APPEND,SND_WRITE_CODE]
  \\ SIMP_TAC std_ss [bs2bytes_APPEND,LENGTH_APPEND,bs2bytes_def,LENGTH,code_ptr_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `x` \\ REPEAT (Cases_on `l`) \\ EVAL_TAC);

val write_lemma = prove(
  ``!w ys. (w2n w = LENGTH ys + k) /\ n + (LENGTH ys + k) < 1073741824 ==>
           (w2n (w - n2w k) = LENGTH ys)``,
  Cases \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ ASM_SIMP_TAC wstd_ss [GSYM word_add_n2w,WORD_ADD_SUB,w2n_n2w]
  \\ REPEAT STRIP_TAC \\ `LENGTH ys < dimword (:'a)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []);

val mc_code_heap_blast = blastLib.BBLAST_PROVE
  ``(w2w ((w2w (w >>> 32)):word32) << 32 !! w2w ((w2w (w:word64)):word32) = w) /\
    ((63 >< 32) w = (w2w (w >>> 32)):word32) /\ ((31 >< 0) w = (w2w w):word32)``;

val WRITE_CODE_IMP_code_length = prove(
  ``!bs code k m.
      (WRITE_CODE (BC_CODE (m,k)) bs = code) ==>
      (code_length bs + k = code_ptr code)``,
  SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ Induct \\ ASM_SIMP_TAC std_ss [WRITE_CODE_def,code_length_def,code_ptr_def]
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);


(* generate approximate code for a few of the bytecode instructions *)

fun approx_code inst = let
  val xs = EVAL (mk_comb(``bc_ref (i,sym)``,inst))
           |> concl |> dest_eq |> snd |> listSyntax.dest_list |> fst
           |> map (fn tm => if can (numSyntax.int_of_term o cdr) tm then tm else ``0w:word64``)
           |> map (numSyntax.int_of_term o cdr)
           |> map (fn n => n mod 256)
           |> map (fn x => if x < 128 then x else x - 256)
  val enc = x64_encodeLib.x64_encode
  fun my_int_to_string n = if n < 0 then "-" ^ int_to_string (0-n) else int_to_string n
  fun encs (i,[]) = []
    | encs (i,(x::xs)) = ("mov BYTE [r2+"^ int_to_string i ^"]," ^ my_int_to_string x)
                         :: encs (i+1,xs)
  val l = length xs
  val code = (["mov r2,[r7-96]"] @ encs (0,xs) @
              ["mov r2,[r7-88]"] @
              ["sub r2," ^ int_to_string l] @
              ["add QWORD [r7-96]," ^ int_to_string l] @
              ["mov [r7-88],r2"])
  val _ = print "\n\n"
  val _ = map (fn x => print ("       " ^ x ^ "\n")) code
  val _ = print "\n\n"
  in () end


(* code heap -- write iCONST_NUM, same as iCONST_SYM *)

val (mc_write_num_spec,mc_write_num_def) = basic_decompile_strings x64_tools "mc_write_num"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       mov BYTE [r2+0],72
       mov BYTE [r2+1],-123
       mov BYTE [r2+2],-37
       mov BYTE [r2+3],62
       mov BYTE [r2+4],72
       mov BYTE [r2+5],117
       mov BYTE [r2+6],9
       mov BYTE [r2+7],-117
       mov BYTE [r2+8],-47
       mov BYTE [r2+9],72
       mov BYTE [r2+10],-1
       mov BYTE [r2+11],-89
       mov BYTE [r2+12],56
       mov BYTE [r2+13],-1
       mov BYTE [r2+14],-1
       mov BYTE [r2+15],-1
       mov BYTE [r2+16],72
       mov BYTE [r2+17],-1
       mov BYTE [r2+18],-53
       mov BYTE [r2+19],68
       mov BYTE [r2+20],-119
       mov BYTE [r2+21],4
       mov BYTE [r2+22],-97
       mov BYTE [r2+23],65
       mov BYTE [r2+24],-72
       mov BYTE [r2+25],r1b
       shr r1,8
       mov BYTE [r2+26],r1b
       shr r1,8
       mov BYTE [r2+27],r1b
       shr r1,8
       mov BYTE [r2+28],r1b
       mov r2,[r7-88]
       sub r2,29
       add QWORD [r7-96],29
       mov [r7-88],r2
       mov r1d,1
   `)

val const_num_blast = blastLib.BBLAST_PROVE
  ``(w2w (w2w (w:word30) << 2 + 0x1w:word32) = w2w w << 2 + 0x1w:word64) /\
    (w2w (w2w (v:29 word) << 3 + 0x3w:word32) = w2w v << 3 + 0x3w:word64) /\
    (w2w ((ww:word32) >>> 8) = (w2w ((w2w ww >>> 8):word64)):word8) /\
    (w2w ((ww:word32) >>> 16) = (w2w ((w2w ww >>> 16):word64)):word8) /\
    (w2w ((ww:word32) >>> 24) = (w2w ((w2w ww >>> 24):word64)):word8)``

val inst = ``iCONST_NUM (getVal x0)``
val mc_write_num_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_num_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_num (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_write_num_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by ALL_TAC THEN1
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast,IMMEDIATE32_def]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ Q.PAT_ASSUM `MAP ref_heap_addr xssss = yssss` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11]
  \\ Q.PAT_ASSUM `isVal x0` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [isVal_thm]
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt,lisp_x_def,getVal_def]
  \\ FULL_SIMP_TAC std_ss [const_num_blast]
  \\ `w2w ((n2w a):word30) = (n2w a):word64` by ALL_TAC THEN1
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH,APPEND,IMMEDIATE32_def] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ `(1 + 4 * a) < 2**32` by (FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `w2w ((n2w (1 + 4 * a)):word32) = (n2w (1 + 4 * a)):word64` by ALL_TAC THEN1
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ SEP_W_TAC
  \\ `(1 + 4 * a) < 2**64` by (FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [];

val LIST_FIND_SOME_IMP = prove(
  ``!xs x a i. (LIST_FIND x a xs = SOME i) ==> MEM a xs``,
  Induct \\ SRW_TAC [] [LIST_FIND_def,MEM] \\ RES_TAC \\ ASM_SIMP_TAC std_ss []);

val inst = ``iCONST_SYM (getSym x0)``
val mc_write_sym_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isSym x0 ==>
    ?fi di tw2i.
        mc_write_num_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_num (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_write_num_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by ALL_TAC THEN1
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast,IMMEDIATE32_def]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ Q.PAT_ASSUM `MAP ref_heap_addr xssss = yssss` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11]
  \\ Q.PAT_ASSUM `isSym x0` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [isSym_thm]
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt,lisp_x_def,getSym_def]
  \\ IMP_RES_TAC LIST_FIND_SOME_IMP
  \\ FULL_SIMP_TAC std_ss [const_num_blast]
  \\ `w2w ((n2w k):29 word) = (n2w k):word64` by ALL_TAC THEN1
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH,APPEND,IMMEDIATE32_def] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ `(3 + 8 * k) < 2**32` by (FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `w2w ((n2w (3 + 8 * k)):word32) = (n2w (3 + 8 * k)):word64` by ALL_TAC THEN1
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ ASM_SIMP_TAC std_ss [] \\ SEP_W_TAC
  \\ `(3 + 8 * k) < 2**64` by (FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [];


(* code heap -- write iJUMP, iJNIL, iCALL *)

val (mc_write_jump_spec,mc_write_jump_def) = basic_decompile_strings x64_tools "mc_write_jump"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       shr r1,2
       add r1,[r7-160]
       sub r1,r2
       sub r1,6
       mov BYTE [r2],72
       mov BYTE [r2+1],-23
       mov BYTE [r2+2],r1b
       shr r1,8
       mov BYTE [r2+3],r1b
       shr r1,8
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       mov r2,[r7-88]
       sub r2,6
       add QWORD [r7-96],6
       mov [r7-88],r2
       mov r1d,1
   `)

val (mc_write_call_spec,mc_write_call_def) = basic_decompile_strings x64_tools "mc_write_call"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       shr r1,2
       add r1,[r7-160]
       sub r1,r2
       sub r1,6
       mov BYTE [r2],72
       mov BYTE [r2+1],-24
       mov BYTE [r2+2],r1b
       shr r1,8
       mov BYTE [r2+3],r1b
       shr r1,8
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       mov r2,[r7-88]
       sub r2,6
       add QWORD [r7-96],6
       mov [r7-88],r2
       mov r1d,1
   `)

val (mc_write_jnil_spec,mc_write_jnil_def) = basic_decompile_strings x64_tools "mc_write_jnil"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       shr r1,2
       add r1,[r7-160]
       sub r1,r2
       sub r1,21
       mov BYTE [r2+0],77
       mov BYTE [r2+1],-117
       mov BYTE [r2+2],-56
       mov BYTE [r2+3],68
       mov BYTE [r2+4],-117
       mov BYTE [r2+5],4
       mov BYTE [r2+6],-97
       mov BYTE [r2+7],72
       mov BYTE [r2+8],-1
       mov BYTE [r2+9],-61
       mov BYTE [r2+10],73
       mov BYTE [r2+11],-125
       mov BYTE [r2+12],-7
       mov BYTE [r2+13],3
       mov BYTE [r2+14],72
       mov BYTE [r2+15],15
       mov BYTE [r2+16],-124
       mov BYTE [r2+17],r1b
       shr r1,8
       mov BYTE [r2+18],r1b
       shr r1,8
       mov BYTE [r2+19],r1b
       shr r1,8
       mov BYTE [r2+20],r1b
       mov r2,[r7-88]
       sub r2,21
       add QWORD [r7-96],21
       mov [r7-88],r2
       mov r1d,1
   `)

val mc_write_jump_blast = blastLib.BBLAST_PROVE
  ``((w2w:word64->word8) ((w2w:word32->word64) (w - v) >>> 24) = w2w ((w2w w - (w2w:word32->word64) v) >>> 24)) /\
    ((w2w:word64->word8) ((w2w:word32->word64) (w - v) >>> 16) = w2w ((w2w w - (w2w:word32->word64) v) >>> 16)) /\
    ((w2w:word64->word8) ((w2w:word32->word64) (w - v) >>> 8) = w2w ((w2w w - (w2w:word32->word64) v) >>> 8)) /\
    ((w2w:word64->word8) ((w2w:word32->word64) (w - v)) = w2w ((w2w w - (w2w:word32->word64) v))) /\
    ((w2w:word32->word8) (x - y) = (w2w:word64->word8) (w2w x - w2w y))``

fun iJUMP_TAC inst =
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_write_jump_def,mc_write_call_def,mc_write_jnil_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by ALL_TAC THEN1
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast,IMMEDIATE32_def]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ Q.PAT_ASSUM `MAP ref_heap_addr xssss = yssss` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11]
  \\ Q.PAT_ASSUM `isVal x0` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [isVal_thm]
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt,lisp_x_def,getVal_def]
  \\ FULL_SIMP_TAC std_ss [const_num_blast]
  \\ `w2w ((n2w a):word30) = (n2w a):word64` by ALL_TAC THEN1
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH,APPEND,IMMEDIATE32_def] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ `(n2w a << 2 + 0x1w) >>> 2 = (n2w a):word64` by ALL_TAC THEN1
   (ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ SIMP_TAC std_ss [WORD_ADD_SUB]
    \\ `n2w a <+ n2w (2**30):word64` by ALL_TAC THEN1
      (`a < (2**64)` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
       \\ FULL_SIMP_TAC wstd_ss [word_lo_n2w])
    \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`(n2w a):word64`,`w`)
    \\ blastLib.BBLAST_TAC)
  \\ ASM_SIMP_TAC std_ss [WORD_SUB_PLUS,WORD_ADD_SUB]
  \\ `code_length bs = code_ptr code` by METIS_TAC [WRITE_CODE_IMP_code_length,ADD_0]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [mc_write_jump_blast]
  \\ `((w2w:word32->word64) (n2w a) = n2w a) /\
      ((w2w:word32->word64) (n2w (code_ptr code)) = n2w (code_ptr code)) /\
      ((w2w:word32->word64) (n2w (code_ptr code + 6)) = n2w (code_ptr code + 6)) /\
      ((w2w:word32->word64) (n2w (code_ptr code + 21)) = n2w (code_ptr code + 21))` by ALL_TAC THEN1
   (`a < 4294967296 /\ code_ptr code < 4294967296 /\
     code_ptr code + 6 < 4294967296 /\ code_ptr code + 21 < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,n2w_11])
  \\ ASM_SIMP_TAC std_ss []
  \\ SEP_WRITE_TAC

val inst = ``iJUMP (getVal x0)``
val mc_write_jump_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_jump_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_jump (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iJUMP_TAC inst) |> SIMP_RULE std_ss [];

val inst = ``iCALL (getVal x0)``
val mc_write_call_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_call_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_call (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iJUMP_TAC inst) |> SIMP_RULE std_ss [];

val inst = ``iJNIL (getVal x0)``
val mc_write_jnil_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_jnil_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_jnil (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iJUMP_TAC inst) |> SIMP_RULE std_ss [];


(* code heap -- write iPOPS, iSTORE, iLOAD *)

val (mc_write_pops_spec,mc_write_pops_def) = basic_decompile_strings x64_tools "mc_write_pops"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       shr r1,2
       mov BYTE [r2+0],72
       mov BYTE [r2+1],-127
       mov BYTE [r2+2],-61
       mov BYTE [r2+3],r1b
       shr r1,8
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       shr r1,8
       mov BYTE [r2+6],r1b
       mov r2,[r7-88]
       sub r2,7
       add QWORD [r7-96],7
       mov [r7-88],r2
       mov r1d,1
   `)

val (mc_write_store_spec,mc_write_store_def) = basic_decompile_strings x64_tools "mc_write_store"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       sub r1,1
       mov BYTE [r2+0],68
       mov BYTE [r2+1],-119
       mov BYTE [r2+2],-124
       mov BYTE [r2+3],-97
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       shr r1,8
       mov BYTE [r2+6],r1b
       shr r1,8
       mov BYTE [r2+7],r1b
       mov BYTE [r2+8],68
       mov BYTE [r2+9],-117
       mov BYTE [r2+10],4
       mov BYTE [r2+11],-97
       mov BYTE [r2+12],72
       mov BYTE [r2+13],-1
       mov BYTE [r2+14],-61
       mov r2,[r7-88]
       sub r2,15
       add QWORD [r7-96],15
       mov [r7-88],r2
       mov r1d,1
   `)

val (mc_write_load_spec,mc_write_load_def) = basic_decompile_strings x64_tools "mc_write_load"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       sub r1,1
       mov BYTE [r2+0],72
       mov BYTE [r2+1],-123
       mov BYTE [r2+2],-37
       mov BYTE [r2+3],62
       mov BYTE [r2+4],72
       mov BYTE [r2+5],117
       mov BYTE [r2+6],9
       mov BYTE [r2+7],-117
       mov BYTE [r2+8],-47
       mov BYTE [r2+9],72
       mov BYTE [r2+10],-1
       mov BYTE [r2+11],-89
       mov BYTE [r2+12],56
       mov BYTE [r2+13],-1
       mov BYTE [r2+14],-1
       mov BYTE [r2+15],-1
       mov BYTE [r2+16],72
       mov BYTE [r2+17],-1
       mov BYTE [r2+18],-53
       mov BYTE [r2+19],68
       mov BYTE [r2+20],-119
       mov BYTE [r2+21],4
       mov BYTE [r2+22],-97
       mov BYTE [r2+23],68
       mov BYTE [r2+24],-117
       mov BYTE [r2+25],-124
       mov BYTE [r2+26],-97
       mov BYTE [r2+27],r1b
       shr r1,8
       mov BYTE [r2+28],r1b
       shr r1,8
       mov BYTE [r2+29],r1b
       shr r1,8
       mov BYTE [r2+30],r1b
       mov r2,[r7-88]
       sub r2,31
       add QWORD [r7-96],31
       mov [r7-88],r2
       mov r1d,1
   `)

val mc_write_pops_blast = blastLib.BBLAST_PROVE
  ``((w2w:word32->word8) x = (w2w:word64->word8) (w2w x))``

fun iPOPS_TAC inst =
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_write_pops_def,mc_write_load_def,mc_write_store_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by ALL_TAC THEN1
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast,IMMEDIATE32_def]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,
       Q.SPECL [`w`,`8`,`8`] LSR_ADD, Q.SPECL [`w`,`8`,`16`] LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ Q.PAT_ASSUM `MAP ref_heap_addr xssss = yssss` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11]
  \\ Q.PAT_ASSUM `isVal x0` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [isVal_thm]
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt,lisp_x_def,getVal_def]
  \\ FULL_SIMP_TAC std_ss [const_num_blast]
  \\ `w2w ((n2w a):word30) = (n2w a):word64` by ALL_TAC THEN1
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH,APPEND,IMMEDIATE32_def] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ `(n2w a << 2 + 0x1w) >>> 2 = (n2w a):word64` by ALL_TAC THEN1
   (ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ SIMP_TAC std_ss [WORD_ADD_SUB]
    \\ `n2w a <+ n2w (2**30):word64` by ALL_TAC THEN1
      (`a < (2**64)` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
       \\ FULL_SIMP_TAC wstd_ss [word_lo_n2w])
    \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`(n2w a):word64`,`w`)
    \\ blastLib.BBLAST_TAC)
  \\ ASM_SIMP_TAC std_ss [WORD_SUB_PLUS,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
  \\ `(w2w:word32->word64) (n2w (4 * a)) = n2w (4 * a)` by ALL_TAC THEN1
     (`(4 * a) < 4294967296` by DECIDE_TAC
      \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,n2w_11])
  \\ ASM_SIMP_TAC std_ss []
  \\ `code_length bs = code_ptr code` by METIS_TAC [WRITE_CODE_IMP_code_length,ADD_0]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [mc_write_jump_blast]
  \\ `((w2w:word32->word64) (n2w a) = n2w a) /\
      ((w2w:word32->word64) (n2w (code_ptr code)) = n2w (code_ptr code))` by ALL_TAC THEN1
   (`a < 4294967296 /\ code_ptr code < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,n2w_11])
  \\ ASM_SIMP_TAC std_ss [mc_write_pops_blast]
  \\ SEP_WRITE_TAC


val inst = ``iPOPS (getVal x0)``
val mc_write_pops_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_pops_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_pops (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iPOPS_TAC inst) |> SIMP_RULE std_ss [];

val inst = ``iSTORE (getVal x0)``
val mc_write_store_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 /\ getVal x0 < 536870912 ==>
    ?fi di tw2i.
        mc_write_store_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_store (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iPOPS_TAC inst) |> SIMP_RULE std_ss [];

val inst = ``iLOAD (getVal x0)``
val mc_write_load_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 /\ getVal x0 < 536870912 ==>
    ?fi di tw2i.
        mc_write_load_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_load (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iPOPS_TAC inst) |> SIMP_RULE std_ss [];


(* code heap -- write const instructions *)

local
val ready_formats = let (* derive Hoare triples for mov BYTE [r2+???],??? *)
  fun foo i = let
    val e = x64_encodeLib.x64_encode ("mov BYTE [r2+"^(int_to_string i)^"],34")
    val e = String.substring(e,0,size(e)-2)
    val (x,_) = x64_spec e
    in (e,x) end
  fun genlist i n f = if i = n then [] else
                        (print (int_to_string (256-i)); f i :: genlist (i+1) n f)
  in genlist 0 256 foo end
in
fun instantiate_ready_format s = let
  val e = String.substring(s,0,size(s)-2)
  val t = String.substring(s,size(s)-2,2)
  fun list_find x [] = fail()
    | list_find x ((y,z)::xs) = if x = y then z else list_find x xs
  val (th,i,j) = list_find e ready_formats
  val n = numSyntax.mk_numeral(Arbnum.fromHexString t)
  val th = INST [mk_var("imm8",``:word8``)|->``(n2w ^n):word8``] th
  val tm = find_term (can (match_term ``SIGN_EXTEND x y z MOD 256``)) (concl th)
  val th = RW [EVAL tm] th
  in (th,i,j) end handle Subsript => fail()
end;

fun get_code_for_bc_inst inst = let
  val ys = EVAL (mk_comb(``bc_ref (i,sym)``,inst))
           |> concl |> dest_eq |> snd |> listSyntax.dest_list |> fst
           |> map (fn tm => if wordsSyntax.is_w2w tm then ``0w:word64`` else tm)
           |> map (numSyntax.int_of_term o cdr)
           |> map (fn n => n mod 256)
  val xs = ys |> map (fn x => if x < 128 then x else x - 256)
  val enc = x64_encodeLib.x64_encode
  fun my_int_to_string n = if n < 0 then "-" ^ int_to_string (0-n) else int_to_string n
  fun encs (i,[]) = []
    | encs (i,(x::xs)) = ("mov BYTE [r2+"^ int_to_string i ^"]," ^ my_int_to_string x)
                         :: encs (i+1,xs)
  val l = length xs
  val (c1,c2,c3) = (["mov r2,[r7-96]"], encs (0,xs),
              ["mov r2,[r7-88]"] @
              ["sub r2," ^ int_to_string l] @
              ["add QWORD [r7-96]," ^ int_to_string l] @
              ["mov [r7-88],r2"])
  in (map enc c1 @ map enc c2 @ map enc c3,ys) end

fun straight_line_decompile func_name code in_out_vars = let
  val _ = print "\nStraight-line decompile, "
  val (spec,_,sts,pc) = x64_tools
  fun my_spec s = (instantiate_ready_format s,NONE) handle HOL_ERR _ => spec s
  fun simple_spec s = let val ((th,_,_),_) = my_spec s in HIDE_STATUS_RULE true sts th end;
  val counter = ref 0
  val total = length code
  fun next x = (counter := 1+(!counter); print ("\n" ^ int_to_string (!counter) ^ " of " ^ int_to_string total ^ " "); x)
  val thms = map simple_spec code
  val th = SPEC_COMPOSE_RULE thms
  val th = SIMP_RULE (std_ss++sep_cond_ss) [] th
  val th = Q.INST [`rip`|->`p`] th
  val (_,p,_,q) = dest_spec (concl (UNDISCH_ALL (RW [progTheory.SPEC_MOVE_COND] th)))
  val ps = filter (not o can dest_sep_hide) (list_dest dest_star p)
  val qs = filter (not o can dest_sep_hide) (list_dest dest_star q)
  val ps = filter (fn tm => not (car tm = pc) handle HOL_ERR _ => true) ps
  val qs = filter (fn tm => not (car tm = pc) handle HOL_ERR _ => true) qs
  fun safe_car tm = car tm handle HOL_ERR _ => tm
  val sorter = sort (fn t1 => fn t2 => term_to_string (safe_car t1) <= term_to_string (safe_car t2))
  val ps = sorter ps
  val qs = sorter qs
  val px = list_mk_star(ps)(type_of (hd ps))
  val qx = list_mk_star(qs)(type_of (hd qs))
  val s = fst (match_term px qx)
  val result = subst s in_out_vars
  val ty = type_of (pairSyntax.mk_pabs(in_out_vars,in_out_vars))
  val def = new_definition(func_name,mk_eq(mk_comb(mk_var(func_name,ty),in_out_vars),result))
  val ty = type_of (pairSyntax.mk_pabs(in_out_vars,``T:bool``))
  val pre_result = th |> RW [progTheory.SPEC_MOVE_COND] |> concl |> dest_imp |> fst
                   handle HOL_ERR _ => ``T``
  val pre = new_definition(func_name ^ "_pre",mk_eq(mk_comb(mk_var(func_name ^ "_pre",ty),in_out_vars),pre_result))
  val th = RW [GSYM pre] th
  val new_q = subst (map (fn {redex= x, residue=y} => y |-> x) s) q
  val rhs = def |> SPEC_ALL |> concl |> dest_eq |> fst
  val new_q = pairSyntax.mk_anylet([(in_out_vars,rhs)],new_q)
  val (th,goal) = SPEC_WEAKEN_RULE th new_q
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [LET_DEF,def,SEP_IMP_REFL])
  val th = MP th lemma
  val x = CONJ (SPEC_ALL def) (SPEC_ALL pre)
  val _ = print "done!\n"
  in (th,x) end;

val one_write_list_def = Define `
  (one_write_list a [] f = f) /\
  (one_write_list (a:word64) (x::xs) f = one_write_list (a + 1w) xs ((a =+ x) f))`;

val one_address_list_def = Define `
  (one_address_list a [] = []) /\
  (one_address_list (a:word64) (x::xs) = a::one_address_list (a+1w) xs)`;

val STAR5_LEMMA = prove(
  ``STAR x1 x2 * x3 * x4 * x5 = x1 * x3 * x2 * x4 * x5``,
  SIMP_TAC (std_ss++star_ss) []);

val one_write_list_lemma = prove(
  ``!xs b a x y p q d.
      (p * one (a,x) * one_byte_list b (MAP FST xs) * q)
          (fun2set (one_write_list b (MAP FST xs) d,dd)) ==>
      (p * one (a,y) * one_byte_list b (MAP FST xs) * q)
          (fun2set (one_write_list b (MAP FST xs) ((a =+ y) d),dd))``,
  Induct \\ SIMP_TAC std_ss [MAP,one_write_list_def]
  THEN1 (REPEAT STRIP_TAC \\ SEP_WRITE_TAC)
  \\ FULL_SIMP_TAC std_ss [one_write_list_def,one_byte_list_def,STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [STAR5_LEMMA]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `y`)
  \\ `~(b = a)` by SEP_NEQ_TAC \\ METIS_TAC [UPDATE_COMMUTES]);

val one_write_list_thm = prove(
  ``!xs p q d a.
      (p * one_byte_list a (MAP SND xs) * q) (fun2set (d,dd)) ==>
      (p * one_byte_list a (MAP FST xs) * q)
         (fun2set (one_write_list a (MAP FST xs) d,dd)) /\
      EVERY (\a. a IN dd) (one_address_list a xs)``,
  Induct \\ SIMP_TAC std_ss [MAP,one_byte_list_def,one_write_list_def,
    STAR_ASSOC,one_address_list_def,EVERY_DEF] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ SEP_R_TAC \\ IMP_RES_TAC one_write_list_lemma \\ FULL_SIMP_TAC std_ss []);


fun generate_and_verify_write_const (name,inst) = let
  val _ = print ("\n\n"^name^"\n\n")
  val (code,ys) = get_code_for_bc_inst inst
  val func_name = ("mc_write_" ^ name)
  val in_out_vars =
    ``(r2:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``
  val (spec_thm,def_thm) = straight_line_decompile name code in_out_vars
  val ds = map (car o fst o dest_eq o concl) (CONJUNCTS def_thm)
  val def = el 1 ds
  val pre = el 2 ds
  val goal =
    ``^LISP /\ 0x100w <+ EL 3 ds ==>
     ?fi di tw2i.
        pre (tw2,sp,df,f,dd,d) /\
        (def (tw2,sp,df,f,dd,d) = (tw2i,sp,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length inst)) ds)) in ^LISP``
    |> subst [mk_var("inst",type_of inst)|->inst]
    |> subst [mk_var("pre",type_of pre)|->pre]
    |> subst [mk_var("def",type_of def)|->def]
  val write_list_th =
    map (fn x => pairSyntax.mk_pair(genvar(``:word8``),genvar(``:word8``))) ys
    |> (fn xs => listSyntax.mk_list(xs,type_of (hd xs)))
    |> (fn tm => Q.SPECL [`p`,`q`,`d`,`a + n2w n`] (SPEC tm one_write_list_thm))
    |> SIMP_RULE std_ss [EVERY_DEF,MAP,one_address_list_def,word_arith_lemma1,
         one_write_list_def,one_byte_list_def,STAR_ASSOC,SEP_CLAUSES]
(*
set_goal([],goal)
*)
  val tac =
 (REPEAT STRIP_TAC \\ SIMP_TAC std_ss [def_thm,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by ALL_TAC THEN1
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def]
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ Q.PAT_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC (GEN_ALL write_list_th) \\ ASM_SIMP_TAC std_ss [])
  val correct_thm = prove(goal,tac) |> SIMP_RULE std_ss [LET_DEF];
  in CONJ spec_thm correct_thm end

(*

val my_consts = LIST_CONJ (map generate_and_verify_write_const
  [("isymbol_less",``iDATA (opSYMBOL_LESS)``)])

*)

val all_const_insts =
  [("ipop",``iPOP``),
   ("isymbol_less",``iDATA (opSYMBOL_LESS)``),
   ("ijump_sym",``iJUMP_SYM``),
   ("icall_sym",``iCALL_SYM``),
   ("ireturn",``iRETURN``),
   ("ifail",``iFAIL``),
   ("icompile",``iCOMPILE``),
   ("iprint",``iPRINT``),
   ("icons",``iDATA (opCONS)``),
   ("iequal",``iDATA (opEQUAL)``),
   ("iless",``iDATA (opLESS)``),
   ("iadd",``iDATA (opADD)``),
   ("isub",``iDATA (opSUB)``),
   ("iconsp",``iDATA (opCONSP)``),
   ("inatp",``iDATA (opNATP)``),
   ("isymbolp",``iDATA (opSYMBOLP)``),
   ("icar",``iDATA (opCAR)``),
   ("icdr",``iDATA (opCDR)``),
   ("ilookup",``iCONST_LOOKUP``)]

val consts = LIST_CONJ (map generate_and_verify_write_const all_const_insts);


(* code heap -- update iJUMP, iJNIL *)

val (mc_update_jump_spec,mc_update_jump_def) = basic_decompile_strings x64_tools "mc_update_jump"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r1,r8
       mov r2,r9
       shr r1,2
       shr r2,2
       sub r1,r2
       sub r1,6
       add r2,[r7-160]
       mov BYTE [r2+2],r1b
       shr r1,8
       mov BYTE [r2+3],r1b
       shr r1,8
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       mov r1d,1
   `)

val (mc_update_jnil_spec,mc_update_jnil_def) = basic_decompile_strings x64_tools "mc_update_jnil"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r1,r8
       mov r2,r9
       shr r1,2
       shr r2,2
       sub r1,r2
       sub r1,21
       add r2,[r7-160]
       mov BYTE [r2+17],r1b
       shr r1,8
       mov BYTE [r2+18],r1b
       shr r1,8
       mov BYTE [r2+19],r1b
       shr r1,8
       mov BYTE [r2+20],r1b
       mov r1d,1
   `)

val REPLACE_CODE_def = Define `
  REPLACE_CODE (BC_CODE (c1,c2)) p x = BC_CODE ((p =+ SOME x) c1,c2)`;

val SND_REPLACE_CODE = prove(
  ``!code p x. code_ptr (REPLACE_CODE code p x) = code_ptr code``,
  Cases \\ Cases_on `p` \\ FULL_SIMP_TAC std_ss [REPLACE_CODE_def,code_ptr_def]);

val CODE_UPDATE_def = Define `
  CODE_UPDATE x (BC_CODE (c,n)) = BC_CODE ((n =+ SOME x) c, n + bc_length x)`;

val WRITE_CODE_SNOC = prove(
  ``!xs x c. WRITE_CODE c (xs ++ [x]) = CODE_UPDATE x (WRITE_CODE c xs)``,
  Induct \\ Cases_on `c` \\ Cases_on `p`
  \\ ASM_SIMP_TAC std_ss [APPEND,WRITE_CODE_def,CODE_UPDATE_def]);

val WRITE_CODE_code_length = prove(
  ``!bs m k q.
      (WRITE_CODE (BC_CODE (m,k)) bs = BC_CODE (q,n)) ==>
      (code_length bs = n - k) /\ k <= n``,
  Induct \\ SIMP_TAC (srw_ss()) [WRITE_CODE_def,code_length_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val code_length_IM_SPLIT = prove(
  ``!bs n code x.
      (code_mem code n = SOME x) /\
      (WRITE_CODE (BC_CODE ((\x.NONE),0)) bs = code) ==>
      ?bs1 bs2. (bs = bs1 ++ [x] ++ bs2) /\ (code_length bs1 = n)``,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ SIMP_TAC std_ss [code_length_def,WRITE_CODE_def,code_mem_def]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_SNOC,SNOC_APPEND]
  \\ Cases_on `WRITE_CODE (BC_CODE ((\x. NONE),0)) bs` \\ Cases_on `p`
  \\ FULL_SIMP_TAC std_ss [code_mem_def,CODE_UPDATE_def,APPLY_UPDATE_THM]
  \\ Cases_on `r = n` \\ FULL_SIMP_TAC std_ss [] THEN1
   (IMP_RES_TAC WRITE_CODE_code_length \\ Q.LIST_EXISTS_TAC [`bs`,`[]`]
    \\ FULL_SIMP_TAC std_ss [APPEND_NIL])
  \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`bs1`,`bs2 ++ [x]`]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]);

val code_length_APPEND = prove(
  ``!xs ys. code_length (xs ++ ys) = code_length xs + code_length ys``,
  Induct \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [ADD_ASSOC]);

val bc_length_NOT_ZERO = prove(
  ``!x. 0 < bc_length x``,
  Cases \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC);

val WRITE_CODE_REPLACE_CODE_IMP = prove(
  ``!bs2 bs1 code m.
      (bc_length x = bc_length y) /\
      (WRITE_CODE (BC_CODE (m,0)) (bs1 ++ [x] ++ bs2) = code) ==>
      (WRITE_CODE (BC_CODE (m,0)) (bs1 ++ [y] ++ bs2) =
       REPLACE_CODE code (code_length bs1) y)``,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ SIMP_TAC std_ss [code_length_def,WRITE_CODE_def,code_mem_def]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND_ASSOC,WRITE_CODE_SNOC]
    \\ Q.PAT_ASSUM `!x.b` (ASSUME_TAC o Q.SPECL [`bs1`,`m`])
    \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `WRITE_CODE (BC_CODE (m,0)) (bs1 ++ [x] ++ bs2)`
    \\ Cases_on `p`
    \\ IMP_RES_TAC WRITE_CODE_code_length
    \\ FULL_SIMP_TAC std_ss [code_length_APPEND,code_length_def]
    \\ `0 < bc_length x` by FULL_SIMP_TAC std_ss [bc_length_NOT_ZERO]
    \\ `~(r = code_length bs1)` by DECIDE_TAC
    \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,APPLY_UPDATE_THM]
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [APPEND_NIL,WRITE_CODE_SNOC]
  \\ Cases_on `WRITE_CODE (BC_CODE (m,0)) bs1` \\ Cases_on `p`
  \\ IMP_RES_TAC WRITE_CODE_code_length
  \\ FULL_SIMP_TAC std_ss [REPLACE_CODE_def,CODE_UPDATE_def]
  \\ FULL_SIMP_TAC std_ss [combinTheory.UPDATE_EQ]);

val LENGTH_bs2bytes_EQ = prove(
  ``!bs k sym. LENGTH (bs2bytes (k,sym) bs) = code_length bs``,
  Induct \\ ASM_SIMP_TAC std_ss [bs2bytes_def,LENGTH,code_length_def,LENGTH_APPEND]
  \\ Cases \\ EVAL_TAC \\ SIMP_TAC std_ss []
  \\ Cases_on `l` \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val code_length_APPEND = prove(
  ``!xs ys. code_length (xs ++ ys) = code_length xs + code_length ys``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,code_length_def,ADD_ASSOC]);

val replace_jump_balst = blastLib.BBLAST_PROVE
  ``(w2w:word32->word64) (w2w (w:30 word) << 2 !! 1w) >>> 2 = w2w w``

val replace_jump_balst2 = blastLib.BBLAST_PROVE
  ``((w2w:word32->word8) ((w - v) >>> 24) = w2w ((w2w w - (w2w:word32->word64) v) >>> 24)) /\
    ((w2w:word32->word8) ((w - v) >>> 16) = w2w ((w2w w - (w2w:word32->word64) v) >>> 16)) /\
    ((w2w:word32->word8) ((w - v) >>> 8) = w2w ((w2w w - (w2w:word32->word64) v) >>> 8)) /\
    ((w2w:word32->word8) ((w - v)) = w2w ((w2w w - (w2w:word32->word64) v)))``

fun REPLACE_JUMP_TAC inst =
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_update_jump_def,mc_update_jnil_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ,SND_REPLACE_CODE]
  \\ `?bs1 bs2. (bs = bs1 ++ [^(car inst) 0] ++ bs2) /\ (code_length bs1 = getVal x1)` by METIS_TAC [code_length_IM_SPLIT]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `bs1 ++ [^inst] ++ bs2` \\ Q.EXISTS_TAC `hs`
  \\ IMP_RES_TAC WRITE_CODE_REPLACE_CODE_IMP
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_APPEND,bs2bytes_APPEND,bs2bytes_def,
        bc_symbols_ok_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,one_byte_list_def,
        one_byte_list_APPEND,APPEND,LENGTH_APPEND,LENGTH,SEP_CLAUSES,STAR_ASSOC,
        word_arith_lemma1,GSYM ADD_ASSOC,LENGTH_bs2bytes_EQ,code_length_APPEND,
        code_length_def,bc_length_def]
  \\ `(w2w w0 >>> 2 = (n2w (getVal x0)):word64) /\ getVal x0 < 2**30 /\
      (w2w w1 >>> 2 = (n2w (getVal x1)):word64) /\ getVal x1 < 2**30` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [isVal_thm,getVal_def]
    \\ Q.PAT_ASSUM `MAP ref_heap_addr [s0; s1; s2; s3; s4; s5] = xx` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF,CONS_11,MAP,lisp_x_def,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [replace_jump_balst]
    \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,WORD_MUL_LSL,word_add_n2w,word_mul_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ ASM_SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
  \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [replace_jump_balst2]
  \\ `(((w2w:word32->word64) (n2w (getVal x0)) = n2w (getVal x0))) /\
      (((w2w:word32->word64) (n2w (getVal x1)) = n2w (getVal x1))) /\
      (((w2w:word32->word64) (n2w (getVal x1 + 6)) = n2w (getVal x1 + 6))) /\
      (((w2w:word32->word64) (n2w (getVal x1 + 21)) = n2w (getVal x1 + 21)))` by ALL_TAC THEN1
   (IMP_RES_TAC (DECIDE ``n < 1073741824 ==> (n:num) < 4294967296 /\ n+6 < 4294967296 /\ n+21 < 4294967296``)
    \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ SEP_WRITE_TAC

val inst = ``iJUMP (getVal x0)``
val mc_update_jump_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==>
    isVal x0 /\ isVal x1 /\ (code_mem code (getVal x1) = SOME (^(car inst) 0)) ==>
    ?di tw2i.
        mc_update_jump_pre (tw1,tw2,sp,w2w w0,w2w w1,df,f,dd,d) /\
        (mc_update_jump (tw1,tw2,sp,w2w w0,w2w w1,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,w2w w1,df,f,dd,di)) /\
         let (code,d,tw2) = (REPLACE_CODE code (getVal x1) ^inst,di,tw2i) in ^LISP``,
  REPLACE_JUMP_TAC inst) |> SIMP_RULE std_ss [LET_DEF];

val inst = ``iJNIL (getVal x0)``
val mc_update_jnil_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==>
    isVal x0 /\ isVal x1 /\ (code_mem code (getVal x1) = SOME (^(car inst) 0)) ==>
    ?di tw2i.
        mc_update_jnil_pre (tw1,tw2,sp,w2w w0,w2w w1,df,f,dd,d) /\
        (mc_update_jnil (tw1,tw2,sp,w2w w0,w2w w1,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,w2w w1,df,f,dd,di)) /\
         let (code,d,tw2) = (REPLACE_CODE code (getVal x1) ^inst,di,tw2i) in ^LISP``,
  REPLACE_JUMP_TAC inst) |> SIMP_RULE std_ss [LET_DEF];


(* store all code heap write/replace *)

val numsym  = LIST_CONJ [CONJ (mc_write_num_spec) (mc_write_num_thm),
                         CONJ (mc_write_num_spec) (mc_write_sym_thm)];
val pops  = LIST_CONJ [CONJ (mc_write_pops_spec) (mc_write_pops_thm),
                       CONJ (mc_write_load_spec) (mc_write_load_thm),
                       CONJ (mc_write_store_spec) (mc_write_store_thm)];
val calls = LIST_CONJ [CONJ (mc_write_call_spec) (mc_write_call_thm),
                       CONJ (mc_write_jump_spec) (mc_write_jump_thm),
                       CONJ (mc_write_jnil_spec) (mc_write_jnil_thm)];
val updates = LIST_CONJ [CONJ mc_update_jump_spec mc_update_jump_thm,
                         CONJ mc_update_jnil_spec mc_update_jnil_thm]

val lisp_inv_write_consts_thm = save_thm("lisp_inv_write_consts_thm",
  LIST_CONJ [numsym,updates,pops,calls,consts]);


(* load pointer into code (used by eval) *)

val (mc_calc_addr_spec,mc_calc_addr_def) = basic_decompile_strings x64_tools "mc_calc_addr"
  (SOME (``(r2:word64,r7:word64,r10:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r7:word64,r10:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r2,r10
       shr r2,2
       add r2,[r7-160]
   `)

val _ = save_thm("mc_calc_addr_spec",mc_calc_addr_spec);

val mc_calc_addr_thm = store_thm("mc_calc_addr_thm",
  ``^LISP ==> isVal x2 ==>
    ?tw2i. mc_calc_addr_pre (tw2,sp,w2w w2,df,f) /\
           (mc_calc_addr (tw2,sp,w2w w2,df,f) = (tw2i,sp,w2w w2,df,f)) /\
           (tw2i = EL 4 cs + n2w (getVal x2)) /\
           let tw2 = tw2i in ^LISP``,
  FULL_SIMP_TAC std_ss [LET_DEF,mc_calc_addr_def] \\ NTAC 2 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def,INSERT_SUBSET,EMPTY_SUBSET]
  \\ IMP_RES_TAC lisp_inv_cs_read \\ FULL_SIMP_TAC std_ss []
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ STRIP_TAC THEN1 (POP_ASSUM MP_TAC THEN blastLib.BBLAST_TAC)
  \\ `w2w w2 >>> 2 = (n2w a):word64` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [lisp_inv_def,EVERY_DEF,MAP,CONS_11]
    \\ Q.PAT_ASSUM `ref_heap_addr s2 = w2` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
    \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_alt]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL,word_mul_n2w,
         word_add_n2w,GSYM w2n_11,w2n_lsr]
    \\ `4 * a + 1 < 4294967296` by DECIDE_TAC
    \\ `(4 * a + 1) < 18446744073709551616` by DECIDE_TAC
    \\ `a < 18446744073709551616` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ METIS_TAC []);


(* return stack *)

val stack_tm =
 [``SPEC X64_MODEL
      (zPC p * zR 0x2w r2 * stack (rbp:word64) qs)
      {(p,[0x48w; 0xFFw; 0xD2w])}
      (zPC r2 * zR 0x2w r2 * stack (rbp:word64) ((p+3w)::qs))``,
  ``SPEC X64_MODEL
      (zPC p * zR 0x2w r2 * stack (rbp:word64) qs)
      {(p,[0x48w; 0x52w])}
      (zPC (p+2w) * zR 0x2w r2 * stack (rbp:word64) (r2::qs))``,
  ``SPEC X64_MODEL
      (zPC p * stack (rbp:word64) qs * cond ~(qs = []))
      {(p,[0x48w; 0xC3w])}
      (zPC (HD qs) * stack (rbp:word64) (TL qs))``,
  ``SPEC X64_MODEL
      (zPC p * zR 0x2w r2 * stack (rbp:word64) qs * cond ~(qs = []))
      {(p,[0x48w; 0x5Aw])}
      (zPC (p+2w) * zR 0x2w (HD qs) * stack (rbp:word64) (TL qs))``,
  ``SPEC X64_MODEL
      (zPC p * stack (rbp:word64) qs)
      {(p,[0x48w; 0xE8w; w2w imm32; w2w (imm32 >>> 8); w2w (imm32 >>> 16); w2w (imm32 >>> 24)])}
      (zPC (p + n2w (6 + SIGN_EXTEND 32 64 (w2n (imm32:word32)))) *
       stack (rbp:word64) ((p + 0x6w)::qs))``]
  |> list_mk_conj
  |> (fn tm => list_mk_forall (filter (fn v => fst (dest_var v) <> "stack")
                                 (free_vars tm), tm));

val zSTACK_def = Define ` (* improve at some point... *)
  zSTACK rbp xs = SEP_EXISTS stack. stack rbp xs * cond ^stack_tm`

val zSTACK_PROPS = store_thm("zSTACK_PROPS",
  subst [hd (free_vars stack_tm)|->``zSTACK``] stack_tm,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES]
  \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS
  \\ FULL_SIMP_TAC std_ss [SPEC_MOVE_COND,STAR_ASSOC,SEP_CLAUSES]);

val lisp_inv_stack = prove(
  ``!qs2 tw3. ^LISP ==> let qs = qs2 in let tw2 = tw3 in ^LISP``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF]) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_stack",lisp_inv_stack);


(* setup symbol table *)

val bytes2words_def = tDefine "bytes2words" `
  bytes2words xs = if LENGTH xs <= 4 then [bytes2word (TAKE 4 (xs ++ [0w;0w;0w;0w]))]:word32 list else
                     bytes2word (TAKE 4 xs) :: bytes2words (DROP 4 xs)`
  (WF_REL_TAC `measure (LENGTH)` \\ SIMP_TAC std_ss [LENGTH_DROP] \\ DECIDE_TAC)

val BINIT_SYMBOLS_def = Define `BINIT_SYMBOLS = INIT_SYMBOLS ++ ["PEQUAL"]`;

val INIT_SYMBOL_ASSERTION =
  EVAL ``(FOLDR (\x y. STRLEN x + y + 1) 1 BINIT_SYMBOLS) MOD 4``
  |> concl |> dest_eq |> snd |> (fn x => if x = ``0`` then () else fail());

val (init_func_spec,init_func_def) = let
  val tm = (snd o dest_eq o concl o EVAL) ``bytes2words (symbol_list BINIT_SYMBOLS)``
  val xs = tm |> listSyntax.dest_list |> fst
  val ((th1,_,_),_) = x64_spec_byte_memory "C700"
  val ((th2,_,_),_) = x64_spec_byte_memory (x64_encodeLib.x64_encode "add r0,4")
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val (_,_,sts,_) = x64_tools
  val th = HIDE_STATUS_RULE true sts th
  val tms = find_terml (can (match_term ``((7 >< 0) (w:'a word)):word8``)) (concl th)
  val imm32 = hd (free_vars (hd tms))
  fun th_inst w = RW (map (EVAL o subst [imm32|->w]) tms) (INST [imm32|->w] th)
  val res = SPEC_COMPOSE_RULE (map th_inst xs)
  val f_tm = find_term (can (match_term ``(a =+ w) f``)) (concl res)
  val lhs_tm = ``(init_func (g:word64->word8) (r0:word64)):word64->word8``
  val def = new_definition("init_func",mk_eq(lhs_tm,f_tm))
  val res = RW [GSYM def] res
  val res = SIMP_RULE wstd_ss [w2w_def,w2n_n2w,w2n_lsr] res
  val res = RW1 [GSYM n2w_mod] res
  val res = SIMP_RULE (std_ss++SIZES_ss++sep_cond_ss) [] res
  val lhs_pre = ``(init_func_pre (dg:word64 set) (r0:word64)):bool``
  val f_pre = (hd o hyp o UNDISCH o RW [progTheory.SPEC_MOVE_COND]) res
  val pre = new_definition("init_func_pre",mk_eq(lhs_pre,f_pre))
  val res = RW [GSYM pre] res
  val def = CONJ def pre
  in (res,def) end

val _ = let
  val th = init_func_spec
  val pc = find_term (can (match_term (``zPC xx``))) (cdr (concl th))
  val post = ``let (r0,g) = (r0 + n2w (LENGTH (symbol_list BINIT_SYMBOLS)),init_func g r0) in
                 x * zR 0x0w r0 * zBYTE_MEMORY dg g * ~zS``
  val post = subst [mk_var("x",type_of pc)|->pc] post
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val lemma = prove(goal,
    SIMP_TAC std_ss [EVAL ``LENGTH (symbol_list BINIT_SYMBOLS)``,LET_DEF]
    \\ SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL])
  val th = MP th lemma
  val i = numSyntax.int_of_term (find_term numSyntax.is_numeral pc)
  val _ = add_decompiled ("init_func",th,i,SOME i)
  in () end;

val one_fun2set_IMP = prove(
  ``(one (a,x) * p) (fun2set (g,dg DIFF xs)) ==>
    p (fun2set (g,dg DIFF (a INSERT xs))) /\ a IN dg``,
  SIMP_TAC std_ss [one_fun2set,IN_DIFF]
  \\ `dg DIFF (a INSERT xs) = dg DIFF xs DELETE a` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_INSERT,IN_DELETE]
  \\ METIS_TAC []);

val DIFF_EMPTY_LEMMA = prove(
  ``fun2set (g,dg) = fun2set (g,dg DIFF {})``,
  SIMP_TAC std_ss [DIFF_EMPTY]);

val LENGTH_EQ_IMP = prove(
  ``!xs y ys.
      (LENGTH xs = LENGTH (y::ys)) ==> ?z zs. (xs = z::zs) /\ (LENGTH zs = LENGTH ys)``,
  Cases \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]);

val init_func_lemma = prove(
  ``(LENGTH xs = LENGTH (symbol_list BINIT_SYMBOLS)) ==>
    (one_byte_list a (xs ++ ys)) (fun2set(g,dg)) /\ 520 <= LENGTH ys ==>
    init_func_pre dg a /\
    (one_symbol_list a BINIT_SYMBOLS (LENGTH (symbol_list BINIT_SYMBOLS ++ ys)) (fun2set(init_func g a,dg)))``,
  SIMP_TAC std_ss [one_symbol_list_def,SEP_EXISTS_THM,cond_STAR]
  \\ REPEAT STRIP_TAC THEN1
   (POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [EVAL ``symbol_list BINIT_SYMBOLS``] \\ STRIP_TAC
    \\ NTAC 500 (IMP_RES_TAC LENGTH_EQ_IMP \\ POP_ASSUM MP_TAC
          \\ ASM_SIMP_TAC std_ss [] \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ STRIP_TAC)
    \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,LENGTH]
    \\ FULL_SIMP_TAC std_ss [one_byte_list_def,word_arith_lemma1,APPEND]
    \\ FULL_SIMP_TAC std_ss [init_func_def,INSERT_SUBSET,EMPTY_SUBSET]
    \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [DIFF_EMPTY_LEMMA]))
    \\ REPEAT (STRIP_TAC
        \\ IMP_RES_TAC one_fun2set_IMP
        \\ POP_ASSUM MP_TAC
        \\ POP_ASSUM MP_TAC
        \\ REPEAT (POP_ASSUM (K ALL_TAC)))
    \\ SIMP_TAC std_ss [])
  \\ Q.EXISTS_TAC `ys` \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 EVAL_TAC
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [EVAL ``symbol_list BINIT_SYMBOLS``] \\ STRIP_TAC
  \\ NTAC 500 (IMP_RES_TAC LENGTH_EQ_IMP \\ POP_ASSUM MP_TAC
        \\ ASM_SIMP_TAC std_ss [] \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ STRIP_TAC)
  \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,LENGTH]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_def,word_arith_lemma1,APPEND]
  \\ FULL_SIMP_TAC std_ss [init_func_def]
  \\ REPEAT STRIP_TAC \\ SEP_WRITE_TAC);

val init_func_thm = prove(
  ``1024 <= LENGTH xs ==>
    (one_byte_list a xs) (fun2set(g,dg)) ==>
    ?ys.
      init_func_pre dg a /\ 520 <= LENGTH ys /\
      (one_symbol_list a BINIT_SYMBOLS (LENGTH (symbol_list BINIT_SYMBOLS ++ ys)) (fun2set(init_func g a,dg))) /\
      (LENGTH xs = LENGTH (symbol_list BINIT_SYMBOLS ++ ys))``,
  `LENGTH (symbol_list BINIT_SYMBOLS) <= 504` by EVAL_TAC \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `LENGTH (symbol_list BINIT_SYMBOLS) <= LENGTH xs` by DECIDE_TAC
  \\ IMP_RES_TAC (Q.SPECL [`xs`,`LENGTH ys`] SPLIT_LIST_LESS_EQ)
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ `520 <= LENGTH xs2` by DECIDE_TAC
  \\ IMP_RES_TAC init_func_lemma \\ Q.EXISTS_TAC `xs2`
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]);

val ref_stack_space_SUC = prove(
  ``!n a.
      ref_stack_space a (SUC n) =
      SEP_EXISTS w. one (a - n2w (4 * n) - 4w,w) * ref_stack_space a n``,
  Induct THEN1 SIMP_TAC std_ss [ref_stack_space_def,SEP_CLAUSES,WORD_SUB_RZERO]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [Once ref_stack_space_def,SEP_CLAUSES,STAR_ASSOC]
  \\ SIMP_TAC std_ss [Once ref_stack_space_def,SEP_CLAUSES,STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,ADD1,word_arith_lemma1,LEFT_ADD_DISTRIB,
       AC ADD_COMM ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,SEP_EXISTS_THM] \\ METIS_TAC []);

val ref_stack_space_above_ADD = prove(
  ``!n m a.
      ref_stack_space_above a (n + m) =
      ref_stack_space (a + 4w + n2w (4 * n)) n *
      ref_stack_space_above (a + n2w (4 * n)) m``,
  Induct THEN1 SIMP_TAC std_ss [ref_stack_space_def,SEP_CLAUSES,WORD_ADD_0]
  \\ ASM_SIMP_TAC std_ss [ref_stack_space_SUC,WORD_ADD_0,ADD,ref_stack_space_above_def]
  \\ SIMP_TAC std_ss [word_arith_lemma1]
  \\ SIMP_TAC std_ss [word_arith_lemma4,DECIDE ``~(SUC n < n)``,
       DECIDE ``4 + 4 * SUC n - (4 * n + 4) = 4``]
  \\ FULL_SIMP_TAC (std_ss++star_ss) [ADD1,LEFT_ADD_DISTRIB,
       AC ADD_COMM ADD_ASSOC,SEP_CLAUSES]);

val lisp_init_def = Define `
  lisp_init (a1,a2,sl,sl1,e,ex,cs) (io:io_streams) (df,f,dg,g,dd,d,sp,sa1,sa_len,ds) =
     ?x xs hs.
       (ref_mem a1 (\x. H_EMP) 0 e * ref_mem a2 (\x. H_EMP) 0 e *
        ref_static sp ([a1; a2; n2w e; n2w sl; sa1; sa_len; x; ex] ++ cs ++ ds) *
       (* ref_stack_space (sp + 256w + 4w * n2w (sl + 1)) (sl + 6 + 1) *)
        ref_stack_space_above (sp + 228w) (sl + 6 + 1 + sl1))
         (fun2set (f,df)) /\
       e < 2147483648 /\ sl + 1 < 2**64 /\ 1024 <= w2n sa_len /\ sl1 < 2**30 /\
       (LENGTH cs = 10) /\ (LENGTH ds = 10) /\ (w2n (EL 3 cs) < 2**30) /\
       (a1 && 0x3w = 0x0w) /\ (a2 && 0x3w = 0x0w) /\ (sp && 0x3w = 0x0w) /\
       (w2n sa_len = LENGTH xs) /\ (one_byte_list sa1 xs) (fun2set(g,dg)) /\
       w2n sa1 + w2n sa_len < 2**64 /\ (w2n (EL 5 cs) < 2**30) /\
       (w2n (EL 5 ds) <= e) /\ (EL 7 ds = n2w sl1) /\
       (one_byte_list (EL 4 cs) hs) (fun2set(d,dd)) /\ (LENGTH hs = w2n (EL 5 cs))`;

val (mc_full_init_spec,mc_full_init_def) = basic_decompile_strings x64_tools "mc_full_init"
  (SOME (``(r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r0:word64,r1:word64,r2:word64,r3:word64,r6:word64,r7:word64,r8:word64,r9:word64,r10:word64,r11:word64,r12:word64,r13:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
      mov r3,[r7+24]
      mov r15,[r7+16]
      mov r0,[r7+32]
      mov r1,[r7+40]
      mov r2,[r7+8]
      mov r6,[r7]
      mov r8,[r7+96]
      mov r9,[r7+104]
      mov r10,[r7+88]
      add r1,r0
      insert init_func
      mov [r7+40],r0
      mov [r7+48],r1
      mov [r7+24],r2
      mov r1d,1
      xor r14,r14
      add r15,r15
      mov r0,r3
      shl r0,2
      dec r0
      add r0,256
      lea r12,[r7+r0]
      add r0,r7
      xor r11,r11
      mov [r7+152],r0
      mov [r7+160],r8
      mov [r7+168],r9
      mov [r7+216],r10
      mov [r7+208],r11
      mov [r7+192],r12
      add r7,256
      xor r2,r2
      not r2
      mov [r7+4*r3],r2d
      mov r0d,3
      mov r2,r0
      mov r8,r0
      mov r9,r0
      mov r10,r0
      mov r11,r0
      mov r12,r0
      mov r13,r0
   `);

val _ = save_thm("mc_full_init_spec",mc_full_init_spec);

val mc_full_init_blast = blastLib.BBLAST_PROVE
  ``(w2w ((w2w (w >>> 32)):word32) << 32 !! w2w ((w2w (w:word64)):word32) = w) /\
    ((63 >< 32) w = (w2w (w >>> 32)):word32) /\ ((31 >< 0) w = (w2w w):word32)``;

val mc_full_init_blast_select = blastLib.BBLAST_PROVE
  ``(w2w (w2w w1 << 32 !! (w2w:word32->word64) w2) = w2:word32) /\
    (w2w ((w2w w1 << 32 !! (w2w:word32->word64) w2) >>> 32) = w1:word32)``;

val expand_list = prove(
  ``!cs. (LENGTH cs = 10) ==>
         ?c0 c1 c2 c3 c4 c5 c6 c7 c8 c9. cs = [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9]``,
  Cases \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11,NOT_CONS_NIL]
  \\ DECIDE_TAC);

val EL_LEMMA = prove(
  ``!x y zs. EL 1 (x::y::zs) = y``,
  SIMP_TAC bool_ss [GSYM (EVAL ``SUC 0``),TL,HD,EL]);

val NO_CODE_def = Define `
  NO_CODE = BC_CODE ((\x:num.(NONE:bc_inst_type option)),0)`;

val one_fun2set_IMP = prove(
  ``(one (a,x)) (fun2set (f,df)) ==> (f a = x) /\ a IN df``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC (REWRITE_RULE [SEP_CLAUSES] (Q.SPECL [`a`,`x`,`emp`] one_fun2set)));

val mc_full_init_thm = prove(
  ``lisp_init (a1,a2,sl,sl1,e,ex,cs) (io) (df,f,dg,g,dd,d,sp,sa1,sa_len,ds) ==>
    ?w0 w1 w2 w3 w4 w5 tw0 tw1 tw2 wi we wsp bp bp2 sa2 sa3 fi gi.
      mc_full_init_pre (sp,df,f,dg,g) /\
      (mc_full_init (sp,df,f,dg,g) = (tw0,tw1,tw2,wsp,bp,sp+256w,w2w w0,w2w w1,w2w w2,w2w w3,w2w w4,w2w w5,wi,we,df,fi,dg,gi)) /\
      let (x0,x1,x2,x3,x4,x5,xs,xs1,xbp,sp,f,g,ds,code,amnt,ok) = (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",[],[],0,sp+256w,fi,gi,UPDATE_NTH 6 (sp + 256w + 4w * n2w sl - 1w) (UPDATE_NTH 8 0w (UPDATE_NTH 9 (EL 3 cs) (UPDATE_NTH 3 (EL 5 cs) (UPDATE_NTH 2 (EL 4 cs) (UPDATE_NTH 1 (sp + 256w + n2w (4 * sl) - 1w) ds))))),NO_CODE,w2n (EL 3 cs),T) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_init_def]
  \\ ONCE_REWRITE_TAC [ref_stack_space_above_ADD]
  \\ `sp + 0xE4w + 0x4w + n2w (4 * (sl + 6 + 1)) =
      sp + 0x100w + 4w * n2w (sl + 1)` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [word_arith_lemma1,word_mul_n2w,LEFT_ADD_DISTRIB]
     \\ Q.SPEC_TAC (`4*sl`,`x`) \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`3w`,`3w`,`3w`,`3w`,`3w`,`3w`,`3w`,`1w`,`3w`]
  \\ Q.LIST_EXISTS_TAC [`0w`,`n2w (2 * e)`,`n2w sl`]
  \\ Q.LIST_EXISTS_TAC [`a1`,`a2`,`sa1+n2w(LENGTH(symbol_list BINIT_SYMBOLS))`,`sa1+sa_len`]
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [mc_full_init_def,ref_full_stack_def]
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,
       word64_3232_def,word_arith_lemma1,STAR_ASSOC,INSERT_SUBSET,EMPTY_SUBSET]
  \\ FULL_SIMP_TAC std_ss [align_add_blast,n2w_and_3]
  \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [mc_full_init_blast]
  \\ SIMP_TAC std_ss [word_add_n2w,DECIDE ``2*n = n+n``]
  \\ `init_func_pre dg sa1` by METIS_TAC [init_func_thm]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,ref_stack_space_def]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC,WORD_ADD_SUB,SEP_CLAUSES,STAR_ASSOC,word_mul_n2w]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [GSYM word_mul_n2w] \\ Q.SPEC_TAC (`(n2w sl):word64`,`slw`)
      \\ Q.PAT_ASSUM `sp && 3w = 0w` MP_TAC \\ blastLib.BBLAST_TAC)
    \\ REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [SEP_EXISTS_THM,AC WORD_ADD_COMM WORD_ADD_ASSOC] \\ SEP_R_TAC)
    \\ IMP_RES_TAC expand_list
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,SEP_EXISTS_THM,
         word64_3232_def,APPEND,word_arith_lemma1,STAR_ASSOC,SEP_CLAUSES,
         ref_static_APPEND]
    \\ REPEAT (Q.PAT_ASSUM `(p_p * q_q) (fun2set (f_f,df_df))`
       (STRIP_ASSUME_TAC o MATCH_MP fun2set_STAR_IMP))
    \\ IMP_RES_TAC one_fun2set_IMP \\ FULL_SIMP_TAC std_ss [DIFF_UNION]
    \\ FULL_SIMP_TAC std_ss [IN_DIFF])
  \\ ASM_SIMP_TAC std_ss []
  \\ `n2w (4 * sl) = (n2w sl << 2):word64` by FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [lisp_inv_def,IS_TRUE_def]
  \\ NTAC 6 (Q.EXISTS_TAC `H_DATA (INR (n2w 0))`)
  \\ Q.EXISTS_TAC `\x.H_EMP`
  \\ Q.LIST_EXISTS_TAC [`0`,`[]`,`[]`,`["PEQUAL"]`,`T`]
  \\ ASM_SIMP_TAC wstd_ss [LENGTH,w2n_n2w,DECIDE ``2*n = n+n``,word_add_n2w]
  \\ `sl < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LENGTH_UPDATE_NTH]
  \\ REPEAT STRIP_TAC THEN1
   (SIMP_TAC (srw_ss()) [ok_split_heap_def,APPEND,UNION_SUBSET,
      ADDR_SET_THM,EMPTY_SUBSET,memory_ok_def,EXTENSION,NOT_IN_EMPTY]
    \\ SIMP_TAC (srw_ss()) [SUBSET_DEF,IN_DEF,D1_def,R0_def])
  THEN1
   (FULL_SIMP_TAC std_ss [EVERY_DEF,ZIP,APPEND]
    \\ FULL_SIMP_TAC std_ss [lisp_x_def] \\ Q.EXISTS_TAC `0` \\ EVAL_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [MAP,ref_heap_addr_def] \\ EVAL_TAC)
  THEN1
   (FULL_SIMP_TAC wstd_ss [align_add_blast] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [EL_CONS] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [EL_CONS] \\ EVAL_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [EL_UPDATE_NTH])
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [EL_CONS] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS,APPEND]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [EVAL ``(w2w (~0x0w:word64)):word32``]
    \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,SEP_CLAUSES,mc_full_init_blast_select]
    \\ `f (sp + 0x6Cw) = w2w (c5' >>> 32)` by SEP_READ_TAC
    \\ `f (sp + 0x68w) = w2w (c5')` by SEP_READ_TAC
    \\ `f (sp + 0x64w) = w2w (c4' >>> 32)` by SEP_READ_TAC
    \\ `f (sp + 0x60w) = w2w (c4')` by SEP_READ_TAC
    \\ `f (sp + 0x5Cw) = w2w (c3' >>> 32)` by SEP_READ_TAC
    \\ `f (sp + 0x58w) = w2w (c3')` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC,word_arith_lemma4]
    \\ `sp + 0xE4w + n2w (4 * (sl + 6 + 1)) = sp + n2w sl << 2 + 0x100w` by ALL_TAC THEN1
     (SIMP_TAC std_ss [GSYM ADD_ASSOC,LEFT_ADD_DISTRIB,WORD_MUL_LSL]
      \\ SIMP_TAC bool_ss [GSYM word_add_n2w,GSYM word_mul_n2w,DECIDE ``256 = 0x1C + 0xE4:num``]
      \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
    \\ FULL_SIMP_TAC std_ss []
    \\ SEP_WRITE_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [symtable_inv_def,GSYM BINIT_SYMBOLS_def]
    \\ IMP_RES_TAC init_func_thm
    \\ Cases_on `sa1` \\ Cases_on `sa_len`
    \\ FULL_SIMP_TAC wstd_ss [word_add_n2w,w2n_n2w]
    \\ Q.PAT_ASSUM `n' = xxx` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
    \\ NO_TAC)
  THEN1
   (IMP_RES_TAC expand_list
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS,APPEND]
    \\ SIMP_TAC std_ss [code_heap_def]
    \\ Q.LIST_EXISTS_TAC [`[]`,`hs`]
    \\ ASM_SIMP_TAC std_ss [bs2bytes_def,bc_symbols_ok_def,APPEND,WRITE_CODE_def,
         NO_CODE_def,WORD_ADD_0,EL_UPDATE_NTH,code_ptr_def]))
  |> SIMP_RULE std_ss [LET_DEF];

val mc_full_init_pre_thm = store_thm("mc_full_init_pre_thm",
  ``mc_full_init_pre (sp,df,f,dg,g) /\
    lisp_init (a1,a2,sl,sl1,e,ex,cs) io (df,f,dg,g,dd,d,sp,sa1,sa_len,ds) =
    lisp_init (a1,a2,sl,sl1,e,ex,cs) io (df,f,dg,g,dd,d,sp,sa1,sa_len,ds)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ MP_TAC mc_full_init_thm \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val _ = save_thm("mc_full_init_thm",mc_full_init_thm);


val _ = export_theory();

