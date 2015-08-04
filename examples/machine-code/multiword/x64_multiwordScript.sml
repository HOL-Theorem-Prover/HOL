
open HolKernel Parse boolLib bossLib;
val _ = new_theory "x64_multiword";

infix \\ val op \\ = op THEN;
open multiwordTheory;

open progTheory;
open decompilerLib x64_codegenLib prog_x64Lib x64_compilerLib;
open wordsTheory wordsLib addressTheory arithmeticTheory listTheory pairSyntax;
open addressTheory pairTheory set_sepTheory rich_listTheory integerTheory;
open prog_x64_extraTheory x64_encodeLib

val REV = Tactical.REVERSE;

fun x64_decompile name asm =
  decompile_strings x64_tools_64 name (assemble asm);

fun x64_decompile_no_status name asm =
  decompile_strings x64_tools_64_no_status name (assemble asm);

(*

  This file produces a single blob of x64 machine code that is able to
  do any of the following arithmetic functions over arbitrary size
  integer inputs.

    + - * div mod compare print-to-dec

  This blob of machine code takes to bignum integers as input. Each
  bignum is represented as a pointer to the payload in memory (an
  unsigned natural number) and a word containing the length of the
  payload and the sign of the integer.

    input 1: R13 hold pointer, R0 holds length with sign
    input 2: R14 hold pointer, R1 holds length with sign

  The name of the operation to perform is held in R2 and a pointer to
  free space is given in R15. Output is produced where at the location
  given in R15 and the length of this output is returned in R0 with
  sign --- the exception is comparison which returns its full result
  in R0.

*)

(*

  All of the functions in this file operate over three arrays (bignum
  payloads): two read-only that may alias and one which is the result
  of the arithemtic operation. In order to make it easy to write
  functions that operate over these we will provide an abstraction
  which makes it clear that we are operating over such arrays. We
  provide two indexes into each array.

*)

val array64_def = Define `
  (array64 a [] = emp) /\
  (array64 a (x::xs) = one (a:word64,x:word64) * array64 (a+8w) xs)`;

val bignum_mem_def = Define `
  bignum_mem p dm m xa xs ya ys za zs =
    (xa && 7w = 0w) /\ (ya && 7w = 0w) /\ (za && 7w = 0w) /\
    if xa = ya then
      (xs = ys) /\ (array64 xa xs * array64 za zs * p) (fun2set (m,dm))
    else
      (array64 xa xs * array64 ya ys * array64 za zs * p) (fun2set (m,dm))`

val zBIGNUMS_def = Define `
  zBIGNUMS (xa,xs,ya,ys,za,zs,p) =
    SEP_EXISTS dm m.
      zMEMORY64 dm m * zR 13w xa * zR 14w ya * zR 15w za *
      cond (bignum_mem p dm m xa xs ya ys za zs)`;

(* read xs, ys, zs *)

val LESS_LENGTH_IMP = prove(
  ``!xs n. n < LENGTH xs ==>
           ?ys1 ys2. (xs = ys1 ++ EL n xs :: ys2) /\ (LENGTH ys1 = n)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH] \\ METIS_TAC []);

val array64_APPEND = prove(
  ``!xs a ys.
      array64 a (xs ++ ys) = array64 a xs * array64 (a + n2w (8 * LENGTH xs)) ys``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [array64_def,SEP_CLAUSES,STAR_ASSOC,
      MULT_CLAUSES,word_arith_lemma1,AC ADD_COMM ADD_ASSOC]);

val ALIGNED64_IMP = prove(
  ``(x && 7w = 0w:word64) ==> (x + 8w * w && 7w = 0w) /\
                              (8w * w + x && 7w = 0w)``,
  blastLib.BBLAST_TAC);

val FINISH_TAC =
  FULL_SIMP_TAC std_ss [array64_APPEND,array64_def]
  \\ Cases_on `xa = ya` \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,
        AC WORD_ADD_COMM WORD_ADD_ASSOC,GSYM w2w_def,
        AC WORD_MULT_COMM WORD_MULT_ASSOC,w2w_id]
  \\ SEP_R_TAC

val x0 = ("r0",``0w:word4``,``r0:word64``);
val x1 = ("r1",``1w:word4``,``r1:word64``);
val x2 = ("r2",``2w:word4``,``r2:word64``);
val x3 = ("r3",``3w:word4``,``r3:word64``);
val x7 = ("r7",``7w:word4``,``r7:word64``);
val x8 = ("r8",``8w:word4``,``r8:word64``);
val x9 = ("r9",``9w:word4``,``r9:word64``);
val x10 = ("r10",``10w:word4``,``r10:word64``);
val x11 = ("r11",``11w:word4``,``r11:word64``);
val x12 = ("r12",``12w:word4``,``r12:word64``);

fun READ_XS (at,wt,rt) (a,w,r) = let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode ("mov "^at^",[8*"^a^"+r13]"))
  val th = SPEC_FRAME_RULE th ``zR 14w ya * zR 15w za *
                 cond (bignum_mem p df f xa xs ya ys za zs /\
                       w2n (^r:word64) < LENGTH xs)``
  val th = Q.INST [`r13`|->`xa`] th
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``let ^rt = (EL (w2n ^r) xs) in zPC (rip + 0x5w) * zR ^wt ^rt * zR ^w ^r *
      zBIGNUMS (xa,xs,ya,ys,za,zs,p)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM,LET_DEF] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`df`,`f`] \\ FULL_SIMP_TAC std_ss []
    \\ `f (8w * ^r + xa) = EL (w2n (^r:word64)) xs` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [bignum_mem_def]
    \\ IMP_RES_TAC LESS_LENGTH_IMP
    \\ Q.ABBREV_TAC `y = EL (w2n (^r:word64)) xs` \\ POP_ASSUM (K ALL_TAC)
    \\ FINISH_TAC)
  val th = MP th lemma
  val th = th |> Q.GEN `df` |> Q.GEN `f` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC rip * zR ^wt ^rt * zR ^w ^r *
      zBIGNUMS (xa,xs,ya,ys,za,zs,p) * cond (w2n ^r < LENGTH xs)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`m`,`dm`] \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [bignum_mem_def]
    \\ IMP_RES_TAC ALIGNED64_IMP \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ IMP_RES_TAC LESS_LENGTH_IMP
    \\ Q.ABBREV_TAC `y = EL (w2n (^r:word64)) xs` \\ POP_ASSUM (K ALL_TAC)
    \\ FINISH_TAC)
  val th = MP th lemma
  val th = th |> INST [``rip:word64``|->``p:word64``]
  val _ = add_compiled [SIMP_RULE std_ss [LET_DEF] th]
  in th end;

val mov_r10_xs = READ_XS x0 x10;
val mov_r10_xs = READ_XS x2 x10;
val mov_r10_xs = READ_XS x2 x11;
val mov_r11_xs = READ_XS x8 x11;
val mov_r12_xs = READ_XS x8 x12;

val r8_el_r10_xs = READ_XS x8 x10;

val _ = add_decompiled("r8_el_r10_xs",r8_el_r10_xs,5,SOME 5);

fun READ_YS (at,wt,rt) (a,w,r) = let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode ("mov "^at^",[8*"^a^"+r14]"))
  val th = SPEC_FRAME_RULE th ``zR 13w xa * zR 15w za *
                 cond (bignum_mem p df f xa xs ya ys za zs /\
                       w2n (^r:word64) < LENGTH ys)``
  val th = Q.INST [`r14`|->`ya`] th
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``let ^rt = (EL (w2n ^r) ys) in zPC (rip + 0x4w) * zR ^wt ^rt * zR ^w ^r *
      zBIGNUMS (xa,xs,ya,ys,za,zs,p)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM,LET_DEF] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`df`,`f`] \\ FULL_SIMP_TAC std_ss []
    \\ `f (8w * ^r + ya) = EL (w2n (^r:word64)) ys` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [bignum_mem_def]
    \\ IMP_RES_TAC LESS_LENGTH_IMP
    \\ Q.ABBREV_TAC `y = EL (w2n (^r:word64)) ys` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `xs = ys` \\ FULL_SIMP_TAC std_ss []
    \\ FINISH_TAC)
  val th = MP th lemma
  val th = th |> Q.GEN `df` |> Q.GEN `f` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC rip * zR ^wt ^rt * zR ^w ^r *
      zBIGNUMS (xa,xs,ya,ys,za,zs,p) * cond (w2n ^r < LENGTH ys)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`m`,`dm`] \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [bignum_mem_def]
    \\ IMP_RES_TAC ALIGNED64_IMP \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ IMP_RES_TAC LESS_LENGTH_IMP
    \\ Q.ABBREV_TAC `y = EL (w2n (^r:word64)) ys` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `xs = ys` \\ FULL_SIMP_TAC std_ss []
    \\ FINISH_TAC)
  val th = MP th lemma
  val th = th |> INST [``rip:word64``|->``p:word64``]
  val _ = add_compiled [SIMP_RULE std_ss [LET_DEF] th]
  in th end;

val mov_r10_ys = READ_YS x1 x10;
val mov_r10_ys = READ_YS x2 x10;
val mov_r11_ys = READ_YS x2 x11;
val mov_r12_ys = READ_YS x2 x12;
val mov_r11_ys = READ_YS x8 x11;
val mov_r12_ys = READ_YS x8 x12;
val mov_r11_ys = READ_YS x9 x11;
val mov_r12_ys = READ_YS x9 x12;

val r8_el_r10_ys = READ_YS x8 x10;
val r9_el_r10_ys = READ_YS x9 x10;

val _ = add_decompiled("r8_el_r10_ys",r8_el_r10_ys,4,SOME 4);
val _ = add_decompiled("r9_el_r10_ys",r9_el_r10_ys,4,SOME 4);

fun READ_ZS (at,wt,rt) (a,w,r) = let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode ("mov "^at^",[8*"^a^"+r15]"))
  val th = SPEC_FRAME_RULE th ``zR 13w xa * zR 14w ya *
                 cond (bignum_mem p df f xa xs ya ys za zs /\
                       w2n (^r:word64) < LENGTH zs)``
  val th = Q.INST [`r15`|->`za`] th
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``let ^rt = (EL (w2n ^r) zs) in zPC (rip + 0x4w) * zR ^wt ^rt * zR ^w ^r *
      zBIGNUMS (xa,xs,ya,ys,za,zs,p)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM,LET_DEF] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`df`,`f`] \\ FULL_SIMP_TAC std_ss []
    \\ `f (8w * ^r + za) = EL (w2n (^r:word64)) zs` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [bignum_mem_def]
    \\ IMP_RES_TAC LESS_LENGTH_IMP
    \\ Q.ABBREV_TAC `y = EL (w2n (^r:word64)) zs` \\ POP_ASSUM (K ALL_TAC)
    \\ FINISH_TAC)
  val th = MP th lemma
  val th = th |> Q.GEN `df` |> Q.GEN `f` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC rip * zR ^wt ^rt * zR ^w ^r *
      zBIGNUMS (xa,xs,ya,ys,za,zs,p) * cond (w2n ^r < LENGTH zs)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`m`,`dm`] \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [bignum_mem_def]
    \\ IMP_RES_TAC ALIGNED64_IMP \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ IMP_RES_TAC LESS_LENGTH_IMP
    \\ Q.ABBREV_TAC `y = EL (w2n (^r:word64)) zs` \\ POP_ASSUM (K ALL_TAC)
    \\ FINISH_TAC)
  val th = MP th lemma
  val th = th |> INST [``rip:word64``|->``p:word64``]
  val _ = add_compiled [SIMP_RULE std_ss [LET_DEF] th]
  in th end;

val mov_r10_zs = READ_ZS x0 x10;
val mov_r10_zs = READ_ZS x1 x10;
val mov_r10_zs = READ_ZS x2 x10;
val mov_r10_zs = READ_ZS x3 x10;
val mov_r10_zs = READ_ZS x3 x10;
val mov_r11_zs = READ_ZS x3 x11;
val mov_r12_zs = READ_ZS x3 x12;
val mov_r10_zs = READ_ZS x8 x10;
val mov_r11_zs = READ_ZS x8 x11;
val mov_r12_zs = READ_ZS x8 x12;
val mov_r10_zs = READ_ZS x9 x10;

val r8_el_r10_zs = READ_ZS x8 x10;
val r9_el_r10_zs = READ_ZS x9 x10;

val _ = add_decompiled("r8_el_r10_zs",r8_el_r10_zs,4,SOME 4);
val _ = add_decompiled("r9_el_r10_zs",r9_el_r10_zs,4,SOME 4);

(* write zs *)

fun WRITE_ZS (at,wt,rt) (a,w,r) = let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode ("mov [8*"^a^"+r15],"^at))
  val th = SPEC_FRAME_RULE th ``zR 13w xa * zR 14w ya *
                 cond (bignum_mem p df f xa xs ya ys za zs /\
                       w2n (^r:word64) < LENGTH zs)``
  val th = Q.INST [`r15`|->`za`] th
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``let zs = LUPDATE ^rt (w2n ^r) zs in
        zPC (rip + 0x4w) * zR ^wt ^rt * zR ^w ^r *
        zBIGNUMS (xa,xs,ya,ys,za,zs,p)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM,LET_DEF] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`df`,`(0x8w * ^r + za =+ ^rt) f`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [bignum_mem_def]
    \\ IMP_RES_TAC LESS_LENGTH_IMP
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ Q.ABBREV_TAC `y = EL (w2n ^r) zs` \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC,LUPDATE_LENGTH]
    \\ FULL_SIMP_TAC std_ss [array64_APPEND,array64_def]
    \\ `za + n2w (8 * LENGTH ys1) = 0x8w * ^r + za` by ALL_TAC THEN1
      (Cases_on `^r` \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w])
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `xa = ya` \\ FULL_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = th |> Q.GEN `df` |> Q.GEN `f` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC rip * zR ^wt ^rt * zR ^w ^r *
      zBIGNUMS (xa,xs,ya,ys,za,zs,p) * cond (w2n ^r < LENGTH zs)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`m`,`dm`] \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [bignum_mem_def]
    \\ IMP_RES_TAC ALIGNED64_IMP \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ IMP_RES_TAC LESS_LENGTH_IMP
    \\ Q.ABBREV_TAC `y = EL (w2n (^r:word64)) zs` \\ POP_ASSUM (K ALL_TAC)
    \\ FINISH_TAC)
  val th = MP th lemma
  val th = th |> INST [``rip:word64``|->``p:word64``]
  val _ = add_compiled [SIMP_RULE std_ss [LET_DEF] th]
  in th end;

val mov_zs_r10 = WRITE_ZS x0 x10;
val mov_zs_r11 = WRITE_ZS x0 x11;
val mov_zs_r12 = WRITE_ZS x0 x12;
val mov_zs_r10 = WRITE_ZS x1 x10;
val mov_zs_r11 = WRITE_ZS x1 x11;
val mov_zs_r12 = WRITE_ZS x1 x12;
val mov_zs_r10 = WRITE_ZS x2 x10;
val mov_zs_r10 = WRITE_ZS x7 x10;
val mov_zs_r10 = WRITE_ZS x8 x10;
val mov_zs_r11 = WRITE_ZS x8 x11;
val mov_zs_r12 = WRITE_ZS x8 x12;

val _ = add_decompiled("lupdate_r10_zs_with_r8",mov_zs_r10,4,SOME 4);

(* swap xs ys *)

val SWAP_XS_YS = let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode ("xchg r13,r14"))
  val th = SPEC_FRAME_RULE th ``zR 15w za * zMEMORY64 df f *
                 cond (bignum_mem p df f xa xs ya ys za zs)``
  val th = Q.INST [`r13`|->`xa`,`r14`|->`ya`] th
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zPC (rip + 0x3w) * zBIGNUMS (ya,ys,xa,xs,za,zs,p)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM,LET_DEF] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`df`,`f`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [bignum_mem_def]
    \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (std_ss++star_ss) []);
  val th = MP th lemma
  val th = th |> Q.GEN `df` |> Q.GEN `f` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC rip * zBIGNUMS (xa,xs,ya,ys,za,zs,p)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++sep_cond_ss) [zBIGNUMS_def,SEP_CLAUSES,
      cond_STAR,SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`m`,`dm`] \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = th |> INST [``rip:word64``|->``p:word64``]
  val _ = add_compiled [SIMP_RULE std_ss [LET_DEF] th]
  in th end;

val _ = print_compiler_grammar ();

(* compare *)

val (res,x64_cmp_def,x64_cmp_pre_def) = x64_compile `
  x64_cmp (r10:word64,xs:word64 list,ys:word64 list) =
    if r10 = 0w then (r10,xs,ys) else
      let r10 = r10 - 1w in
      let r8 = EL (w2n r10) xs in
      let r9 = EL (w2n r10) ys in
        if r8 = r9 then
          x64_cmp (r10,xs,ys)
        else if r8 <+ r9 then let r10 = 1w in (r10,xs,ys)
                         else let r10 = 2w in (r10,xs,ys)`

val (res,x64_compare_def,x64_compare_pre_def) = x64_compile `
  x64_compare (r10:word64,r11,xs:word64 list,ys:word64 list) =
    if r10 <+ r11 then let r10 = 1w in (r10,xs,ys) else
    if r11 <+ r10 then let r10 = 2w in (r10,xs,ys) else
      let (r10,xs,ys) = x64_cmp (r10,xs,ys) in
        (r10,xs,ys)`

val x64_header_def = Define `
  x64_header (s,xs:word64 list) = n2w (LENGTH xs * 2) + if s then 1w else 0w:word64`;

val (x64_icompare_res,x64_icompare_def,x64_icompare_pre_def) = x64_compile `
  x64_icompare (r10:word64,r11,xs:word64 list,ys:word64 list) =
    if r10 && 1w = 0w then
      if ~(r11 && 1w = 0w) then let r10 = 2w in (r10,xs,ys) else
        let r10 = r10 >>> 1 in
        let r11 = r11 >>> 1 in
        let (r10,xs,ys) = x64_compare (r10,r11,xs,ys) in
          (r10,xs,ys)
    else
      if r11 && 1w = 0w then let r10 = 1w in (r10,xs,ys) else
        let r10 = r10 >>> 1 in
        let r11 = r11 >>> 1 in
        let (r10,xs,ys) = x64_compare (r10,r11,xs,ys) in
          if r10 = 0w then (r10,xs,ys) else
            let r10 = r10 ?? 3w in (r10,xs,ys)`

val cmp2w_def = Define `
  (cmp2w NONE = 0w:word64) /\
  (cmp2w (SOME T) = 1w) /\
  (cmp2w (SOME F) = 2w)`;

val x64_cmp_thm = prove(
  ``!xs ys xs1 ys1.
      (LENGTH ys = LENGTH xs) /\ LENGTH xs < dimword(:64) ==>
      x64_cmp_pre (n2w (LENGTH xs),xs++xs1,ys++ys1) /\
      (x64_cmp (n2w (LENGTH xs),xs++xs1,ys++ys1) =
       (cmp2w (mw_cmp xs ys),xs++xs1,ys++ys1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [x64_cmp_def,Once x64_cmp_pre_def]
    \\ FULL_SIMP_TAC std_ss [Once mw_cmp_def,cmp2w_def,APPEND])
  \\ NTAC 7 STRIP_TAC
  \\ `(ys = []) \/ ?y ys2. ys = SNOC y ys2` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,ADD1]
  \\ `LENGTH xs < dimword (:64)` by (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ RES_TAC \\ ONCE_REWRITE_TAC [x64_cmp_def,x64_cmp_pre_def]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC (srw_ss()) [n2w_11,word_add_n2w,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.EL_LENGTH_APPEND]
  \\ Q.PAT_ASSUM `LENGTH ys2 = LENGTH xs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.EL_LENGTH_APPEND]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [Once mw_cmp_def]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]
  \\ SRW_TAC [] [cmp2w_def])
  |> Q.SPECL [`xs`,`ys`,`[]`,`[]`]
  |> SIMP_RULE std_ss [APPEND_NIL];

val x64_compare_thm = prove(
  ``LENGTH xs < dimword (:64) /\ LENGTH ys < dimword (:64) ==>
    x64_compare_pre (n2w (LENGTH xs),n2w (LENGTH ys),xs,ys) /\
    (x64_compare (n2w (LENGTH xs),n2w (LENGTH ys),xs,ys) =
     (cmp2w (mw_compare xs ys),xs,ys))``,
  SIMP_TAC (srw_ss()) [x64_compare_def,x64_compare_pre_def,
    n2w_11,WORD_LO,LET_DEF,mw_compare_def] \\ SRW_TAC [] [cmp2w_def]
  \\ `LENGTH xs = LENGTH ys` by DECIDE_TAC
  \\ MP_TAC x64_cmp_thm \\ FULL_SIMP_TAC (srw_ss()) []);

val x64_header_sign = prove(
  ``(x64_header (s,xs) && 1w = 0w) = ~s``,
  SIMP_TAC std_ss [x64_header_def,GSYM word_mul_n2w]
  \\ Q.SPEC_TAC (`n2w (LENGTH xs)`,`w`) \\ Cases_on `s`
  \\ FULL_SIMP_TAC std_ss [] \\ blastLib.BBLAST_TAC);

val x64_length_lemma = prove(
  ``(w * 2w + if s then 0x1w else 0x0w) >>> 1 = (w * 2w:word64) >>> 1``,
  Cases_on `s` \\ FULL_SIMP_TAC std_ss [] \\ blastLib.BBLAST_TAC);

val x64_length = prove(
  ``LENGTH xs < dimword (:63) ==>
    (x64_header (s,xs) >>> 1 = n2w (LENGTH xs))``,
  FULL_SIMP_TAC std_ss [x64_header_def,GSYM word_mul_n2w,x64_length_lemma]
  \\ SIMP_TAC std_ss [GSYM w2n_11,w2n_lsr,w2n_n2w,word_mul_n2w]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ `(LENGTH xs * 2) < 18446744073709551616` by DECIDE_TAC
  \\ `LENGTH xs < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [MULT_DIV]);

val dim63_IMP_dim64 = prove(
  ``n < dimword (:63) ==> n < dimword (:64)``,
  FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

val x64_icompare_thm = prove(
  ``LENGTH xs < dimword (:63) /\ LENGTH ys < dimword (:63) ==>
    x64_icompare_pre (x64_header (s,xs),x64_header (t,ys),xs,ys) /\
    (x64_icompare (x64_header (s,xs),x64_header (t,ys),xs,ys) =
     (cmp2w (mwi_compare (s,xs) (t,ys)),xs,ys))``,
  FULL_SIMP_TAC std_ss [x64_icompare_def,x64_icompare_pre_def,x64_header_sign,
    x64_length,LET_DEF] \\ STRIP_TAC \\ IMP_RES_TAC dim63_IMP_dim64
  \\ FULL_SIMP_TAC std_ss [x64_compare_thm,mwi_compare_def]
  \\ Cases_on `s` \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [cmp2w_def]
  \\ Cases_on `mw_compare xs ys` \\ FULL_SIMP_TAC std_ss [cmp2w_def,option_eq_def]
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,option_eq_def,n2w_11]);

(* addition *)

val (res,x64_add_loop_def) = x64_decompile_no_status "x64_add_loop" `
      inc r1
      inc r2
      add r1,0
      jmp L2
  L1: insert r8_el_r10_xs
      insert r9_el_r10_ys
      adc r8,r9
      insert lupdate_r10_zs_with_r8
      lea r10,[r10+1]
  L2: loop L1
      mov r1,r2
      mov r9,0
      jmp L4
  L3: insert r8_el_r10_xs
      adc r8,r9
      insert lupdate_r10_zs_with_r8
      lea r10,[r10+1]
  L4: loop L3
      jnb L5
      mov r8,1
      insert lupdate_r10_zs_with_r8
      lea r10,[r10+1]
  L5:`

val (x64_add_res,x64_add_def) = x64_decompile "x64_add" `
  sub r2,r1
  insert x64_add_loop`;

val _ = add_compiled [x64_add_res]

val SNOC_INTRO = prove(
  ``xs1 ++ x::(xs ++ xs2) = SNOC x xs1 ++ (xs ++ xs2)``,
  FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]);

val LUPDATE_SNOC = prove(
  ``(LENGTH zs1 = LENGTH xs1) ==>
    (LUPDATE x (LENGTH xs1) (SNOC y zs1 ++ (t ++ zs2)) =
     (SNOC x zs1 ++ (t ++ zs2)))``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,LUPDATE_LENGTH]);

val bool2num_thm = prove(``!b. bool2num b = b2n b``,Cases \\ EVAL_TAC)

val x64_add_loop1_thm = prove(
  ``!xs ys zs xs1 ys1 zs1 xs2 ys2 zs2
     z_af z_of c z_pf z_sf z_zf r8 r9.
      (LENGTH ys1 = LENGTH xs1) /\ (LENGTH zs1 = LENGTH xs1) /\
      (LENGTH ys = LENGTH xs) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH (xs1 ++ xs) + 1 < 18446744073709551616 ==>
      ?r8' r9' z_af' z_of' z_pf' z_sf' z_zf'.
        x64_add_loop1_pre (n2w (LENGTH xs + 1),r8,r9,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) /\
        (x64_add_loop1 (n2w (LENGTH xs + 1),r8,r9,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) =
          (0w,r8',r9',n2w (LENGTH (xs1++xs)),xs1 ++ xs ++ xs2,ys1 ++ ys ++ ys2,z_af',
             SOME (SND (mw_add xs ys c)),z_of',z_pf',z_sf',z_zf',
                        zs1 ++ FST (mw_add xs ys c) ++ zs2))``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_add_def]
    \\ ONCE_REWRITE_TAC [x64_add_loop_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_add_def,LET_DEF])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [x64_add_loop_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < 18446744073709551616 /\
      LENGTH xs + 1 < 18446744073709551616 /\
      LENGTH xs + 1 + 1 < 18446744073709551616` by DECIDE_TAC
  \\ `LENGTH xs1 < 18446744073709551616 /\
      LENGTH xs1 + 1 < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ Q.PAT_ASSUM `LENGTH ys1 = LENGTH xs1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ SIMP_TAC std_ss [GSYM word_sub_def,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs1 + 1 = LENGTH (SNOC h' xs1)` by
    FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1] \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LUPDATE_SNOC]
  \\ SEP_I_TAC "x64_add_loop1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_add_def,
       LET_DEF,single_add_def,bool2num_thm]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def] \\ DECIDE_TAC)

val x64_add_loop2_thm = prove(
  ``!xs zs xs1 zs1 xs2 zs2
     z_af z_of c z_pf z_sf z_zf r8.
      (LENGTH zs1 = LENGTH xs1) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH (xs1 ++ xs) + 1 < 18446744073709551616 ==>
      ?r8' r9' z_af' z_of' z_pf' z_sf' z_zf'.
        x64_add_loop2_pre (n2w (LENGTH xs + 1),r8,0w,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) /\
        (x64_add_loop2 (n2w (LENGTH xs + 1),r8,0w,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) =
          (0w,r8',r9',n2w (LENGTH (xs1++xs)),xs1 ++ xs ++ xs2,z_af',
             SOME (SND (mw_add xs (MAP (\x.0w) xs) c)),z_of',z_pf',z_sf',z_zf',
                        zs1 ++ FST (mw_add xs (MAP (\x.0w) xs) c) ++ zs2))``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_add_def]
    \\ ONCE_REWRITE_TAC [x64_add_loop_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_add_def,LET_DEF])
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [x64_add_loop_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < 18446744073709551616 /\
      LENGTH xs + 1 < 18446744073709551616 /\
      LENGTH xs + 1 + 1 < 18446744073709551616` by DECIDE_TAC
  \\ `LENGTH xs1 < 18446744073709551616 /\
      LENGTH xs1 + 1 < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ SIMP_TAC std_ss [GSYM word_sub_def,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs1 + 1 = LENGTH (SNOC h xs1)` by
    FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1] \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LUPDATE_SNOC]
  \\ SEP_I_TAC "x64_add_loop2" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_add_def,
       LET_DEF,single_add_def,bool2num_thm]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def]
  \\ DECIDE_TAC)

val x64_add_thm = prove(
  ``!xs ys zs zs2.
      LENGTH ys <= LENGTH xs /\ (LENGTH zs = LENGTH (mw_addv xs ys F)) /\
      LENGTH xs + 1 < 18446744073709551616 ==>
      ?r1' r2' r8' r9' r10'.
        x64_add_pre (n2w (LENGTH ys),n2w (LENGTH xs),0w,0w,0w,xs,ys,zs++zs2) /\
        (x64_add (n2w (LENGTH ys),n2w (LENGTH xs),0w,0w,0w,xs,ys,zs++zs2) =
          (r1',r2',r8',r9',n2w (LENGTH (mw_addv xs ys F)),xs,ys,mw_addv xs ys F ++ zs2))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC LESS_EQ_LENGTH
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,x64_add_def,LET_DEF]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ ONCE_REWRITE_TAC [x64_add_loop_def]
  \\ SIMP_TAC (srw_ss()) [LET_DEF,w2n_n2w,word_add_n2w]
  \\ `~((18446744073709551616 <= (LENGTH ys + 1) MOD 18446744073709551616))` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [DECIDE ``~(n <= m) = m < n:num``])
  \\ FULL_SIMP_TAC std_ss []
  \\ (x64_add_loop1_thm |> Q.SPECL [`xs1`,`ys`,`zs`,`[]`,`[]`,`[]`,`xs2`,`[]`,`zs2`]
      |> GEN_ALL |> MP_TAC)
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND,APPEND_NIL] \\ STRIP_TAC
  \\ Q.PAT_ASSUM `LENGTH xs1 = LENGTH ys` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [mw_addv_EQ_mw_add,LET_DEF]
  \\ `?qs1 c1. mw_add xs1 ys F = (qs1,c1)` by METIS_TAC [PAIR]
  \\ `?qs2 c2. mw_add xs2 (MAP (\x.0w) xs2) c1 = (qs2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `qs3 = if c2 then [0x1w] else []:word64 list`
  \\ `?zs1 zs3 zs4. (zs = zs1 ++ zs3 ++ zs4) /\
        (LENGTH zs1 = LENGTH xs1) /\
        (LENGTH zs3 = LENGTH xs2) /\
        (LENGTH zs4 = LENGTH qs3)` by ALL_TAC THEN1
   (IMP_RES_TAC LENGTH_mw_add
    \\ `LENGTH xs1 <= LENGTH zs` by ALL_TAC THEN1
          (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
    \\ IMP_RES_TAC LESS_EQ_LENGTH \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `xs1'` \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ `LENGTH xs2 <= LENGTH xs2'` by ALL_TAC THEN1
          (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
    \\ IMP_RES_TAC LESS_EQ_LENGTH \\ FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`xs1''`,`xs2''`]
    \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,LENGTH_APPEND]
    \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ SEP_I_TAC "x64_add_loop1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ (x64_add_loop2_thm |> Q.SPECL [`xs`,`ys`,`xs1`,`zs1`,`[]`] |> GEN_ALL
       |> SIMP_RULE std_ss [GSYM APPEND_ASSOC,APPEND_NIL] |> ASSUME_TAC)
  \\ SEP_I_TAC "x64_add_loop2" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (IMP_RES_TAC LENGTH_mw_add \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REV (Cases_on `c2`) \\ FULL_SIMP_TAC std_ss []
  THEN1 (Q.UNABBREV_TAC `qs3`
         \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND_NIL,LENGTH_APPEND])
  \\ `LENGTH xs1 + LENGTH xs2 < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC LENGTH_mw_add
  \\ Q.UNABBREV_TAC `qs3` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ Cases_on `zs4` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,word_add_n2w,ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,GSYM LENGTH_APPEND,LUPDATE_LENGTH]);

(* subtraction *)

val (res,x64_sub_loop_def) = x64_decompile_no_status "x64_sub_loop" `
      inc r1
      inc r2
      sub r8,0
      jmp L2
  L1: insert r8_el_r10_xs
      insert r9_el_r10_ys
      sbb r8,r9
      insert lupdate_r10_zs_with_r8
      lea r10,[r10+1]
  L2: loop L1
      mov r1,r2
      mov r9,0
      jmp L4
  L3: insert r8_el_r10_xs
      sbb r8,r9
      insert lupdate_r10_zs_with_r8
      lea r10,[r10+1]
  L4: loop L3`

val (x64_fix_res,x64_fix_def) = x64_decompile "x64_fix" `
  L1: test r10,r10
      je L2
      dec r10
      insert r8_el_r10_zs
      test r8,r8
      je L1
      inc r10
  L2: `

val _ = add_compiled [x64_fix_res];

val (x64_sub_res,x64_sub_def) = x64_decompile "x64_sub" `
      sub r2,r1
      insert x64_sub_loop
      insert x64_fix`

val _ = add_compiled [x64_sub_res]

val x64_fix_thm = prove(
  ``!zs zs1 r8.
      LENGTH zs < dimword(:64) ==>
      ?r8'.
        x64_fix_pre (r8,n2w (LENGTH zs),zs++zs1) /\
        (x64_fix (r8,n2w (LENGTH zs),zs++zs1) =
         (r8',n2w (LENGTH (mw_fix zs)),
          mw_fix zs ++ REPLICATE (LENGTH zs - LENGTH (mw_fix zs)) 0w ++ zs1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [x64_fix_def,mw_fix_def]
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,ADD1,GSYM word_sub_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC (DECIDE ``n + 1 < k ==> n < k:num``)
  \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,
       rich_listTheory.EL_LENGTH_APPEND,NULL,HD]
  \\ REV (Cases_on `x = 0w`) \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,REPLICATE,APPEND,
      GSYM APPEND_ASSOC,word_add_n2w] \\ DECIDE_TAC)
  \\ SEP_I_TAC "x64_fix" \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 DECIDE_TAC \\ AP_TERM_TAC
  \\ `LENGTH (mw_fix zs) <= LENGTH zs` by
      FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
  \\ `LENGTH zs + 1 - LENGTH (mw_fix zs) =
        SUC (LENGTH zs - LENGTH (mw_fix zs))` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [REPLICATE_SNOC]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND])

val sub_borrow_lemma = prove(
  ``!h:word64 h':word64 c.
     (18446744073709551616 <= b2n ~c + (w2n h' + w2n (~h))) =
      ~(w2n h' < b2n c + w2n h)``,
  Cases \\ Cases \\ Cases
  \\ `(18446744073709551615 - n) < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [b2n_def,word_1comp_n2w] \\ DECIDE_TAC);

val x64_sub_loop1_thm = prove(
  ``!xs ys zs xs1 ys1 zs1 xs2 ys2 zs2
     z_af z_of c z_pf z_sf z_zf r8 r9.
      (LENGTH ys1 = LENGTH xs1) /\ (LENGTH zs1 = LENGTH xs1) /\
      (LENGTH ys = LENGTH xs) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH (xs1 ++ xs) + 1 < 18446744073709551616 ==>
      ?r8' r9' z_af' z_of' z_pf' z_sf' z_zf'.
        x64_sub_loop1_pre (n2w (LENGTH xs + 1),r8,r9,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) /\
        (x64_sub_loop1 (n2w (LENGTH xs + 1),r8,r9,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2, ys1 ++ ys ++ ys2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) =
          (0w,r8',r9',n2w (LENGTH (xs1++xs)),xs1 ++ xs ++ xs2,ys1 ++ ys ++ ys2,z_af',
             SOME (~SND (mw_sub xs ys ~c)),z_of',z_pf',z_sf',z_zf',
                        zs1 ++ FST (mw_sub xs ys ~c) ++ zs2))``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def]
    \\ ONCE_REWRITE_TAC [x64_sub_loop_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def,LET_DEF])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [x64_sub_loop_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < 18446744073709551616 /\
      LENGTH xs + 1 < 18446744073709551616 /\
      LENGTH xs + 1 + 1 < 18446744073709551616` by DECIDE_TAC
  \\ `LENGTH xs1 < 18446744073709551616 /\
      LENGTH xs1 + 1 < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ Q.PAT_ASSUM `LENGTH ys1 = LENGTH xs1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ SIMP_TAC std_ss [GSYM word_sub_def,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs1 + 1 = LENGTH (SNOC h' xs1)` by
    FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1] \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LUPDATE_SNOC]
  \\ SEP_I_TAC "x64_sub_loop1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_sub_def,
       LET_DEF,single_sub_def,bool2num_thm,single_add_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def]
  \\ `(18446744073709551616 <= b2n ~c + (w2n h' + w2n (~h))) =
      ~(w2n h' < b2n c + w2n h)` by METIS_TAC [sub_borrow_lemma]
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]
  \\ REPEAT (STRIP_TAC THEN1 DECIDE_TAC)
  \\ Cases_on `c` \\ FULL_SIMP_TAC std_ss [b2n_def]
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ blastLib.BBLAST_TAC);

val x64_sub_loop2_thm = prove(
  ``!xs zs xs1 zs1 xs2 zs2
     z_af z_of c z_pf z_sf z_zf r8.
      (LENGTH zs1 = LENGTH xs1) /\ (LENGTH zs = LENGTH xs) /\
      LENGTH (xs1 ++ xs) + 1 < 18446744073709551616 ==>
      ?r8' r9' z_af' z_of' z_pf' z_sf' z_zf'.
        x64_sub_loop2_pre (n2w (LENGTH xs + 1),r8,0w,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) /\
        (x64_sub_loop2 (n2w (LENGTH xs + 1),r8,0w,n2w (LENGTH xs1),
          xs1 ++ xs ++ xs2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) =
          (0w,r8',r9',n2w (LENGTH (xs1++xs)),xs1 ++ xs ++ xs2,z_af',
             SOME (~SND (mw_sub xs [] ~c)),z_of',z_pf',z_sf',z_zf',
                        zs1 ++ FST (mw_sub xs [] ~c) ++ zs2))``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def]
    \\ ONCE_REWRITE_TAC [x64_sub_loop_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def,LET_DEF])
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [x64_sub_loop_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < 18446744073709551616 /\
      LENGTH xs + 1 < 18446744073709551616 /\
      LENGTH xs + 1 + 1 < 18446744073709551616` by DECIDE_TAC
  \\ `LENGTH xs1 < 18446744073709551616 /\
      LENGTH xs1 + 1 < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
        rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,TL]
  \\ SIMP_TAC std_ss [GSYM word_sub_def,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs1 + 1 = LENGTH (SNOC h xs1)` by
    FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1] \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LUPDATE_SNOC]
  \\ SEP_I_TAC "x64_sub_loop2" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_sub_def,
       LET_DEF,single_add_def,bool2num_thm,single_sub_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def]
  \\ `(18446744073709551616 <= b2n ~c + (w2n h + w2n (~(0w:word64)))) =
      ~(w2n h < b2n c + w2n (0w:word64))` by METIS_TAC [sub_borrow_lemma]
  \\ FULL_SIMP_TAC (srw_ss()) [AC ADD_COMM ADD_ASSOC]
  \\ REPEAT (STRIP_TAC THEN1 DECIDE_TAC)
  \\ Cases_on `c` \\ FULL_SIMP_TAC std_ss [b2n_def]
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ blastLib.BBLAST_TAC);

val x64_sub_thm = prove(
  ``!xs ys zs zs2.
      LENGTH ys <= LENGTH xs /\ (LENGTH zs = LENGTH xs) /\
      LENGTH xs + 1 < 18446744073709551616 ==>
      ?r1' r2' r8' r9' r10'.
        x64_sub_pre (n2w (LENGTH ys),n2w (LENGTH xs),0w,0w,0w,xs,ys,zs++zs2) /\
        (x64_sub (n2w (LENGTH ys),n2w (LENGTH xs),0w,0w,0w,xs,ys,zs++zs2) =
          (r1',r2',r8',r9',n2w (LENGTH (mw_subv xs ys)),xs,ys,
           mw_subv xs ys ++ REPLICATE (LENGTH xs - LENGTH (mw_subv xs ys)) 0w ++ zs2))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC LESS_EQ_LENGTH
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,x64_sub_def,LET_DEF]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ ONCE_REWRITE_TAC [x64_sub_loop_def]
  \\ SIMP_TAC std_ss [LET_DEF,w2n_n2w,word_add_n2w,WORD_LO]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ (x64_sub_loop1_thm |> Q.SPECL [`xs1`,`ys`,`zs`,`[]`,`[]`,`[]`,`xs2`,`[]`,`zs2`]
      |> GEN_ALL |> MP_TAC)
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND,APPEND_NIL] \\ STRIP_TAC
  \\ Q.PAT_ASSUM `LENGTH xs1 = LENGTH ys` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [mw_subv_def,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [mw_sub_APPEND]
  \\ `?qs1 c1. mw_sub xs1 ys T = (qs1,c1)` by METIS_TAC [PAIR]
  \\ `?qs2 c2. mw_sub xs2 [] c1 = (qs2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ `?zs1 zs3. (zs = zs1 ++ zs3) /\
        (LENGTH zs1 = LENGTH xs1) /\
        (LENGTH zs3 = LENGTH xs2)` by ALL_TAC THEN1
     (IMP_RES_TAC LENGTH_mw_sub \\ FULL_SIMP_TAC std_ss []
      \\ `LENGTH qs1 <= LENGTH zs` by DECIDE_TAC
      \\ IMP_RES_TAC LESS_EQ_LENGTH \\ FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`xs1'`,`xs2'`] \\ FULL_SIMP_TAC std_ss []
      \\ `LENGTH (xs1' ++ xs2') = LENGTH (qs1 ++ qs2)` by ALL_TAC
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ SEP_I_TAC "x64_sub_loop1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ (x64_sub_loop2_thm |> Q.SPECL [`xs`,`ys`,`xs1`,`zs1`,`[]`] |> GEN_ALL
       |> SIMP_RULE std_ss [GSYM APPEND_ASSOC,APPEND_NIL] |> ASSUME_TAC)
  \\ SEP_I_TAC "x64_sub_loop2" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (IMP_RES_TAC LENGTH_mw_sub \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ IMP_RES_TAC LENGTH_mw_sub
  \\ `LENGTH (xs1 ++ xs2) = LENGTH (qs1 ++ qs2)` by FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ `LENGTH (qs1 ++ qs2) < dimword (:64)` by
        (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC x64_fix_thm \\ SEP_I_TAC "x64_fix"
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,AC ADD_COMM ADD_ASSOC]);

(* integer addition *)

val (res,x64_iadd1_def,x64_iadd1_pre_def) = x64_compile `
  x64_iadd1 (r1:word64,r2:word64,xs:word64 list,ys:word64 list,xa:word64,ya:word64) =
    let r0 = 0w:word64 in
      if r1 <+ r2 then
        let (xa,xs,ya,ys) = (ya,ys,xa,xs) in
        let r0 = 1w in
          (r1,r2,r0,xs,ys,xa,ya)
      else
        let r8 = r1 in
        let r1 = r2 in
        let r2 = r8 in
          (r1,r2,r0,xs,ys,xa,ya)`

val (res,x64_iadd2_def,x64_iadd2_pre_def) = x64_compile `
  x64_iadd2 (r1:word64,r2:word64,r10:word64,r12:word64,xs,ys,xa,ya) =
    let r0 = 0w:word64 in
      if r10 = 1w then
        let (xa,xs,ya,ys) = (ya,ys,xa,xs) in
        let r12 = r12 ?? 1w in
        let r0 = 1w in
          (r1,r2,r0,r12,xs,ys,xa,ya)
      else
        let r8 = r1 in
        let r1 = r2 in
        let r2 = r8 in
          (r1,r2,r0,r12,xs:word64 list,ys:word64 list,xa:word64,ya:word64)`

val (res,x64_iadd3_def,x64_iadd3_pre_def) = x64_compile `
  x64_iadd3 (r0:word64,xs:word64 list,ys:word64 list,xa:word64,ya:word64) =
      if r0 = 0w then (xs,ys,xa,ya) else
        let (xa,xs,ya,ys) = (ya,ys,xa,xs) in
          (xs,ys,xa,ya)`

val (x64_iadd_res,x64_iadd_def,x64_iadd_pre_def) = x64_compile `
  x64_iadd (r1:word64,r2:word64,xs:word64 list,ys:word64 list,zs:word64 list,xa,ya) =
    let r10 = r1 && 1w in
    let r11 = r2 && 1w in
      if r10 = r11 then (* same sign *)
        let r1 = r1 >>> 1 in
        let r2 = r2 >>> 1 in
        let (r1,r2,r0,xs,ys,xa,ya) = x64_iadd1 (r1,r2,xs,ys,xa,ya) in
        let r8 = 0w in
        let r9 = r8 in
        let r10 = r8 in
        let (r1,r2,r8,r9,r10,xs,ys,zs) = x64_add (r1,r2,r8,r9,r10,xs,ys,zs) in
        let (xs,ys,xa,ya) = x64_iadd3 (r0,xs,ys,xa,ya) in
        let r10 = r10 << 1 in
        let r10 = r10 + r11 in
          (r10,xs,ys,zs,xa,ya)
      else (* signs differ *)
        let r12 = r10 in
        let r10 = r1 >>> 1 in
        let r11 = r2 >>> 1 in
        let (r10,xs,ys) = x64_compare (r10,r11,xs,ys) in
          if r10 = 0w then
            (r10,xs,ys,zs,xa,ya)
          else
            let (r1,r2,r0,r12,xs,ys,xa,ya) = x64_iadd2 (r1,r2,r10,r12,xs,ys,xa,ya) in
            let r8 = 0w in
            let r9 = r8 in
            let r10 = r8 in
            let r1 = r1 >>> 1 in
            let r2 = r2 >>> 1 in
            let (r1,r2,r8,r9,r10,xs,ys,zs) = x64_sub (r1,r2,r8,r9,r10,xs,ys,zs) in
            let (xs,ys,xa,ya) = x64_iadd3 (r0,xs,ys,xa,ya) in
            let r10 = r10 << 1 in
            let r10 = r10 + r12 in
              (r10,xs,ys,zs,xa,ya)`

val x64_header_AND_1 = prove(
  ``x64_header (s,xs) && 0x1w = b2w s``,
  FULL_SIMP_TAC std_ss [x64_header_def,GSYM word_mul_n2w]
  \\ Cases_on `s` \\ FULL_SIMP_TAC std_ss [b2w_def,b2n_def]
  \\ blastLib.BBLAST_TAC);

val x64_header_EQ = prove(
  ``(x64_header (s,xs) && 0x1w = x64_header (t,ys) && 0x1w) = (s = t)``,
  FULL_SIMP_TAC std_ss [x64_header_AND_1]
  \\ Cases_on `s` \\ Cases_on `t` \\ EVAL_TAC);

val b2w_NOT = prove(
  ``!s. b2w s ?? 0x1w = b2w (~s):word64``,
  Cases \\ EVAL_TAC);

val x64_iadd_thm = prove(
  ``LENGTH xs < dimword (:63) /\ LENGTH ys < dimword (:63) /\
    LENGTH xs + LENGTH ys <= LENGTH zs /\ mw_ok xs /\ mw_ok ys ==>
    ?zs1.
      x64_iadd_pre (x64_header (s,xs),x64_header (t,ys),xs,ys,zs,xa,ya) /\
      (x64_iadd (x64_header (s,xs),x64_header (t,ys),xs,ys,zs,xa,ya) =
        (x64_header (mwi_add (s,xs) (t,ys)),xs,ys,
         SND (mwi_add (s,xs) (t,ys))++zs1,xa,ya)) /\
      (LENGTH (SND (mwi_add (s,xs) (t,ys))++zs1) = LENGTH zs) ``,
  FULL_SIMP_TAC std_ss [x64_iadd_def,x64_iadd_pre_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [x64_header_EQ,mwi_add_def,x64_length]
  \\ Cases_on `s <=> t` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC dim63_IMP_dim64 THEN1
   (Cases_on `LENGTH ys <= LENGTH xs` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [x64_iadd1_def,WORD_LO,GSYM NOT_LESS,LET_DEF]
    THEN1
     (ASSUME_TAC x64_add_thm
      \\ `LENGTH (mw_addv xs ys F) <= LENGTH xs + LENGTH ys` by
            FULL_SIMP_TAC std_ss [LENGTH_mw_addv,NOT_LESS]
      \\ `LENGTH (mw_addv xs ys F) <= LENGTH zs` by DECIDE_TAC
      \\ IMP_RES_TAC LESS_EQ_LENGTH
      \\ FULL_SIMP_TAC std_ss []
      \\ SEP_I_TAC "x64_add" \\ POP_ASSUM MP_TAC
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,x64_iadd3_def,x64_iadd3_pre_def,LET_DEF]
      \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ FULL_SIMP_TAC std_ss [x64_header_AND_1]
      \\ FULL_SIMP_TAC std_ss [x64_header_def,AC MULT_COMM MULT_ASSOC]
      \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [b2w_def,b2n_def,
           AC ADD_COMM ADD_ASSOC,word_add_n2w])
    THEN1
     (ASSUME_TAC x64_add_thm
      \\ `LENGTH (mw_addv ys xs F) <= LENGTH ys + LENGTH xs` by
         (`LENGTH xs <= LENGTH ys` by DECIDE_TAC
          \\ FULL_SIMP_TAC std_ss [LENGTH_mw_addv])
      \\ `LENGTH (mw_addv ys xs F) <= LENGTH zs` by DECIDE_TAC
      \\ IMP_RES_TAC LESS_EQ_LENGTH
      \\ FULL_SIMP_TAC std_ss []
      \\ SEP_I_TAC "x64_add" \\ POP_ASSUM MP_TAC
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,x64_iadd3_def,x64_iadd3_pre_def,LET_DEF]
      \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ FULL_SIMP_TAC std_ss [x64_header_AND_1]
      \\ FULL_SIMP_TAC std_ss [x64_header_def,AC MULT_COMM MULT_ASSOC]
      \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [b2w_def,b2n_def,
           AC ADD_COMM ADD_ASSOC,word_add_n2w]))
  \\ FULL_SIMP_TAC std_ss [x64_compare_thm,mw_compare_thm]
  \\ Cases_on `mw2n ys = mw2n xs` \\ FULL_SIMP_TAC std_ss [cmp2w_def]
  THEN1 (FULL_SIMP_TAC (srw_ss()) [x64_header_def,APPEND,LENGTH])
  \\ Cases_on `mw2n xs < mw2n ys` \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,x64_iadd2_def,LET_DEF]
  THEN1
   (`LENGTH ys <= LENGTH zs` by DECIDE_TAC
    \\ IMP_RES_TAC LESS_EQ_LENGTH
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC x64_sub_thm
    \\ FULL_SIMP_TAC (srw_ss()) [x64_length]
    \\ SEP_I_TAC "x64_sub" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ `mw2n xs <= mw2n ys` by DECIDE_TAC
    \\ IMP_RES_TAC mw2n_LESS
    THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,x64_iadd3_def,
         x64_iadd3_pre_def,LET_DEF,EVAL ``1w=0w:word64``]
    \\ SIMP_TAC (srw_ss()) [GSYM APPEND_ASSOC,LENGTH_REPLICATE]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ FULL_SIMP_TAC std_ss [x64_header_AND_1]
      \\ FULL_SIMP_TAC std_ss [x64_header_def,AC MULT_COMM MULT_ASSOC]
      \\ FULL_SIMP_TAC std_ss [b2w_NOT]
      \\ Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) [b2w_def,b2n_def,
           AC ADD_COMM ADD_ASSOC,word_add_n2w])
    \\ `LENGTH (mw_subv ys xs) <= LENGTH ys` by ASM_SIMP_TAC std_ss [LENGTH_mw_subv]
    \\ DECIDE_TAC)
  THEN1
   (`LENGTH xs <= LENGTH zs` by DECIDE_TAC
    \\ IMP_RES_TAC LESS_EQ_LENGTH
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC x64_sub_thm
    \\ FULL_SIMP_TAC (srw_ss()) [x64_length]
    \\ SEP_I_TAC "x64_sub" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ `mw2n ys <= mw2n xs` by DECIDE_TAC
    \\ IMP_RES_TAC mw2n_LESS
    THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,x64_iadd3_def,x64_iadd3_pre_def,LET_DEF]
    \\ SIMP_TAC (srw_ss()) [GSYM APPEND_ASSOC,LENGTH_REPLICATE]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ FULL_SIMP_TAC std_ss [x64_header_AND_1]
      \\ FULL_SIMP_TAC std_ss [x64_header_def,AC MULT_COMM MULT_ASSOC]
      \\ FULL_SIMP_TAC std_ss [b2w_NOT]
      \\ Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) [b2w_def,b2n_def,
           AC ADD_COMM ADD_ASSOC,word_add_n2w])
    \\ `LENGTH (mw_subv xs ys) <= LENGTH xs` by ASM_SIMP_TAC std_ss [LENGTH_mw_subv]
    \\ DECIDE_TAC));


(* multiplication *)

val (x64_single_mul_add_res,
     x64_single_mul_add_def) = x64_decompile "x64_single_mul_add" `
  mul r2
  add r0,r1
  adc r2,0
  add r0,r3
  adc r2,0`

val _ = add_compiled [x64_single_mul_add_res]

val x64_single_mul_add_thm = prove(
  ``x64_single_mul_add_pre (p,k,q,s) /\
    (x64_single_mul_add (p,k,q,s) =
      let (x1,x2) = single_mul_add p q k s in (x1,k,x2,s))``,
  FULL_SIMP_TAC (srw_ss()) [x64_single_mul_add_def,LET_DEF]
  \\ Cases_on `k` \\ Cases_on `s` \\ Cases_on `p` \\ Cases_on `q`
  \\ FULL_SIMP_TAC (srw_ss()) [single_mul_add_def,LET_DEF,single_mul_def,bool2num_thm,
       mw_add_def,single_add_def,b2n_def,b2w_def,word_add_n2w,word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC, AC MULT_COMM MULT_ASSOC]
  \\ `10 < 18446744073709551616:num` by DECIDE_TAC
  \\ Q.ABBREV_TAC `k = 18446744073709551616:num` \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
  \\ `n'' * n''' DIV k + b2n (k <= n + (n'' * n''') MOD k) =
      (n + n'' * n''') DIV k` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.SPEC_TAC (`n'' * n'''`,`l`) \\ STRIP_TAC
  \\ `0 < k` by DECIDE_TAC
  \\ `(n + l) DIV k = l DIV k + (n + l MOD k) DIV k` by ALL_TAC THEN1
   (SIMP_TAC std_ss [Once ADD_COMM]
    \\ STRIP_ASSUME_TAC (SIMP_RULE bool_ss [PULL_FORALL] DIVISION
         |> Q.SPECL [`k`,`l`] |> UNDISCH_ALL |> ONCE_REWRITE_RULE [CONJ_COMM])
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
    \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC,ADD_DIV_ADD_DIV]
    \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `k <= n + l MOD k` \\ FULL_SIMP_TAC std_ss [b2n_def]
  \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ `l MOD k < k` by FULL_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC);

val (res,x64_mul_pass_def,x64_mul_pass_pre_def) = x64_compile `
  x64_mul_pass (r1:word64,r8:word64,r9:word64,r10:word64,r11:word64,ys:word64 list,zs:word64 list) =
    if r9 = r11 then
      let zs = LUPDATE r1 (w2n r10) zs in
      let r10 = r10 + 1w in
        (r1,r9,r10,ys,zs)
    else
      let r3 = EL (w2n r10) zs in
      let r2 = EL (w2n r11) ys in
      let r0 = r8 in
      let (r0,r1,r2,r3) = x64_single_mul_add (r0,r1,r2,r3) in
      let zs = LUPDATE r0 (w2n r10) zs in
      let r1 = r2 in
      let r10 = r10 + 1w in
      let r11 = r11 + 1w in
        x64_mul_pass (r1,r8,r9,r10,r11,ys,zs)`

val (res,x64_mul_def,x64_mul_pre_def) = x64_compile `
  x64_mul (r7:word64,r9,r10:word64,r12:word64,xs:word64 list,ys,zs) =
    if r7 = 0w then let r10 = r10 + r9 in (r10,xs,ys,zs) else
      let r7 = r7 - 1w in
      let r8 = EL (w2n r12) xs in
      let r12 = r12 + 1w in
      let r11 = 0w in
      let r1 = r11 in
      let (r1,r9,r10,ys,zs) = x64_mul_pass (r1,r8,r9,r10,r11,ys,zs) in
      let r10 = r10 - r9 in
        x64_mul (r7,r9,r10,r12,xs,ys,zs)`

val (res,x64_mul_zero_def,x64_mul_zero_pre_def) = x64_compile `
  x64_mul_zero (r0:word64,r10:word64,zs:word64 list) =
    if r10 = 0w then (r10,zs) else
      let r10 = r10 - 1w in
      let zs = LUPDATE r0 (w2n r10) zs in
        x64_mul_zero (r0,r10,zs)`;

val (x64_imul_res,x64_imul_def,x64_imul_pre_def) = x64_compile `
  x64_imul (r1:word64,r2:word64,xs:word64 list,ys:word64 list,zs:word64 list) =
    let r10 = 0w in
      if r1 = 0w then (r10,xs,ys,zs) else
      if r2 = 0w then (r10,xs,ys,zs) else
        let r0 = 0w in
        let r10 = r2 >>> 1 in
        let (r10,zs) = x64_mul_zero (r0,r10,zs) in
        let r10 = r1 && 1w in
        let r11 = r2 && 1w in
          if r10 = r11 then
            let r7 = r1 >>> 1 in
            let r9 = r2 >>> 1 in
            let r10 = 0w in
            let r12 = r10 in
            let (r10,xs,ys,zs) = x64_mul (r7,r9,r10,r12,xs,ys,zs) in
            let r8 = 0w in
            let (r8,r10,zs) = x64_fix (r8,r10,zs) in
            let r10 = r10 << 1 in
              (r10,xs,ys,zs)
          else
            let r7 = r1 >>> 1 in
            let r9 = r2 >>> 1 in
            let r10 = 0w in
            let r12 = r10 in
            let (r10,xs,ys,zs) = x64_mul (r7,r9,r10,r12,xs,ys,zs) in
            let r8 = 0w in
            let (r8,r10,zs) = x64_fix (r8,r10,zs) in
            let r10 = r10 << 1 in
            let r10 = r10 + 1w in
              (r10,xs,ys,zs)`;

val x64_mul_pass_thm = prove(
  ``!ys ys1 x zs k zs1 zs2 z2.
      LENGTH (ys1++ys) < dimword (:64) /\  (LENGTH zs = LENGTH ys) /\
      LENGTH (zs1++zs) < dimword (:64) ==>
      ?r1.
        x64_mul_pass_pre (k,x,n2w (LENGTH (ys1++ys)),n2w (LENGTH zs1),
                          n2w (LENGTH ys1),ys1++ys,zs1++zs++z2::zs2) /\
        (x64_mul_pass (k,x,n2w (LENGTH (ys1++ys)),n2w (LENGTH zs1),
                       n2w (LENGTH ys1),ys1++ys,zs1++zs++z2::zs2) =
           (r1,n2w (LENGTH (ys1++ys)),n2w (LENGTH (zs1++zs)+1),ys1++ys,
            zs1++(mw_mul_pass x ys zs k)++zs2))``,
  Induct \\ Cases_on `zs`
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND_NIL,mw_mul_pass_def,ADD1]
  \\ ONCE_REWRITE_TAC [x64_mul_pass_def,x64_mul_pass_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,n2w_11,w2n_n2w,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,word_add_n2w,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (DECIDE ``m+n<k ==> m < k /\ n<k:num``)
  \\ FULL_SIMP_TAC std_ss [ADD1,x64_single_mul_add_thm]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,LUPDATE_LENGTH,NULL,HD]
  \\ Cases_on `single_mul_add x h' k h` \\ FULL_SIMP_TAC std_ss [LET_DEF,TL]
  \\ ONCE_REWRITE_TAC [SNOC_INTRO |> Q.INST [`xs2`|->`[]`] |> REWRITE_RULE [APPEND_NIL]]
  \\ `((LENGTH ys1 + (LENGTH ys + 1)) = (LENGTH (SNOC h' ys1) + LENGTH ys)) /\
      ((LENGTH ys1 + 1) = (LENGTH (SNOC h' ys1))) /\
      ((LENGTH zs1 + 1) = LENGTH (SNOC q zs1))` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH_SNOC] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "x64_mul_pass" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,
       LENGTH_APPEND,LENGTH,AC ADD_COMM ADD_ASSOC] \\ DECIDE_TAC)
  |> Q.SPECL [`ys`,`[]`] |> SIMP_RULE std_ss [APPEND,LENGTH] |> GEN_ALL;

val WORD_SUB_LEMMA = prove(
  ``v + -1w * w = v - w``,
  FULL_SIMP_TAC (srw_ss()) []);

val x64_mul_thm = prove(
  ``!xs ys zs xs1 zs1 zs2.
      LENGTH (xs1 ++ xs) < dimword (:64) /\ LENGTH ys < dimword (:64) /\
      (LENGTH zs = LENGTH ys) /\ LENGTH (zs1++zs++zs2) < dimword (:64) /\
      LENGTH xs <= LENGTH zs2 /\ ys <> [] ==>
      ?zs3.
        x64_mul_pre (n2w (LENGTH xs),n2w (LENGTH ys),n2w (LENGTH zs1),n2w (LENGTH xs1),
                 xs1 ++ xs,ys,zs1 ++ zs ++ zs2) /\
       (x64_mul (n2w (LENGTH xs),n2w (LENGTH ys),n2w (LENGTH zs1),n2w (LENGTH xs1),
                 xs1 ++ xs,ys,zs1 ++ zs ++ zs2) =
          (n2w (LENGTH (zs1 ++ mw_mul xs ys zs)),xs1++xs,ys,zs1 ++ mw_mul xs ys zs ++ zs3)) /\
       (LENGTH (zs1 ++ zs ++ zs2) = LENGTH (zs1 ++ mw_mul xs ys zs ++ zs3))``,
  Induct \\ ONCE_REWRITE_TAC [x64_mul_def,x64_mul_pre_def]
  \\ FULL_SIMP_TAC std_ss [LENGTH,mw_mul_def,APPEND_NIL,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,word_add_n2w]
  THEN1 (METIS_TAC [])
  \\ NTAC 7 STRIP_TAC
  \\ IMP_RES_TAC (DECIDE ``m+n<k ==> m < k /\ n<k:num``)
  \\ IMP_RES_TAC (DECIDE ``SUC n < k ==> n < k``)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,LUPDATE_LENGTH,NULL,HD]
  \\ FULL_SIMP_TAC std_ss [GSYM word_sub_def,ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ Cases_on `zs2` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ ASSUME_TAC x64_mul_pass_thm
  \\ SEP_I_TAC "x64_mul_pass" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH (mw_mul_pass h ys zs 0x0w) = LENGTH ys + 1` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH_mw_mul_pass])
  \\ Cases_on `mw_mul_pass h ys zs 0x0w`
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ `n2w (LENGTH (zs1 ++ zs:word64 list) + 1) + -0x1w * n2w (LENGTH (ys:word64 list)) =
      n2w (LENGTH (SNOC h'' zs1)):word64` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [WORD_SUB_LEMMA,LENGTH,LENGTH_APPEND]
    \\ `LENGTH zs1 + LENGTH ys + 1 = (LENGTH zs1 + 1) + LENGTH ys` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,LENGTH_SNOC,ADD1])
  \\ `n2w (LENGTH xs1) + 0x1w = n2w (LENGTH (SNOC h xs1)):word64` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [word_add_n2w,LENGTH_SNOC,ADD1])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ ONCE_REWRITE_TAC [SNOC_INTRO |> Q.INST [`xs2`|->`[]`] |> REWRITE_RULE [APPEND_NIL]]
  \\ SEP_I_TAC "x64_mul" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ DECIDE_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [word_add_n2w,TL,LENGTH_SNOC,ADD1,HD,AC ADD_COMM ADD_ASSOC]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_mw_mul] \\ STRIP_TAC
  \\ Q.EXISTS_TAC `zs3` \\ DECIDE_TAC)
  |> Q.SPECL [`xs`,`ys`,`zs`,`[]`,`[]`,`zs2`]
  |> SIMP_RULE std_ss [LENGTH,APPEND] |> GEN_ALL;

val x64_mul_zero_thm = prove(
  ``!zs zs1.
      LENGTH zs < dimword(:64) ==>
        x64_mul_zero_pre (0w,n2w (LENGTH zs),zs++zs1) /\
        (x64_mul_zero (0w,n2w (LENGTH zs),zs++zs1) = (0w,MAP (\x.0w) zs ++ zs1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  \\ NTAC 3 STRIP_TAC
  \\ ONCE_REWRITE_TAC [x64_mul_zero_def,x64_mul_zero_pre_def]
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,LET_DEF]
  \\ NTAC 3 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,ADD1,GSYM word_sub_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC (DECIDE ``n+1<k ==> n<k:num``)
  \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,
       APPEND,LUPDATE_LENGTH,MAP_APPEND,MAP] \\ DECIDE_TAC);

val MAP_EQ_MAP_EQ = prove(
  ``!xs ys. (MAP (\x.0w) xs = MAP (\x.0w) ys) = (LENGTH xs = LENGTH ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []);

val x64_imul_thm = prove(
  ``((x64_header (s,xs) = 0w) = (xs = [])) /\
    ((x64_header (t,ys) = 0w) = (ys = [])) /\
    LENGTH xs < dimword (:63) /\ LENGTH ys < dimword (:63) /\
    LENGTH xs + LENGTH ys <= LENGTH zs /\ LENGTH zs < dimword (:63) ==>
    ?zs1.
      x64_imul_pre (x64_header (s,xs),x64_header (t,ys),xs,ys,zs) /\
      (x64_imul (x64_header (s,xs),x64_header (t,ys),xs,ys,zs) =
        (x64_header (mwi_mul (s,xs) (t,ys)),xs,ys,
         SND (mwi_mul (s,xs) (t,ys))++zs1)) /\
      (LENGTH (SND (mwi_mul (s,xs) (t,ys))++zs1) = LENGTH zs) ``,
  FULL_SIMP_TAC std_ss [x64_imul_def,x64_imul_pre_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [x64_header_EQ,mwi_mul_def,x64_length]
  \\ Cases_on `xs = []` \\ FULL_SIMP_TAC std_ss [APPEND]
  THEN1 (REPEAT STRIP_TAC \\ EVAL_TAC)
  \\ Cases_on `ys = []` \\ FULL_SIMP_TAC std_ss [APPEND]
  THEN1 (REPEAT STRIP_TAC \\ EVAL_TAC)
  \\ REPEAT STRIP_TAC
  \\ `LENGTH ys <= LENGTH zs` by DECIDE_TAC
  \\ `?qs1 qs2. (zs = qs1 ++ qs2) /\ (LENGTH ys = LENGTH qs1)` by
       METIS_TAC [LESS_EQ_LENGTH]
  \\ `LENGTH qs1 < dimword (:64)` by (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [x64_mul_zero_thm]
  \\ ASSUME_TAC x64_mul_thm
  \\ Q.PAT_ASSUM `LENGTH ys = LENGTH qs1` (ASSUME_TAC o GSYM)
  \\ `MAP (\x. 0x0w:word64) qs1 = MAP (\x. 0x0w) ys` by
       ASM_SIMP_TAC std_ss [MAP_EQ_MAP_EQ]
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "x64_mul" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH qs1 < dimword (:64)` by (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ `LENGTH (mw_mul xs ys (MAP (\x. 0x0w) ys)) < dimword (:64)` by ALL_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [LENGTH_mw_mul,LENGTH_MAP] \\ DECIDE_TAC)
  \\ ASSUME_TAC x64_fix_thm \\ SEP_I_TAC "x64_fix" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `s = t` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [x64_header_def,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_REPLICATE,WORD_MUL_LSL,word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC]
  \\ Q.ABBREV_TAC `ts = mw_mul xs ys (MAP (\x. 0x0w) ys)`
  \\ `LENGTH (mw_fix ts) <= LENGTH ts` by FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
  \\ DECIDE_TAC);


(* simple div xs into zs and zs into zs *)

val (x64_single_div_res,x64_single_div_def) = x64_decompile "x64_single_div" `
  div r9`

val _ = add_compiled [x64_single_div_res]

val MULT_LEMMA_LEMMA = prove(
  ``!m n. l < k /\ l + k * m < k + k * n ==> m <= n:num``,
  Induct \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
  THEN1 (REPEAT STRIP_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val MULT_LEMMA = prove(
  ``l < k ==> (l + k * m < k + k * n = m <= n:num)``,
  REPEAT STRIP_TAC \\ REV EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (SUFF_TAC ``k * m <= k * n:num`` \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
    \\ MATCH_MP_TAC LESS_MONO_MULT2 \\ FULL_SIMP_TAC std_ss [])
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ IMP_RES_TAC MULT_LEMMA_LEMMA \\ DECIDE_TAC);

val x64_single_div_thm = prove(
  ``(x64_single_div_pre (x2,x1,y) = x1 <+ y) /\
    (x64_single_div (x2,x1,y) = let (q,r) = single_div x1 x2 y in (q,r,y))``,
  FULL_SIMP_TAC (srw_ss()) [x64_single_div_def,single_div_def,LET_DEF]
  \\ Cases_on `y` \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO,DIV_LT_X]
  \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
  \\ SIMP_TAC std_ss [Once ADD_COMM] \\ SIMP_TAC std_ss [Once MULT_COMM]
  \\ `w2n x2 < 18446744073709551616` by ALL_TAC THEN1
   (ASSUME_TAC (w2n_lt |> INST_TYPE [``:'a``|->``:64``] |> Q.SPEC `x2`)
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [MULT_LEMMA]
  \\ DECIDE_TAC);

val (res,x64_simple_div_def,x64_simple_div_pre_def) = x64_compile `
  x64_simple_div (r2:word64,r9:word64,r10:word64,xs:word64 list,zs:word64 list) =
    if r10 = 0w then (r2,r9,r10,xs,zs) else
      let r10 = r10 - 1w in
      let r0 = EL (w2n r10) xs in
      let (r0,r2,r9) = x64_single_div (r0,r2,r9) in
      let zs = LUPDATE r0 (w2n r10) zs in
        x64_simple_div (r2,r9,r10,xs,zs)`

val (res,x64_simple_div1_def,x64_simple_div1_pre_def) = x64_compile `
  x64_simple_div1 (r2:word64,r9:word64,r10:word64,zs:word64 list) =
    if r10 = 0w then (r2,r9,r10,zs) else
      let r10 = r10 - 1w in
      let r0 = EL (w2n r10) zs in
      let (r0,r2,r9) = x64_single_div (r0,r2,r9) in
      let zs = LUPDATE r0 (w2n r10) zs in
        x64_simple_div1 (r2,r9,r10,zs)`

val x64_simple_div_thm = prove(
  ``!xs xs1 zs zs1 r2 r9 qs r.
      LENGTH xs < dimword(:64) /\ (LENGTH zs = LENGTH xs) /\
      (mw_simple_div r2 (REVERSE xs) r9 = (qs,r,T)) ==>
      x64_simple_div_pre (r2,r9,n2w (LENGTH xs),xs++xs1,zs++zs1) /\
      (x64_simple_div (r2,r9,n2w (LENGTH xs),xs++xs1,zs++zs1) =
         (r,r9,0w,xs++xs1,REVERSE qs++zs1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH,Once x64_simple_div_pre_def,
         Once x64_simple_div_def,REVERSE,mw_simple_div_def]
    \\ Q.SPEC_TAC (`qs`,`qs`)
    \\ Cases_on `zs` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,ADD1])
  \\ NTAC 11 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [REVERSE_SNOC,mw_simple_div_def,LET_DEF]
  \\ `(zs = []) \/ ?z zs2. zs = SNOC z zs2` by METIS_TAC [SNOC_CASES]
  THEN1 (FULL_SIMP_TAC (srw_ss()) [LENGTH])
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC]
  \\ SIMP_TAC std_ss [LENGTH,Once x64_simple_div_pre_def,
         Once x64_simple_div_def,REVERSE,mw_simple_div_def]
  \\ FULL_SIMP_TAC (srw_ss()) [n2w_11,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,GSYM word_sub_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC (DECIDE ``n+1<k ==> n<k:num``)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,NULL,HD]
  \\ Q.PAT_ASSUM `LENGTH zs2 = LENGTH xs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH,x64_single_div_thm]
  \\ `?q1 r1. single_div r2 x r9 = (q1,r1)` by METIS_TAC [PAIR]
  \\ `?qs2 r2 c2. mw_simple_div r1 (REVERSE xs) r9 = (qs2,r2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Q.PAT_ASSUM `q1::qs2 = qs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [REVERSE,SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ DECIDE_TAC);

val x64_simple_div1_thm = prove(
  ``!zs zs1 r2 r9 qs r.
      LENGTH zs < dimword(:64) /\
      (mw_simple_div r2 (REVERSE zs) r9 = (qs,r,T)) ==>
      x64_simple_div1_pre (r2,r9,n2w (LENGTH zs),zs++zs1) /\
      (x64_simple_div1 (r2,r9,n2w (LENGTH zs),zs++zs1) =
         (r,r9,0w,REVERSE qs++zs1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH,Once x64_simple_div1_pre_def,
         Once x64_simple_div1_def,REVERSE,mw_simple_div_def]
    \\ Q.SPEC_TAC (`qs`,`qs`) \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,ADD1])
  \\ NTAC 9 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [REVERSE_SNOC,mw_simple_div_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC]
  \\ SIMP_TAC std_ss [LENGTH,Once x64_simple_div1_pre_def,
         Once x64_simple_div1_def,REVERSE,mw_simple_div_def]
  \\ FULL_SIMP_TAC (srw_ss()) [n2w_11,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,GSYM word_sub_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC (DECIDE ``n+1<k ==> n<k:num``)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,NULL,HD]
  \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH,x64_single_div_thm]
  \\ `?q1 r1. single_div r2 x r9 = (q1,r1)` by METIS_TAC [PAIR]
  \\ `?qs2 r2 c2. mw_simple_div r1 (REVERSE zs) r9 = (qs2,r2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Q.PAT_ASSUM `q1::qs2 = qs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [REVERSE,SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ DECIDE_TAC);

(* mw_div -- calc_d *)

val (res,x64_calc_d_def,x64_calc_d_pre_def) = x64_compile `
  x64_calc_d (r1:word64,r2:word64) =
    let r0 = r1 + r1 in
    let r0 = r0 >>> 1 in
      if r0 <> r1 then r2 else
        let r1 = r1 + r1 in
        let r2 = r2 + r2 in
          x64_calc_d (r1,r2)`

val x64_calc_d_thm = prove(
  ``!v1 d.
      (\(v1,d).
        (v1 <> 0w) ==>
        x64_calc_d_pre (v1,d) /\
        (x64_calc_d (v1,d) = calc_d (v1,d))) (v1,d)``,
  MATCH_MP_TAC (calc_d_ind |> INST_TYPE [alpha|->``:64``])
  \\ FULL_SIMP_TAC std_ss [] \\ NTAC 4 STRIP_TAC
  \\ ONCE_REWRITE_TAC [x64_calc_d_pre_def,x64_calc_d_def,calc_d_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Tactical.REVERSE (Cases_on `v1 = (v1 + v1) >>> 1`)
  \\ `(v1 = (v1 + v1) >>> 1) <=> ~word_msb v1` by
        (NTAC 2 (POP_ASSUM MP_TAC) \\ blastLib.BBLAST_TAC)
  \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  \\ FULL_SIMP_TAC std_ss [GSYM addressTheory.WORD_TIMES2,
       AC WORD_MULT_ASSOC WORD_MULT_COMM]
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ REPEAT (POP_ASSUM MP_TAC) \\ blastLib.BBLAST_TAC)
  |> SIMP_RULE std_ss [];

(* mw_div -- mw_div_guess *)

val (x64_single_mul_res,
     x64_single_mul_def) = x64_decompile "x64_single_mul" `
  mul r2
  add r0,r1
  adc r2,0`

val _ = add_compiled [x64_single_mul_res]

val single_mul_add_thm  = prove(
  ``single_mul_add p q k s =
      (let (r0,r1,r2,r3) = x64_single_mul_add (p,k,q,s) in
         (r0,r2))``,
  SIMP_TAC std_ss [x64_single_mul_add_thm]
  \\ Q.SPEC_TAC (`single_mul_add p q k s`,`w`)
  \\ FULL_SIMP_TAC std_ss [FORALL_PROD,LET_DEF]);

val x64_single_mul_thm = prove(
  ``x64_single_mul_pre (p,k,q) /\
    (x64_single_mul (p,k,q) =
      let (x1,x2) = single_mul_add p q k 0w in (x1,k,x2))``,
  SIMP_TAC (srw_ss()) [single_mul_add_thm,x64_single_mul_def,LET_DEF,
    x64_single_mul_add_def] \\ SIMP_TAC std_ss [GSYM (EVAL ``dimword (:64)``)]
  \\ SIMP_TAC std_ss [GSYM NOT_LESS,w2n_lt,EVAL ``bool2num F``,WORD_ADD_0]);

val (res,x64_mul_by_single2_def,x64_mul_by_single2_pre_def) = x64_compile `
  x64_mul_by_single2 (r6:word64,r7:word64,r8:word64) =
    let r0 = r6 in
    let r1 = 0w in
    let r2 = r7 in
    let (r0,r1,r2) = x64_single_mul (r0,r1,r2) in
    let r12 = r0 in
    let r0 = r6 in
    let r1 = r2 in
    let r2 = r8 in
    let (r0,r1,r2) = x64_single_mul (r0,r1,r2) in
    let r3 = r2 in
    let r2 = r0 in
    let r1 = r12 in
      (r1,r2,r3,r6,r7,r8)`

val x64_mul_by_single2_thm = prove(
  ``!r6 r7 r8.
      ?r1 r2 r3.
        x64_mul_by_single2_pre (r6,r7,r8) /\
        (x64_mul_by_single2 (r6,r7,r8) = (r1,r2,r3,r6,r7,r8)) /\
        (mw_mul_by_single r6 [r7; r8] = [r1; r2; r3])``,
  SIMP_TAC std_ss [mw_mul_by_single_def,LENGTH,mw_mul_pass_def,x64_single_mul_thm,
    k2mw_def,HD,TL,x64_mul_by_single2_def,EVAL ``(k2mw 2 0):word64 list``,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ SIMP_TAC std_ss [x64_mul_by_single2_pre_def,LET_DEF,x64_single_mul_add_def]
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ SIMP_TAC std_ss [x64_mul_by_single2_pre_def,LET_DEF,x64_single_mul_add_def]
  \\ SIMP_TAC std_ss [x64_single_mul_thm] \\ EVAL_TAC);

val (res,x64_cmp3_def,x64_cmp3_pre_def) = x64_compile `
  x64_cmp3 (r1:word64,r2,r3,r9:word64,r10:word64,r11:word64) =
    let r0 = 1w:word64 in
      if r3 <> r11 then
        if r11 <+ r3 then (r0,r1,r2,r3,r9,r10,r11) else
          let r0 = 0w in (r0,r1,r2,r3,r9,r10,r11) else
      if r2 <> r10 then
        if r10 <+ r2 then (r0,r1,r2,r3,r9,r10,r11) else
          let r0 = 0w in (r0,r1,r2,r3,r9,r10,r11) else
      if r1 <> r9 then
        if r9 <+ r1 then (r0,r1,r2,r3,r9,r10,r11) else
          let r0 = 0w in (r0,r1,r2,r3,r9,r10,r11) else
      let r0 = 0w in (r0,r1,r2,r3,r9,r10,r11)`

val x64_cmp3_thm = prove(
  ``x64_cmp3_pre (r1,r2,r3,r9,r10,r11) /\
    (x64_cmp3 (r1,r2,r3,r9,r10,r11) =
      (if mw_cmp [r9;r10;r11] [r1;r2;r3] = SOME T then 1w else 0w,
       r1,r2,r3,r9,r10,r11))``,
  NTAC 5 (ONCE_REWRITE_TAC [mw_cmp_def])
  \\ SIMP_TAC (srw_ss()) [x64_cmp3_def,x64_cmp3_pre_def,LET_DEF]
  \\ Tactical.REVERSE (Cases_on `r3 = r11`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []
  \\ Tactical.REVERSE (Cases_on `r2 = r10`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []
  \\ Tactical.REVERSE (Cases_on `r1 = r9`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []);

val (res,x64_cmp_mul2_def,x64_cmp_mul2_pre_def) = x64_compile `
  x64_cmp_mul2 (r6,r7,r8,r9,r10,r11) =
    let (r1,r2,r3,r6,r7,r8) = x64_mul_by_single2 (r6,r7,r8) in
    let (r0,r1,r2,r3,r9,r10,r11) = x64_cmp3 (r1,r2,r3,r9,r10,r11) in
      (r0,r6,r7,r8,r9,r10,r11)`

val x64_cmp_mul2_thm = prove(
  ``x64_cmp_mul2_pre (r6,r7,r8,r9,r10,r11) /\
    (x64_cmp_mul2 (r6,r7,r8,r9,r10,r11) =
      ((if mw_cmp [r9;r10;r11] (mw_mul_by_single r6 [r7; r8]) = SOME T
            then 1w else 0w),r6,r7,r8,r9,r10,r11))``,
  SIMP_TAC std_ss [x64_cmp_mul2_pre_def,x64_cmp_mul2_def]
  \\ STRIP_ASSUME_TAC (x64_mul_by_single2_thm |> SPEC_ALL)
  \\ FULL_SIMP_TAC std_ss [LET_DEF,x64_cmp3_thm]);

val (res,x64_sub1_def,x64_sub1_pre_def) = x64_compile `
  x64_sub1 (r6:word64) =
    if r6 = 0w then r6 else let r6 = r6 - 1w in r6`

val x64_sub1_thm = prove(
  ``!r6. x64_sub1_pre r6 /\ (x64_sub1 r6 = n2w (w2n r6 - 1))``,
  Cases \\ ASM_SIMP_TAC (srw_ss()) [x64_sub1_pre_def,x64_sub1_def]
  \\ Cases_on `n = 0` \\ FULL_SIMP_TAC std_ss [LET_DEF,GSYM word_sub_def]
  \\ `~(n < 1)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [addressTheory.word_arith_lemma2]);

val (res,x64_cmp2_def,x64_cmp2_pre_def) = x64_compile `
  x64_cmp2 (r0:word64,r2,r10:word64,r11:word64) =
    let r1 = 1w:word64 in
      if r2 <> r11 then
        if r11 <+ r2 then (r0,r1,r2,r10,r11) else
          let r1 = 0w in (r0,r1,r2,r10,r11) else
      if r0 <> r10 then
        if r10 <+ r0 then (r0,r1,r2,r10,r11) else
          let r1 = 0w in (r0,r1,r2,r10,r11) else
      let r1 = 0w in (r0,r1,r2,r10,r11)`

val x64_cmp2_thm = prove(
  ``x64_cmp2_pre (r0,r2,r10,r11) /\
    (x64_cmp2 (r0,r2,r10,r11) =
      (r0,if mw_cmp [r10;r11] [r0;r2] = SOME T then 1w else 0w,
       r2,r10,r11))``,
  NTAC 5 (ONCE_REWRITE_TAC [mw_cmp_def])
  \\ SIMP_TAC (srw_ss()) [x64_cmp2_def,x64_cmp2_pre_def,LET_DEF]
  \\ Tactical.REVERSE (Cases_on `r2 = r11`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []
  \\ Tactical.REVERSE (Cases_on `r0 = r10`)
  \\ FULL_SIMP_TAC std_ss [] THEN1 SRW_TAC [] []);

val (res,x64_div_test_def,x64_div_test_pre_def) = x64_compile `
  x64_div_test (r6,r7,r8,r9,r10,r11) =
    let (r0,r6,r7,r8,r9,r10,r11) = x64_cmp_mul2 (r6,r7,r8,r9,r10,r11) in
      if r0 <> 0w then
        let r6 = x64_sub1 r6 in
        let r0 = r6 in
        let r1 = 0w in
        let r2 = r8 in
        let r3 = r1 in
        let (r0,r1,r2,r3) = x64_single_mul_add (r0,r1,r2,r3) in
        let r2 = r2 + 1w in
        let (r0,r1,r2,r10,r11) = x64_cmp2 (r0,r2,r10,r11) in
          if r1 <> 0w then
            x64_div_test (r6,r7,r8,r9,r10,r11)
          else (r6,r7,r8,r9,r10,r11)
      else
        (r6,r7,r8,r9,r10,r11)`

val single_mul_thm = prove(
  ``single_mul_add x y 0w 0w = single_mul x y 0w``,
  SIMP_TAC (srw_ss()) [single_mul_add_def,single_mul_def,LET_DEF,
    mw_add_def,single_add_def,b2n_def,b2w_def,GSYM NOT_LESS,w2n_lt]);

val mw_add_0_1 = prove(
  ``(FST (mw_add [r0;r2] [0w;1w] F) = [r0;r2+1w])``,
  SIMP_TAC (srw_ss()) [mw_add_def,HD,TL,single_add_def,b2w_def,
    LET_DEF,EVAL ``b2n F``,GSYM NOT_LESS,w2n_lt]);

val x64_div_test_thm = prove(
  ``!q u1 u2 u3 v1 v2.
      x64_div_test_pre (q,v2,v1,u3,u2,u1) /\
      (x64_div_test (q,v2,v1,u3,u2,u1) =
         (mw_div_test q u1 u2 u3 v1 v2,v2,v1,u3,u2,u1))``,
  HO_MATCH_MP_TAC mw_div_test_ind \\ NTAC 7 STRIP_TAC
  \\ ONCE_REWRITE_TAC [x64_div_test_def,x64_div_test_pre_def,mw_div_test_def]
  \\ SIMP_TAC std_ss [x64_cmp_mul2_thm]
  \\ Cases_on `mw_cmp [u3; u2; u1] (mw_mul_by_single q [v2; v1]) = SOME T`
  \\ ASM_SIMP_TAC std_ss [LET_DEF,EVAL ``0w = 1w:word64``,x64_sub1_thm]
  \\ FULL_SIMP_TAC std_ss [x64_single_mul_add_thm,GSYM single_mul_thm]
  \\ Cases_on `single_mul_add (n2w (w2n q - 1)) v1 0x0w 0x0w`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,x64_cmp2_thm]
  \\ Q.MATCH_ASSUM_RENAME_TAC
       `single_mul_add (n2w (w2n q - 1)) v1 0x0w 0x0w = (q1,q2)`
  \\ FULL_SIMP_TAC std_ss [mw_add_0_1]
  \\ Cases_on `mw_cmp [u2; u1] [q1; q2 + 0x1w] = SOME T`
  \\ FULL_SIMP_TAC std_ss [EVAL ``0w = 1w:word64``]);

val (x64_div_r1_res,x64_div_r1_def) = x64_decompile "x64_div_r1" `
      cmp r2 r1
      jb L
      xor r0,r0
      not r0
      jmp EXIT
L:    div r1
EXIT: `;

val _ = add_compiled [x64_div_r1_res]

val x64_div_r1_thm = prove(
  ``x64_div_r1 (r0,r1,r2) =
      if r2 <+ r1 then
        (FST (single_div r2 r0 r1),r1,SND (single_div r2 r0 r1))
      else (~0w,r1,r2)``,
  SIMP_TAC (srw_ss()) [x64_div_r1_def,single_div_def,LET_DEF]);

val (res,x64_div_guess_def,x64_div_guess_pre_def) = x64_compile `
  x64_div_guess (r7,r8,r9,r10,r11) =
    let r0 = r10 in
    let r1 = r8 in
    let r2 = r11 in
    let (r0,r1,r2) = x64_div_r1 (r0,r1,r2) in
    let r6 = r0 in
    let (r6,r7,r8,r9,r10,r11) = x64_div_test (r6,r7,r8,r9,r10,r11) in
      (r6,r7,r8,r9,r10,r11)`

val x64_div_guess_thm = prove(
  ``!q u1 u2 u3 v1 v2.
      (x64_div_guess_pre (v2,v1,u3,u2,u1) <=>
         (u1 <+ v1 ==> v1 <> 0w))  /\
      (x64_div_guess (v2,v1,u3,u2,u1) =
         (mw_div_guess (u1::u2::u3::us) (v1::v2::vs),v2,v1,u3,u2,u1))``,
  SIMP_TAC (srw_ss()) [x64_div_guess_def,x64_div_guess_pre_def,
    x64_div_test_thm, mw_div_guess_def,HD,TL,x64_div_r1_thm,LET_DEF]
  \\ SIMP_TAC std_ss [x64_div_r1_def,LET_DEF,WORD_LO]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `w2n u1 < w2n v1` \\ FULL_SIMP_TAC std_ss [EVAL ``-1w:word64``]
  \\ Cases_on `v1 = 0w` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `v1` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `0 < n` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [DIV_LT_X]
  \\ Cases_on `u1` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `u2` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ DECIDE_TAC);

(* mw_div -- mw_div_adjust *)

(*

 r1 -- k1
 r6 -- x1, i.e. d
 r7 -- x2
 r8 -- accumulated result
 r9 -- length of ys
 r10 -- points into zs
 r11 -- points into ys
 r12 -- k2

*)

val (res,x64_adj_cmp_def,x64_adj_cmp_pre_def) = x64_compile `
  x64_adj_cmp (r0:word64,r3:word64,r8:word64) =
    if r0 = r3 then (r0,r3,r8) else
      let r8 = 1w in
        if r3 <+ r0 then (r0,r3,r8)
        else let r8 = 0w in (r0,r3,r8)`

val (res,x64_adjust_aux_def,x64_adjust_aux_pre_def) = x64_compile `
  x64_adjust_aux (r1,r6,r7,r8,r9,r10:word64,r11:word64,r12,ys:word64 list,zs) =
    if r9 = r11 then
      let r0 = r12 in
      let r3 = EL (w2n r10) zs in
      let r10 = r10 + 1w in
      let (r0,r3,r8) = x64_adj_cmp (r0,r3,r8) in
        (r6,r7,r8,r9,r10,r11,ys,zs)
    else
      let r0 = r6 in (* x1 *)
      let r2 = EL (w2n r11) ys in
      let (r0,r1,r2) = x64_single_mul (r0,r1,r2) in
      let r1 = r12 in
      let r12 = r2 in
      let r2 = r0 in
      let r0 = r7 in
      let (r0,r1,r2) = x64_single_mul (r0,r1,r2) in
      let r1 = r12 in
      let r12 = r2 in
      let r3 = EL (w2n r10) zs in
      let (r0,r3,r8) = x64_adj_cmp (r0,r3,r8) in
      let r11 = r11 + 1w in
      let r10 = r10 + 1w in
        x64_adjust_aux (r1,r6,r7,r8,r9,r10,r11,r12,ys,zs)`

val (res,x64_div_adjust_def,x64_div_adjust_pre_def) = x64_compile `
  x64_div_adjust (r6,r7,r9,r10,ys,zs) =
    let r1 = 0w in
    let r8 = r1 in
    let r11 = r1 in
    let r12 = r1 in
    let (r6,r7,r8,r9,r10,r11,ys,zs) =
      x64_adjust_aux (r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) in
      if (r7 = 0w) then (r6,r7,r9,r10,r11,ys,zs) else
      if (r8 = 0w) then (r6,r7,r9,r10,r11,ys,zs) else
        let r7 = r7 - 1w in (r6,r7,r9,r10,r11,ys,zs)`

val x64_adj_cmp_thm = prove(
  ``x64_adj_cmp_pre (r1,h,anything) /\
    (x64_adj_cmp (r1,h,if res = SOME T then 0x1w else 0x0w) =
      (r1,h,if mw_cmp_alt [h] [r1] res = SOME T then 0x1w else 0x0w))``,
  SIMP_TAC std_ss [mw_cmp_alt_def,HD,TL,x64_adj_cmp_def,x64_adj_cmp_pre_def,LET_DEF]
  \\ Cases_on `r1 = h` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h <+ r1` \\ FULL_SIMP_TAC std_ss []);

val EL_LENGTH = prove(
  ``(EL (LENGTH xs) (xs ++ y::ys) = y) /\
    (EL (LENGTH xs) (xs ++ y::ys ++ zs) = y)``,
  SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD,
    GSYM APPEND_ASSOC,APPEND]);

val SNOC_INTRO = prove(
  ``(xs ++ y::ys = SNOC y xs ++ ys) /\
    (xs ++ y::ys ++ zs = SNOC y xs ++ ys ++ zs)``,
  FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]);

val mw_cmp_alt_CONS = prove(
  ``mw_cmp_alt zs (mw_mul_by_single2 r6 r7 ys q2 q4) (mw_cmp_alt [z] [q3] res) =
    mw_cmp_alt (z::zs) (q3::mw_mul_by_single2 r6 r7 ys q2 q4) res``,
  SIMP_TAC std_ss [mw_cmp_alt_def,TL,HD]);

val x64_adjust_aux_thm = prove(
  ``!ys zs ys1 zs1 zs2 res r1 r12.
      (LENGTH zs = LENGTH ys + 1) /\ LENGTH (ys1 ++ ys) < dimword (:64)
                                  /\ LENGTH (zs1 ++ zs) < dimword (:64) ==>
      x64_adjust_aux_pre (r1,r6,r7,if res = SOME T then 1w else 0w,
        n2w (LENGTH (ys1 ++ ys)), n2w (LENGTH zs1),n2w (LENGTH ys1),
        r12,ys1 ++ ys,zs1 ++ zs ++ zs2) /\
      (x64_adjust_aux (r1,r6,r7,if res = SOME T then 1w else 0w,
        n2w (LENGTH (ys1 ++ ys)), n2w (LENGTH zs1),n2w (LENGTH ys1),
        r12,ys1 ++ ys,zs1 ++ zs ++ zs2) =
        (r6,r7,if mw_cmp_alt zs (mw_mul_by_single2 r6 r7 ys r1 r12) res = SOME T
               then 1w else 0w,n2w (LENGTH (ys1 ++ ys)),n2w (LENGTH (zs1 ++ zs)),
               n2w (LENGTH (ys1 ++ ys)),ys1 ++ ys,zs1 ++ zs ++ zs2))``,
  Induct THEN1
   (SIMP_TAC std_ss [APPEND_NIL,mw_mul_by_single2_def,LENGTH]
    \\ Cases \\ SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1]
    \\ ONCE_REWRITE_TAC [x64_adjust_aux_def,x64_adjust_aux_pre_def]
    \\ SIMP_TAC std_ss [LET_DEF,LENGTH_APPEND,LENGTH]
    \\ NTAC 6 STRIP_TAC
    \\ `LENGTH zs1 < dimword (:64)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC,w2n_n2w,
         rich_listTheory.EL_LENGTH_APPEND,NULL_DEF,HD]
    \\ REWRITE_TAC [x64_adj_cmp_thm] \\ SIMP_TAC std_ss [word_add_n2w]
    \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [x64_adjust_aux_def,x64_adjust_aux_pre_def]
  \\ Cases_on `zs` \\ SIMP_TAC std_ss [LENGTH,ADD1] \\ NTAC 8 STRIP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH (zs1 ++ z::zs) < dimword (:64)`
  \\ POP_ASSUM MP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH (ys1 ++ y::ys) < dimword (:64)`
  \\ STRIP_TAC
  \\ `n2w (LENGTH (ys1 ++ y::ys)) <> n2w (LENGTH ys1):word64` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ `LENGTH ys1 < dimword(:64)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH,ADD1])
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,x64_adj_cmp_thm,x64_single_mul_add_thm,
        x64_single_mul_thm]
  \\ `LENGTH zs1 < dimword (:64) /\ LENGTH ys1 < dimword (:64)` by
       (FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,EL_LENGTH,LET_DEF,mw_mul_by_single2_def]
  \\ `?q1 q2. single_mul_add r6 y r1 0x0w = (q1,q2)` by METIS_TAC [PAIR]
  \\ `?q3 q4. single_mul_add r7 q1 r12 0x0w = (q3,q4)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [SNOC_INTRO]
  \\ `(LENGTH ys1 + 1 = LENGTH (SNOC y ys1)) /\
      (LENGTH zs1 + 1 = LENGTH (SNOC z zs1))` by
        FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1]
  \\ FULL_SIMP_TAC std_ss [mw_cmp_alt_CONS]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  |> Q.SPECL [`ys`,`zs`,`[]`,`zs1`,`zs2`,`NONE`,`0w`,`0w`]
  |> SIMP_RULE std_ss [LENGTH,APPEND] |> GEN_ALL;

val x64_div_adjust_thm = prove(
  ``(LENGTH zs = LENGTH ys + 1) /\ LENGTH ys < dimword (:64)
                                /\ LENGTH (zs1 ++ zs) < dimword (:64) ==>
    x64_div_adjust_pre (r6,r7,n2w (LENGTH ys),n2w (LENGTH zs1),
                        ys,zs1 ++ zs ++ zs2) /\
    (x64_div_adjust (r6,r7,n2w (LENGTH ys),n2w (LENGTH zs1),
                     ys,zs1 ++ zs ++ zs2) =
      (r6,mw_div_adjust r7 zs (FRONT (mw_mul_by_single r6 ys)),
       n2w (LENGTH ys),n2w (LENGTH (zs1 ++ zs)),n2w (LENGTH ys),
       ys,zs1 ++ zs ++ zs2))``,
  SIMP_TAC std_ss [x64_div_adjust_def,x64_div_adjust_pre_def,LET_DEF]
  \\ ASSUME_TAC x64_adjust_aux_thm \\ SEP_I_TAC "x64_adjust_aux"
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mw_div_adjust_def]
  \\ SIMP_TAC std_ss [GSYM mw_mul_by_single2_thm]
  \\ `mw_cmp_alt zs (mw_mul_by_single2 r6 r7 ys 0x0w 0x0w) NONE =
      mw_cmp zs (mw_mul_by_single2 r6 r7 ys 0x0w 0x0w)` by ALL_TAC THEN1
   (MATCH_MP_TAC (GSYM mw_cmp_alt_thm)
    \\ SIMP_TAC std_ss [mw_mul_by_single2_thm,LENGTH_mw_mul_by_single]
    \\ FULL_SIMP_TAC std_ss [LENGTH_mw_mul_by_single,LENGTH_FRONT,
         GSYM LENGTH_NIL] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ `0 < dimword (:64)` by DECIDE_TAC
  \\ Cases_on `r7` \\ FULL_SIMP_TAC std_ss [w2n_n2w,n2w_11]
  \\ Cases_on `mw_cmp zs (mw_mul_by_single2 r6 (n2w n) ys 0x0w 0x0w) = SOME T`
  \\ FULL_SIMP_TAC std_ss [EVAL ``0w=1w:word64``]
  \\ Cases_on `n = 0` \\ FULL_SIMP_TAC std_ss [word_arith_lemma2]
  \\ `~(n < 1)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []);

(* mw_div -- mw_sub *)

val (x64_div_sub_res,x64_div_sub_def) = x64_decompile "x64_div_sub" `
      not r0
      add r8,1
      adc r3,r0
      mov r0,0
      mov r8,r0
      not r0
      cmovb r8,r0`;

val _ = add_compiled [x64_div_sub_res]

val bool2num_thm = prove(
  ``bool2num = b2n``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ Cases \\ EVAL_TAC);

val x64_div_sub_thm = prove(
  ``x64_div_sub_pre (r0,r3,r8) /\
    (x64_div_sub (r0,r3,r8) =
       let (r3,c) = single_sub r3 r0 (dimword (:64) <= w2n r8 + 1) in
         (~0w,r3,if c then ~0w else 0w))``,
  SIMP_TAC std_ss [single_sub_def,x64_div_sub_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [bool2num_thm]
  \\ SIMP_TAC std_ss [GSYM (EVAL ``dimword (:64)``)]
  \\ SIMP_TAC std_ss [GSYM (EVAL ``FST (single_add x y c)``)]
  \\ SIMP_TAC std_ss [GSYM (EVAL ``SND (single_add x y c)``)]
  \\ Cases_on `single_add r3 (~r0) (dimword (:64) <= w2n r8 + 1)`
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `r` \\ EVAL_TAC);

val (res,x64_div_sub_loop_def,x64_div_sub_loop_pre_def) = x64_compile `
  x64_div_sub_loop (r1,r6,r7,r8:word64,r9,r10:word64,r11:word64,r12,ys:word64 list,zs) =
    if r9 = r11 then
      let r0 = r12 in
      let r3 = EL (w2n r10) zs in
      let (r0,r3,r8) = x64_div_sub (r0,r3,r8) in
      let r1 = r3 in
      let zs = LUPDATE r1 (w2n r10) zs in
      let r10 = r10 + 1w in
        (r6,r7,r9,r10,r11,ys,zs)
    else
      let r0 = r6 in (* x1 *)
      let r2 = EL (w2n r11) ys in
      let (r0,r1,r2) = x64_single_mul (r0,r1,r2) in
      let r1 = r12 in
      let r12 = r2 in
      let r2 = r0 in
      let r0 = r7 in
      let (r0,r1,r2) = x64_single_mul (r0,r1,r2) in
      let r1 = r12 in
      let r12 = r2 in
      let r3 = EL (w2n r10) zs in
      let (r0,r3,r8) = x64_div_sub (r0,r3,r8) in
      let r0 = r1 in
      let r1 = r3 in
      let zs = LUPDATE r1 (w2n r10) zs in
      let r1 = r0 in
      let r11 = r11 + 1w in
      let r10 = r10 + 1w in
        x64_div_sub_loop (r1,r6,r7,r8,r9,r10,r11,r12,ys,zs)`

val LUPDATE_THM = prove(
  ``(LUPDATE q (LENGTH xs) (SNOC x xs) = SNOC q xs) /\
    (LUPDATE q (LENGTH xs) (SNOC x xs ++ ys) = SNOC q xs ++ ys) /\
    (LUPDATE q (LENGTH xs) (SNOC x xs ++ ys ++ zs) = SNOC q xs ++ ys ++ zs)``,
  SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,LUPDATE_LENGTH]);

val x64_div_sub_loop_thm = prove(
  ``!ys zs ys1 zs1 zs2 c r1 r12.
      (LENGTH zs = LENGTH ys + 1) /\ LENGTH (ys1 ++ ys) < dimword (:64)
                                  /\ LENGTH (zs1 ++ zs) < dimword (:64) ==>
      x64_div_sub_loop_pre (r1,r6,r7,(if c then ~0w else 0w),
        n2w (LENGTH (ys1 ++ ys)), n2w (LENGTH zs1),n2w (LENGTH ys1),
        r12,ys1 ++ ys,zs1 ++ zs ++ zs2) /\
      (x64_div_sub_loop (r1,r6,r7,(if c then ~0w else 0w),
        n2w (LENGTH (ys1 ++ ys)), n2w (LENGTH zs1),n2w (LENGTH ys1),
        r12,ys1 ++ ys,zs1 ++ zs ++ zs2) =
        (r6,r7,n2w (LENGTH (ys1 ++ ys)),n2w (LENGTH (zs1 ++ zs)),
               n2w (LENGTH (ys1 ++ ys)),ys1 ++ ys,
         zs1 ++ (FST (mw_sub zs (mw_mul_by_single2 r6 r7 ys r1 r12) c)) ++ zs2))``,
  Induct THEN1
   (SIMP_TAC std_ss [APPEND_NIL,mw_mul_by_single2_def,LENGTH]
    \\ Cases \\ SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1]
    \\ ONCE_REWRITE_TAC [x64_div_sub_loop_def,x64_div_sub_loop_pre_def]
    \\ SIMP_TAC std_ss [LET_DEF,LENGTH_APPEND,LENGTH]
    \\ NTAC 6 STRIP_TAC
    \\ `LENGTH zs1 < dimword (:64)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,w2n_n2w,EL_LENGTH]
    \\ FULL_SIMP_TAC std_ss [LUPDATE_THM,APPEND_NIL,SNOC_INTRO]
    \\ FULL_SIMP_TAC std_ss [SNOC_INTRO,x64_div_sub_thm]
    \\ `(dimword (:64) <= w2n (if c then (~0x0w) else 0x0w:word64) + 1) = c` by
          (Cases_on `c` \\ EVAL_TAC)
    \\ FULL_SIMP_TAC std_ss [mw_sub_def,HD,TL]
    \\ Cases_on `single_sub h r12 c`
    \\ FULL_SIMP_TAC std_ss [LET_DEF,SNOC_INTRO,APPEND_NIL] \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [x64_div_sub_loop_def,x64_div_sub_loop_pre_def]
  \\ Cases_on `zs` \\ SIMP_TAC std_ss [LENGTH,ADD1] \\ NTAC 8 STRIP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH (zs1 ++ z::zs) < dimword (:64)`
  \\ POP_ASSUM MP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH (ys1 ++ y::ys) < dimword (:64)`
  \\ STRIP_TAC
  \\ `n2w (LENGTH (ys1 ++ y::ys)) <> n2w (LENGTH ys1):word64` by
   (FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ `LENGTH ys1 < dimword(:64)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH,ADD1])
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,x64_adj_cmp_thm,x64_single_mul_add_thm,
        x64_single_mul_thm]
  \\ `LENGTH zs1 < dimword (:64) /\ LENGTH ys1 < dimword (:64)` by
       (FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,EL_LENGTH,LET_DEF,mw_mul_by_single2_def]
  \\ `?q1 q2. single_mul_add r6 y r1 0x0w = (q1,q2)` by METIS_TAC [PAIR]
  \\ `?q3 q4. single_mul_add r7 q1 r12 0x0w = (q3,q4)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [SNOC_INTRO,x64_div_sub_thm]
  \\ `(dimword (:64) <= w2n (if c then (~0x0w) else 0x0w:word64) + 1) = c` by
        (Cases_on `c` \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [mw_sub_def,HD,TL]
  \\ Cases_on `single_sub z q3 c`
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ SIMP_TAC std_ss [SNOC_INTRO,LUPDATE_THM]
  \\ `(LENGTH ys1 + 1 = LENGTH (SNOC y ys1)) /\
      (LENGTH zs1 + 1 = LENGTH (SNOC q zs1)) /\
      (LENGTH (SNOC y ys1 ++ ys) = LENGTH (SNOC q ys1 ++ ys)) /\
      LENGTH (SNOC q ys1 ++ ys) < dimword (:64) /\
      LENGTH (SNOC q zs1 ++ zs) < dimword (:64)` by
        (FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1,LENGTH_APPEND] \\ DECIDE_TAC)
  \\ Q.PAT_ASSUM `!zs. bbb` (MP_TAC o Q.SPECL [`zs`,`SNOC y ys1`,
         `SNOC q zs1`,`zs2`,`r`,`q2`,`q4`])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_SNOC]
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC)
  |> Q.SPECL [`ys`,`zs`,`[]`,`zs1`,`zs2`,`T`,`0w`,`0w`]
  |> SIMP_RULE std_ss [LENGTH,APPEND] |> GEN_ALL;

(* mw_div -- mw_div_aux *)

val (res,x64_div_loop_def,x64_div_loop_pre_def) = x64_compile `
  x64_div_loop (r7,r9,r10,r11,ys,zs,ss) =
    if r10 = 0w then
      (r7,r9,r10,r11,ys,zs,ss)
    else
      let (r6,ss) = (HD ss,TL ss) in
      let (r3,ss) = (HD ss,TL ss) in
      let ss = r7::ss in
      let ss = r9::ss in
      let ss = r10::ss in
      let r10 = r10 + r9 in
      let r10 = r10 - 1w in
      let r0 = EL (w2n r10) zs in
      let r10 = r10 - 1w in
      let r1 = EL (w2n r10) zs in
      let r10 = r10 - 1w in
      let r2 = EL (w2n r10) zs in
      let r11 = r0 in
      let r10 = r1 in
      let r9 = r2 in
      let r7 = r3 in
      let r8 = r6 in
      let (r6,r7,r8,r9,r10,r11) = x64_div_guess (r7,r8,r9,r10,r11) in
      let r0 = r6 in
      let (r10,ss) = (HD ss,TL ss) in
      let (r9,ss) = (HD ss,TL ss) in
      let (r6,ss) = (HD ss,TL ss) in
      let r10 = r10 - 1w in
      let ss = r7::ss in
      let ss = r8::ss in
      let r7 = r0 in
      let (r6,r7,r9,r10,r11,ys,zs) = x64_div_adjust (r6,r7,r9,r10,ys,zs) in
      let r10 = r10 - r9 in
      let r10 = r10 - 1w in
      let r1 = 0w in
      let r8 = ~r1 in
      let r11 = r1 in
      let r12 = r1 in
      let (r6,r7,r9,r10,r11,ys,zs) =
            x64_div_sub_loop (r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) in
      let r10 = r10 - 1w in
      let zs = LUPDATE r7 (w2n r10) zs in
      let r10 = r10 - r9 in
      let r7 = r6 in
        x64_div_loop (r7,r9,r10,r11,ys,zs,ss)`

val x64_div_loop_thm = prove(
  ``!zs1 zs ys1 zs2 c r1 r12.
      (LENGTH zs = LENGTH ys) /\ LENGTH (zs1 ++ zs ++ zs2) < dimword (:64) /\
      1 < LENGTH ys /\ LAST (FRONT (mw_mul_by_single d ys)) <> 0x0w ==>
      let ys1 = (FRONT (mw_mul_by_single d ys)) in
        x64_div_loop_pre (d,n2w (LENGTH ys),n2w (LENGTH zs1),n2w (LENGTH ys),
          ys,zs1 ++ zs ++ zs2,(LAST ys1)::(LAST (BUTLAST ys1))::ss) /\
        (x64_div_loop (d,n2w (LENGTH ys),n2w (LENGTH zs1),n2w (LENGTH ys),
          ys,zs1 ++ zs ++ zs2,(LAST ys1)::(LAST (BUTLAST ys1))::ss) =
          (d,n2w (LENGTH ys),0w,n2w (LENGTH ys),ys,
           (let (qs,rs) = mw_div_aux zs1 zs ys1 in
              rs ++ REVERSE qs ++ zs2),(LAST ys1)::(LAST (BUTLAST ys1))::ss))``,
  Q.ABBREV_TAC `ys1 = FRONT (mw_mul_by_single d ys)`
  \\ SIMP_TAC std_ss [LET_DEF] \\ HO_MATCH_MP_TAC SNOC_INDUCT
  \\ STRIP_TAC THEN1 (SIMP_TAC std_ss
    [LENGTH,APPEND,Once mw_div_aux_def,APPEND_NIL,
     Once x64_div_loop_def,Once x64_div_loop_pre_def,REVERSE_DEF])
  \\ NTAC 2 STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_div_aux_def] \\ NTAC 4 STRIP_TAC
  \\ SIMP_TAC std_ss [LAST_SNOC,FRONT_SNOC,rich_listTheory.NOT_SNOC_NIL]
  \\ NTAC 4 (SIMP_TAC std_ss [Once LET_DEF])
  \\ Q.ABBREV_TAC `guess = mw_div_guess (REVERSE (x::zs)) (REVERSE ys1)`
  \\ Q.ABBREV_TAC `adj = mw_div_adjust guess (x::zs) ys1`
  \\ Q.ABBREV_TAC `sub = (FST (mw_sub (x::zs) (mw_mul_by_single adj ys1) T))`
  \\ `?qs1 rs1. mw_div_aux zs1 (FRONT sub) ys1 = (qs1,rs1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [x64_div_loop_def,x64_div_loop_pre_def]
  \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH_APPEND]
  \\ IMP_RES_TAC (DECIDE ``n + m + k < d ==> 0 < d /\ n < d:num``)
  \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH_APPEND]
  \\ SIMP_TAC std_ss [LENGTH_SNOC,ADD1,GSYM word_add_n2w,WORD_ADD_SUB,HD,TL]
  \\ SIMP_TAC std_ss [LET_DEF,TL,HD,GSYM WORD_SUB_PLUS,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC]
  \\ `(zs1 ++ ([x] ++ (zs ++ zs2))) = (zs1 ++ x::zs ++ zs2)` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss []
  \\ `~(LENGTH zs1 + 1 + LENGTH ys < 3) /\
      ~(LENGTH zs1 + 1 + LENGTH ys < 2) /\
      ~(LENGTH zs1 + 1 + LENGTH ys < 1) /\
      ~(LENGTH (zs1 ++ x::zs) < 1) /\
      ~(LENGTH (zs1 ++ x::zs) < 1 + LENGTH ys) /\
      (LENGTH zs1 + 1 + LENGTH ys - 3) < dimword (:64) /\
      (LENGTH zs1 + 1 + LENGTH ys - 2) < dimword (:64) /\
      (LENGTH zs1 + 1 + LENGTH ys - 1) < dimword (:64) /\
      (LENGTH zs1 + 1 + LENGTH ys) < dimword (:64) /\
      (LENGTH (zs1 ++ x::zs) - 1) < dimword (:64) /\
      ~(LENGTH zs1 + 1 < 1) /\
      ~(LENGTH (zs1 ++ x::zs) < LENGTH ys + 1) /\
      (LENGTH (zs1 ++ x::zs) - (LENGTH ys + 1) = LENGTH zs1)` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,word_arith_lemma2]
  \\ FULL_SIMP_TAC std_ss [w2n_n2w]
  \\ `(EL (LENGTH zs1 + 1 + LENGTH ys - 3) (zs1 ++ x::zs ++ zs2) =
       LAST (BUTLAST (BUTLAST (x::zs)))) /\
      (EL (LENGTH zs1 + 1 + LENGTH ys - 2) (zs1 ++ x::zs ++ zs2) =
       LAST (BUTLAST (x::zs))) /\
      (EL (LENGTH zs1 + 1 + LENGTH ys - 1) (zs1 ++ x::zs ++ zs2) =
       LAST (x::zs))` by ALL_TAC THEN1
   (`(LENGTH zs1 + 1 + LENGTH ys - 3 = LENGTH zs1 + (LENGTH (x::zs) - 3)) /\
     (LENGTH zs1 + 1 + LENGTH ys - 2 = LENGTH zs1 + (LENGTH (x::zs) - 2)) /\
     (LENGTH zs1 + 1 + LENGTH ys - 1 = LENGTH zs1 + (LENGTH (x::zs) - 1)) /\
     (LENGTH (x::zs) - 3 < LENGTH (x::zs))` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,DECIDE ``n <= n + m:num``,
         GSYM APPEND_ASSOC,rich_listTheory.EL_APPEND1]
    \\ `(x::zs = []) \/ ?t1 t2. x::zs = SNOC t1 t2` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
    \\ `LENGTH ys = LENGTH t2` by ALL_TAC THEN1
     (`LENGTH (x::zs) = LENGTH (t2 ++ [t1])` by METIS_TAC []
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,ADD1])
    \\ FULL_SIMP_TAC std_ss [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC]
    \\ `(t2 = []) \/ ?t3 t4. t2 = SNOC t3 t4` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC (srw_ss()) [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC,
         LENGTH,ADD1,SNOC_APPEND] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ SIMP_TAC std_ss [EL_LENGTH,DECIDE ``n+1+1-2 = n:num``]
    \\ `(t4 = []) \/ ?t5 t6. t4 = SNOC t5 t6` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC (srw_ss()) [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC,
         LENGTH,ADD1,SNOC_APPEND] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ SIMP_TAC std_ss [EL_LENGTH,DECIDE ``n+1+1+1-3 = n:num``])
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (x64_div_guess_thm |> GEN_ALL)
  \\ SEP_I_TAC "x64_div_guess" \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`REVERSE (FRONT (FRONT ys1))`,
      `REVERSE (FRONT (FRONT (FRONT (x::zs))))`])
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `mw_div_guess
        (LAST (x::zs)::LAST (FRONT (x::zs))::
             LAST (FRONT (FRONT (x::zs)))::REVERSE (FRONT (FRONT (FRONT (x::zs)))))
        (LAST ys1::LAST (FRONT ys1)::REVERSE (FRONT (FRONT ys1))) = guess` by ALL_TAC
  THEN1
   (Q.UNABBREV_TAC `guess`
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x1 = x2) /\ (y1 = y2) ==> (f x1 y1 = f x2 y2)``)
    \\ Tactical.REVERSE STRIP_TAC THEN1
     (`LENGTH ys1 = LENGTH ys` by ALL_TAC THEN1
       (Q.UNABBREV_TAC `ys1`
        \\ FULL_SIMP_TAC std_ss [LENGTH_FRONT,LENGTH_mw_mul_by_single,GSYM LENGTH_NIL]
        \\ DECIDE_TAC)
      \\ `(ys1 = []) \/ ?t1 t2. ys1 = SNOC t1 t2` by METIS_TAC [SNOC_CASES]
      \\ FULL_SIMP_TAC (srw_ss()) [ADD1,GSYM LENGTH_NIL] THEN1 `F` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC]
      \\ `(t2 = []) \/ ?t3 t4. t2 = SNOC t3 t4` by METIS_TAC [SNOC_CASES]
      \\ FULL_SIMP_TAC (srw_ss()) [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC,
           LENGTH,ADD1,SNOC_APPEND] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ DECIDE_TAC)
    \\ `(x::zs = []) \/ ?t1 t2. x::zs = SNOC t1 t2` by METIS_TAC [SNOC_CASES]
    THEN1 FULL_SIMP_TAC (srw_ss()) [ADD1] \\ ASM_SIMP_TAC std_ss []
    \\ `LENGTH ys = LENGTH t2` by ALL_TAC THEN1
     (`LENGTH (x::zs) = LENGTH (SNOC t1 t2)` by METIS_TAC []
      \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,LENGTH,ADD1])
    \\ FULL_SIMP_TAC std_ss [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC]
    \\ `(t2 = []) \/ ?t3 t4. t2 = SNOC t3 t4` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [LAST_SNOC,FRONT_SNOC,REVERSE_SNOC,CONS_11]
    \\ FULL_SIMP_TAC (srw_ss()) [EL_LENGTH,RW [SNOC_APPEND] FRONT_SNOC,
         LENGTH,ADD1,SNOC_APPEND] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ `(t4 = []) \/ ?t5 t6. t4 = SNOC t5 t6` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [LAST_SNOC,FRONT_SNOC,REVERSE_SNOC,CONS_11]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [] \\ NTAC 6 (POP_ASSUM (K ALL_TAC))
  \\ ASSUME_TAC (GEN_ALL x64_div_adjust_thm)
  \\ SEP_I_TAC "x64_div_adjust" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [LENGTH] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [word_add_n2w,word_arith_lemma2]
  \\ ASSUME_TAC (GEN_ALL x64_div_sub_loop_thm)
  \\ SEP_I_TAC "x64_div_sub_loop" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [LENGTH] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [word_add_n2w,word_arith_lemma2]
  \\ FULL_SIMP_TAC std_ss [w2n_n2w]
  \\ `LENGTH (zs1 ++ x::zs) - (1 + LENGTH ys) = LENGTH zs1` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `LUPDATE adj (LENGTH (zs1 ++ x::zs) - 1) (zs1 ++
        FST (mw_sub (x::zs) (mw_mul_by_single2 d adj ys 0x0w 0x0w) T) ++
        zs2) = zs1 ++ SNOC adj (FRONT sub) ++ zs2` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [mw_mul_by_single2_thm]
    \\ `LENGTH sub = LENGTH (x::zs)` by ALL_TAC THEN1
     (Q.UNABBREV_TAC `sub`
      \\ Cases_on `mw_sub (x::zs) (mw_mul_by_single adj ys1) T`
      \\ IMP_RES_TAC LENGTH_mw_sub \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ `(sub = []) \/ ?t3 t4. sub = SNOC t3 t4` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,FRONT_SNOC]
    \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
    \\ `LENGTH (zs1 ++ x::zs) - 1 = LENGTH (zs1 ++ t4)` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH])
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,APPEND]
  \\ SEP_I_TAC "x64_div_loop" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (`(LENGTH (FRONT sub) = LENGTH ys)` by ALL_TAC THEN1
      (Q.UNABBREV_TAC `sub`
       \\ Cases_on `mw_sub (x::zs) (mw_mul_by_single adj ys1) T`
       \\ FULL_SIMP_TAC std_ss []
       \\ IMP_RES_TAC LENGTH_mw_sub
       \\ Cases_on `q = []` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
       \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_FRONT,GSYM LENGTH_NIL,ADD1]
       \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [REVERSE_DEF,GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC (srw_ss()) [GSYM CONJ_ASSOC]
  \\ Cases_on `mw_sub (x::zs) (mw_mul_by_single2 d adj ys 0x0w 0x0w) T`
  \\ IMP_RES_TAC LENGTH_mw_sub
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

(* mw_div -- mul_by_single *)

val (res,x64_mul_by_single_def,x64_mul_by_single_pre_def) = x64_compile `
  x64_mul_by_single (r1:word64,r8:word64,r9:word64,r10:word64,r11:word64,xs:word64 list,zs:word64 list) =
    if r9 = r11 then
      let zs = LUPDATE r1 (w2n r10) zs in
      let r10 = r10 + 1w in
        (r1,r8,r9,r10,xs,zs)
    else
      let r2 = EL (w2n r11) xs in
      let r0 = r8 in
      let r3 = 0w in
      let (r0,r1,r2,r3) = x64_single_mul_add (r0,r1,r2,r3) in
      let zs = LUPDATE r0 (w2n r10) zs in
      let r1 = r2 in
      let r10 = r10 + 1w in
      let r11 = r11 + 1w in
        x64_mul_by_single (r1,r8,r9,r10,r11,xs,zs)`

val x64_mul_by_single_thm = prove(
  ``!xs xs1 x zs k zs1 zs2 z2.
      LENGTH (xs1++xs) < dimword (:64) /\  (LENGTH zs = LENGTH xs) /\
      LENGTH (zs1++zs) < dimword (:64) ==>
      ?r1.
        x64_mul_by_single_pre (k,x,n2w (LENGTH (xs1++xs)),n2w (LENGTH zs1),
                          n2w (LENGTH xs1),xs1++xs,zs1++zs++z2::zs2) /\
        (x64_mul_by_single (k,x,n2w (LENGTH (xs1++xs)),n2w (LENGTH zs1),
                       n2w (LENGTH xs1),xs1++xs,zs1++zs++z2::zs2) =
           (r1,x,n2w (LENGTH (xs1++xs)),n2w (LENGTH (zs1++zs)+1),xs1++xs,
            zs1++(mw_mul_pass x xs (MAP (K 0w) xs) k)++zs2))``,
  Induct \\ Cases_on `zs`
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND_NIL,mw_mul_pass_def,ADD1]
  \\ ONCE_REWRITE_TAC [x64_mul_by_single_def,x64_mul_by_single_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,n2w_11,w2n_n2w,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,word_add_n2w,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [LENGTH,MAP,HD,TL]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (DECIDE ``m+n<k ==> m < k /\ n<k:num``)
  \\ FULL_SIMP_TAC std_ss [ADD1,x64_single_mul_add_thm]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,LUPDATE_LENGTH,NULL,HD]
  \\ Cases_on `single_mul_add x h' k 0w` \\ FULL_SIMP_TAC std_ss [LET_DEF,TL]
  \\ ONCE_REWRITE_TAC [SNOC_INTRO |> Q.INST [`xs2`|->`[]`] |> REWRITE_RULE [APPEND_NIL]]
  \\ `((LENGTH xs1 + (LENGTH xs + 1)) = (LENGTH (SNOC h' xs1) + LENGTH xs)) /\
      ((LENGTH xs1 + 1) = (LENGTH (SNOC h' xs1))) /\
      ((LENGTH zs1 + 1) = LENGTH (SNOC q zs1))` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH_SNOC] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "x64_mul_by_single" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,
       LENGTH_APPEND,LENGTH,AC ADD_COMM ADD_ASSOC] \\ DECIDE_TAC)
  |> Q.SPECL [`xs`,`[]`,`x`,`zs`,`0w`,`[]`]
  |> SIMP_RULE std_ss [APPEND,LENGTH,GSYM k2mw_LENGTH_0,GSYM mw_mul_by_single_def]
  |> GEN_ALL;

(* mw_div -- mul_by_single, top two from ys *)

val (res,x64_top_two_def,x64_top_two_pre_def) = x64_compile `
  x64_top_two (r0,r1:word64,r3,r8:word64,r9:word64,r11:word64,ys:word64 list) =
    if r9 = r11 then
      let r1 = r3 in
        (r0,r1,r8,r9,r11,ys)
    else
      let r3 = r0 in
      let r2 = EL (w2n r11) ys in
      let r0 = r8 in
      let (r0,r1,r2) = x64_single_mul (r0,r1,r2) in
      let r1 = r2 in
      let r11 = r11 + 1w in
        x64_top_two (r0,r1,r3,r8,r9,r11,ys)`

val x64_top_two_thm = prove(
  ``!ys x k1 k2 k3 ys1.
      LENGTH (ys1 ++ ys) < dimword (:64) ==>
      x64_top_two_pre (k2,k1,k3,
                       x,n2w (LENGTH (ys1++ys)),n2w (LENGTH ys1),ys1++ys) /\
      (x64_top_two (k2,k1,k3,
                    x,n2w (LENGTH (ys1++ys)),n2w (LENGTH ys1),ys1++ys) =
               (FST (SND (mw_mul_pass_top x ys (k1,k2,k3))),
                SND (SND (mw_mul_pass_top x ys (k1,k2,k3))),x,
                n2w (LENGTH (ys1++ys)),n2w (LENGTH (ys1++ys)),ys1++ys))``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND,APPEND_NIL]
  \\ ONCE_REWRITE_TAC [x64_top_two_def,x64_top_two_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,n2w_11,mw_mul_pass_top_def]
  \\ NTAC 7 STRIP_TAC
  \\ `LENGTH ys1 < dimword (:64) /\
      LENGTH (ys1 ++ h::ys) <> LENGTH ys1` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,EL_LENGTH]
  \\ FULL_SIMP_TAC std_ss [x64_single_mul_thm]
  \\ Cases_on `single_mul_add x h k1 0w`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,SNOC_INTRO]
  \\ `(LENGTH ys1 + 1) = (LENGTH (SNOC h ys1))` by ALL_TAC THEN1
       FULL_SIMP_TAC (srw_ss()) [word_add_n2w,ADD1]
  \\ FULL_SIMP_TAC std_ss [word_add_n2w]
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND] \\ DECIDE_TAC)
  |> Q.SPECL [`ys`,`x`,`0w`,`0w`,`0w`,`[]`] |> DISCH ``1 < LENGTH (ys:word64 list)``
  |> SIMP_RULE std_ss [APPEND_NIL,APPEND,LENGTH,mw_mul_pass_top_thm]
  |> REWRITE_RULE [AND_IMP_INTRO]


(* mw_div -- copy result down *)

val (res,x64_copy_down_def,x64_copy_down_pre_def) = x64_compile `
  x64_copy_down (r8:word64,r10:word64,r11:word64,zs:word64 list) =
    if r8 = 0w then zs else
      let r0 = EL (w2n r10) zs in
      let r8 = r8 - 1w in
      let r10 = r10 + 1w in
      let zs = LUPDATE r0 (w2n r11) zs in
      let r11 = r11 + 1w in
        x64_copy_down (r8,r10,r11,zs)`

val x64_copy_down_thm = prove(
  ``!zs0 zs1 zs2 zs3.
      LENGTH (zs0 ++ zs1 ++ zs2) < dimword (:64) /\ zs1 <> [] ==>
      ?zs4.
        x64_copy_down_pre (n2w (LENGTH zs2),
          n2w (LENGTH (zs0 ++ zs1)),n2w (LENGTH zs0),zs0 ++ zs1 ++ zs2 ++ zs3) /\
        (x64_copy_down (n2w (LENGTH zs2),
          n2w (LENGTH (zs0 ++ zs1)),n2w (LENGTH zs0),zs0 ++ zs1 ++ zs2 ++ zs3) =
           zs0 ++ zs2 ++ zs4) /\ (LENGTH zs4 = LENGTH zs1 + LENGTH zs3)``,
  Induct_on `zs2`
  \\ ONCE_REWRITE_TAC [x64_copy_down_def,x64_copy_down_pre_def]
  \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND_NIL]
  \\ FULL_SIMP_TAC std_ss [APPEND_11,GSYM APPEND_ASSOC,LENGTH_APPEND]
  \\ REPEAT STRIP_TAC
  \\ `SUC (LENGTH zs2) < dimword (:64) /\ 0 < dimword (:64) /\
      (LENGTH zs0 + LENGTH zs1) < dimword (:64) /\ LENGTH zs0 < dimword (:64)`
       by (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [n2w_11,ADD1,w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [GSYM LENGTH_APPEND,APPEND_ASSOC,EL_LENGTH]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [word_add_n2w]
  \\ Cases_on `zs1` \\ FULL_SIMP_TAC std_ss []
  \\ Q.MATCH_ASSUM_RENAME_TAC `z::zs <> []`
  \\ FULL_SIMP_TAC std_ss []
  \\ `(LENGTH (zs0 ++ z::zs) + 1 = LENGTH (SNOC h zs0 ++ SNOC h zs)) /\
      (LENGTH zs0 + 1 = LENGTH (SNOC h zs0))`
       by (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,LENGTH_SNOC] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH,GSYM APPEND_ASSOC,APPEND]
  \\ SIMP_TAC std_ss [SNOC_INTRO] \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ Q.PAT_ASSUM `!xx.bb` (MP_TAC o Q.SPECL [`SNOC h zs0`,`SNOC h zs`,`zs3`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
    (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,LENGTH_SNOC,NOT_SNOC_NIL]
     \\ DECIDE_TAC) \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `zs4` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,LENGTH_SNOC,NOT_SNOC_NIL]
  \\ DECIDE_TAC) |> Q.SPEC `[]` |> SIMP_RULE std_ss [APPEND,LENGTH];

(* mw_div -- copy xs into zs *)

val (res,x64_copy_over_def,x64_copy_over_pre_def) = x64_compile `
  x64_copy_over (r10:word64,xs:word64 list,zs:word64 list) =
    if r10 = 0w then (xs,zs) else
      let r10 = r10 - 1w in
      let r0 = EL (w2n r10) xs in
      let zs = LUPDATE r0 (w2n r10) zs in
        x64_copy_over (r10,xs,zs)`;

val x64_copy_over_thm = prove(
  ``!xs0 zs0 xs zs.
      (LENGTH zs0 = LENGTH xs0) /\
      LENGTH (zs0++zs) < dimword (:64) ==>
      x64_copy_over_pre (n2w (LENGTH xs0),xs0 ++ xs,zs0 ++ zs) /\
      (x64_copy_over (n2w (LENGTH xs0),xs0 ++ xs,zs0 ++ zs) =
         (xs0 ++ xs,xs0 ++ zs))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ STRIP_TAC THEN1
   (ONCE_REWRITE_TAC [x64_copy_over_def,x64_copy_over_pre_def]
    \\ SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND])
  \\ NTAC 7 STRIP_TAC
  \\ `(zs0 = []) \/ ?x l. zs0 = SNOC x l` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_SNOC]
  \\ `LENGTH xs0 + 1 < dimword (:64) /\ LENGTH xs0 < dimword (:64)` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH_SNOC,LENGTH_APPEND] \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [x64_copy_over_def,x64_copy_over_pre_def]
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,EL_LENGTH,SNOC_APPEND]
  \\ Q.PAT_ASSUM `LENGTH l = LENGTH xs0` (ASSUME_TAC o GSYM)
  \\ ASM_SIMP_TAC std_ss [LUPDATE_LENGTH,APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  \\ `LENGTH l + LENGTH (x::zs) < dimword (:64)` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND] \\ DECIDE_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])


(* mw_div -- top-level function *)

val (res,x64_div_def,x64_div_pre_def) = x64_compile `
  x64_div (r0,r1,r3,xs,ys,zs,ss) =
    if r0 <+ r1 then (* LENGTH xs < LENGTH ys *)
      let r6 = r0 in
        if r3 = 0w then (* return div *)
          let r0 = 0w in
            (r0,r3,r6,xs,ys,zs,ss)
        else (* return mod *)
          let r11 = r0 in
          let r10 = r1 in
          let r0 = 0w in
          let (r10,zs) = x64_mul_zero (r0,r10,zs) in
          let r10 = r11 in
          let (xs,zs) = x64_copy_over (r10,xs,zs) in
          let r0 = r1 in
            (r0,r3,r6,xs,ys,zs,ss)
    else if r1 = 1w then (* LENGTH ys = 1 *)
      let ss = r3 :: ss in
      let r2 = 0w in
      let r10 = r2 in
      let r9 = EL (w2n r10) ys in
      let r10 = r0 in
      let r8 = r0 in
      let (r2,r9,r10,xs,zs) = x64_simple_div (r2,r9,r10,xs,zs) in
      let r6 = 0w in
      let r0 = r8 in
      let (r3,ss) = (HD ss,TL ss) in
        if r3 = 0w then
          if r2 = 0w then (r0,r3,r6,xs,ys,zs,ss) else
            let r6 = 1w in
              (r0,r3,r6,xs,ys,zs,ss)
        else
          let r0 = 1w in
          let r10 = 0w:word64 in
          let zs = LUPDATE r2 (w2n r10) zs in
            if r2 = 0w then (r0,r3,r6,xs,ys,zs,ss) else
              let r6 = 1w in
                (r0,r3,r6,xs,ys,zs,ss)
    else (* 1 < LENGTH ys <= LENGTH xs *)
      let ss = r3 :: ss in
      let ss = r0 :: ss in
      let r7 = r1 in
      let r9 = r0 in
      let r10 = r1 - 1w in
      let r1 = EL (w2n r10) ys in
      let r2 = 1w in
      let r2 = x64_calc_d (r1,r2) in
      let r1 = 0w in
      let r8 = r2 in
      let r10 = r1 in
      let r11 = r1 in
      let (r1,r8,r9,r10,xs,zs) = x64_mul_by_single (r1,r8,r9,r10,r11,xs,zs) in
      let r1 = 0w in
      let zs = LUPDATE r1 (w2n r10) zs in
      let r0 = 0w in
      let r1 = r0 in
      let r3 = r0 in
      let r11 = r0 in
      let r9 = r7 in
      let (r0,r1,r8,r9,r11,ys) = x64_top_two (r0,r1,r3,r8,r9,r11,ys) in
      let r7 = r8 in
      let r11 = r9 in
      let (r10,ss) = (HD ss,TL ss) in
      let r10 = r10 - r9 in
      let r10 = r10 + 2w in
      let ss = r10 :: ss in
      let ss = r1 :: ss in
      let ss = r0 :: ss in
      let (r7,r9,r10,r11,ys,zs,ss) = x64_div_loop (r7,r9,r10,r11,ys,zs,ss) in
      let (r0,ss) = (HD ss,TL ss) in
      let (r0,ss) = (HD ss,TL ss) in
      let (r8,ss) = (HD ss,TL ss) in
      let r11 = r9 in
      let r10 = r9 in
      let r9 = r7 in
      let r2 = 0w in
      let (r2,r9,r10,zs) = x64_simple_div1 (r2,r9,r10,zs) in
      let r9 = r11 in
      let r10 = r9 in
      let r7 = r8 in
      let (r8,r10,zs) = x64_fix (r8,r10,zs) in
      let r6 = r10 in
      let r10 = r9 in
      let (r3,ss) = (HD ss,TL ss) in
      let r8 = r7 in
        if r3 = 0w then
          let r11 = 0w in
          let zs = x64_copy_down (r8,r10,r11,zs) in
          let r0 = r7 in
            (r0,r3,r6,xs,ys,zs,ss)
        else
          let r0 = r9 in
            (r0,r3,r6,xs,ys,zs,ss)`

val mw_fix_SNOC = store_thm("mw_fix_SNOC",
 ``mw_fix (SNOC 0w xs) = mw_fix xs``,
  SIMP_TAC std_ss [Once mw_fix_def,FRONT_SNOC,LAST_SNOC] \\ SRW_TAC [] []);

val mw_fix_REPLICATE = prove(
  ``!n. mw_fix (xs ++ REPLICATE n 0w) = mw_fix xs``,
  Induct THEN1 SIMP_TAC std_ss [REPLICATE,APPEND_NIL]
  \\ ASM_SIMP_TAC std_ss [REPLICATE_SNOC,APPEND_SNOC,mw_fix_SNOC]);

val MAP_K_0 = prove(
  ``!xs. MAP (\x. 0x0w) xs = REPLICATE (LENGTH xs) 0x0w``,
  Induct \\ SRW_TAC [] [REPLICATE]);

val x64_div_thm = prove(
  ``ys <> [] /\ mw_ok xs /\ mw_ok ys /\ LENGTH xs + LENGTH ys <= LENGTH zs /\
    LENGTH zs < dimword (:64) /\ ((res,mod,T) = mw_div xs ys) ==>
    ?zs2.
      x64_div_pre (n2w (LENGTH xs),n2w (LENGTH ys),r3,xs,ys,zs,ss) /\
      (x64_div (n2w (LENGTH xs),n2w (LENGTH ys),r3,xs,ys,zs,ss) =
         (n2w (LENGTH (if r3 = 0w then res else mod)),r3,
          n2w (LENGTH (mw_fix mod)),xs,ys,
          (if r3 = 0w then res else mod) ++ zs2,ss)) /\
      (LENGTH zs = LENGTH ((if r3 = 0w then res else mod) ++ zs2)) /\
      ((r3 = 0w) ==> LENGTH zs2 <> 0) /\ LENGTH (mw_fix mod) < dimword (:64)``,
  SIMP_TAC std_ss [mw_div_def,LET_DEF] \\ STRIP_TAC
  \\ `LENGTH xs < dimword (:64) /\ LENGTH ys < dimword (:64)` by DECIDE_TAC
  \\ IMP_RES_TAC mw_ok_mw_fix_ID \\ FULL_SIMP_TAC std_ss []
  \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ Cases_on `LENGTH xs < LENGTH ys` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Cases_on `r3 = 0w` \\ FULL_SIMP_TAC std_ss [] THEN1
     (Q.EXISTS_TAC `zs`
      \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND,APPEND]
      \\ ASM_SIMP_TAC std_ss [x64_div_def,x64_div_pre_def,LET_DEF,WORD_LO,
           w2n_n2w, mw_ok_mw_fix_ID,n2w_11,ZERO_LT_dimword,LENGTH_NIL,
           mw_fix_REPLICATE] \\ FULL_SIMP_TAC std_ss [LENGTH,GSYM LENGTH_NIL]
      \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [x64_div_def,x64_div_pre_def,LET_DEF,WORD_LO,
           w2n_n2w, mw_ok_mw_fix_ID,n2w_11,ZERO_LT_dimword,LENGTH_NIL]
    \\ `?zs1 zs2. (zs = zs1 ++ zs2) /\ (LENGTH zs1 = LENGTH ys)` by ALL_TAC
    THEN1 (MATCH_MP_TAC LESS_EQ_LENGTH \\ DECIDE_TAC)
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC x64_mul_zero_thm \\ SEP_I_TAC "x64_mul_zero"
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `?zs3 zs4. (zs1 = zs3 ++ zs4) /\ (LENGTH zs3 = LENGTH xs)` by ALL_TAC
    THEN1 (MATCH_MP_TAC LESS_EQ_LENGTH \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [MAP_APPEND,GSYM APPEND_ASSOC]
    \\ ASSUME_TAC (x64_copy_over_thm |>
          Q.SPECL [`xs`,`MAP (\x.0w) (zs1:word64 list)`,`[]`,`zs2`]
          |> SIMP_RULE std_ss [LENGTH_MAP,APPEND_NIL,LENGTH_APPEND] |> GEN_ALL)
    \\ SEP_I_TAC "x64_copy_over" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND,LENGTH_MAP] \\ DECIDE_TAC)
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `LENGTH (zs3 ++ zs4) - LENGTH xs = LENGTH zs4` by ALL_TAC
    THEN1 FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ FULL_SIMP_TAC std_ss [mw_fix_REPLICATE,mw_ok_mw_fix_ID]
    \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE,GSYM LENGTH_NIL]
    \\ ASM_SIMP_TAC std_ss [MAP_K_0,APPEND_11])
  \\ Cases_on `LENGTH ys = 1` \\ FULL_SIMP_TAC std_ss [] THEN1
   (`?qs r c. mw_simple_div 0x0w (REVERSE xs) (HD ys) = (qs,r,c)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE]
    \\ `0 < dimword (:64)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [x64_div_def,x64_div_pre_def,LET_DEF,WORD_LO,w2n_n2w,EL]
    \\ `?zs1 zs2. (zs = zs1 ++ zs2) /\ (LENGTH zs1 = LENGTH xs)` by
         (MATCH_MP_TAC LESS_EQ_LENGTH \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC (x64_simple_div_thm |> Q.SPECL [`xs`,`[]`] |> GEN_ALL
        |> SIMP_RULE std_ss [APPEND_NIL])
    \\ SEP_I_TAC "x64_simple_div" \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ `(LENGTH xs) = (LENGTH qs)` by
        (IMP_RES_TAC LENGTH_mw_simple_div \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ Cases_on `r3 = 0w` \\ FULL_SIMP_TAC std_ss [] THEN1
     (Q.EXISTS_TAC `zs2` \\ Cases_on `r = 0w`
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REVERSE]
      \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL])
    \\ FULL_SIMP_TAC std_ss [HD,NOT_CONS_NIL,TL,LENGTH]
    \\ Cases_on `REVERSE qs`
    THEN1 FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL,LENGTH_REVERSE]
    \\ FULL_SIMP_TAC std_ss [APPEND,LUPDATE_def,LENGTH]
    \\ Q.EXISTS_TAC `t ++ zs2`
    \\ `LENGTH (mw_fix [r]) = if r = 0w then 0 else 1` by ALL_TAC
    THEN1 (EVAL_TAC \\ SRW_TAC [] [] \\ EVAL_TAC)
    \\ `LENGTH (REVERSE qs) = LENGTH (h::t)` by FULL_SIMP_TAC std_ss []
    \\ `LENGTH (zs1 ++ zs2) = SUC (LENGTH (t ++ zs2))` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_REVERSE,LENGTH_APPEND] \\ DECIDE_TAC)
    \\ `LENGTH (t ++ zs2) <> 0` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_REVERSE,LENGTH_APPEND] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `r = 0w` \\ FULL_SIMP_TAC std_ss [HD,NOT_CONS_NIL,TL])
  \\ Q.ABBREV_TAC `d = calc_d (LAST ys,0x1w)`
  \\ Q.ABBREV_TAC `xs1 = mw_mul_by_single d xs ++ [0x0w]`
  \\ `?qs1 rs1. (mw_div_aux (BUTLASTN (LENGTH ys) xs1) (LASTN (LENGTH ys) xs1)
           (FRONT (mw_mul_by_single d ys))) = (qs1,rs1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REVERSE]
  \\ `LENGTH ys <> 0` by FULL_SIMP_TAC std_ss [LENGTH_NIL]
  \\ `0 < dimword (:64) /\ LENGTH ys - 1 < dimword (:64)` by DECIDE_TAC
  \\ `1 < dimword (:64) /\ ~(LENGTH ys < 1) /\ 0 < LENGTH ys` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [x64_div_def,x64_div_pre_def,LET_DEF,WORD_LO,
       w2n_n2w,n2w_11,word_arith_lemma2]
  \\ `(LAST ys <> 0w) /\ (EL (LENGTH ys - 1) ys = LAST ys)` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [mw_ok_def]
    \\ `(ys = []) \/ ?y ys2. ys = SNOC y ys2` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,LAST_SNOC]
    \\ FULL_SIMP_TAC std_ss [EL_LENGTH,SNOC_APPEND])
  \\ FULL_SIMP_TAC std_ss [x64_calc_d_thm]
  \\ `?zs1 zs2. (zs = zs1 ++ zs2) /\ (LENGTH zs1 = LENGTH xs)` by
       (MATCH_MP_TAC LESS_EQ_LENGTH \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `zs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  THEN1 (`F` by DECIDE_TAC)
  \\ ASSUME_TAC x64_mul_by_single_thm
  \\ SEP_I_TAC "x64_mul_by_single"
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  THEN1 (`F` by DECIDE_TAC)
  \\ Q.MATCH_ASSUM_RENAME_TAC `zs = zs1 ++ z1::z2::zs2`
  \\ FULL_SIMP_TAC std_ss [LENGTH_mw_mul_by_single]
  \\ `LENGTH xs + 1 < dimword (:64)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [w2n_n2w]
  \\ `LUPDATE 0x0w (LENGTH xs + 1) (mw_mul_by_single d xs ++ z2::zs2) =
      xs1 ++ zs2` by ALL_TAC THEN1
   (`LENGTH xs + 1 = LENGTH (mw_mul_by_single d xs)` by
       FULL_SIMP_TAC std_ss [LENGTH_mw_mul_by_single]
    \\ ASM_SIMP_TAC std_ss [LUPDATE_LENGTH]
    \\ Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, APPEND])
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ (x64_top_two_thm |> GEN_ALL |> ASSUME_TAC)
  \\ SEP_I_TAC "x64_top_two" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [HD,TL]
  \\ `n2w (LENGTH xs) - n2w (LENGTH ys) + 0x2w:word64 =
      n2w (LENGTH xs1 - LENGTH ys)` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma2,word_add_n2w,LENGTH_APPEND,
          LENGTH_mw_mul_by_single,LENGTH] \\ AP_TERM_TAC \\ DECIDE_TAC)
  \\  FULL_SIMP_TAC std_ss []
  \\ `LENGTH xs + 2 = LENGTH xs1` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC std_ss [LENGTH_mw_mul_by_single,LENGTH_APPEND,LENGTH]
    \\ DECIDE_TAC)
  \\ `LENGTH ys <= LENGTH xs1` by DECIDE_TAC
  \\ `?ts1 ts2. (xs1 = ts1 ++ ts2) /\ (LENGTH ts2 = LENGTH ys)` by
        (MATCH_MP_TAC LESS_EQ_LENGTH_ALT \\ FULL_SIMP_TAC std_ss [])
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [BUTLASTN_LENGTH_APPEND,LASTN_LENGTH_APPEND]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ ASSUME_TAC (x64_div_loop_thm |> SIMP_RULE std_ss [LET_DEF] |> GEN_ALL)
  \\ SEP_I_TAC "x64_div_loop" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ STRIP_TAC THEN1 DECIDE_TAC \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ Q.UNABBREV_TAC `d`
    \\ MATCH_MP_TAC LAST_FRONT_mw_mul_by_single_NOT_ZERO
    \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [TL,HD,NOT_CONS_NIL]
  \\ `(LENGTH rs1 = LENGTH ys) /\ (LENGTH qs1 = LENGTH ts1)` by ALL_TAC THEN1
   (`LENGTH ys = LENGTH (FRONT (mw_mul_by_single d ys))` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [LENGTH_FRONT,GSYM LENGTH_NIL,
        LENGTH_mw_mul_by_single] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC LENGTH_mw_div_aux
    \\ Q.EXISTS_TAC `ts2` \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `LENGTH rs1 = LENGTH ys` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ ASSUME_TAC x64_simple_div1_thm
  \\ SEP_I_TAC "x64_simple_div1" \\ POP_ASSUM MP_TAC
  \\ `?x1 x2 x3. mw_simple_div 0x0w (REVERSE rs1) d = (x1,x2,x3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ IMP_RES_TAC LENGTH_mw_simple_div
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE]
  \\ (x64_fix_thm |> Q.SPECL [`REVERSE x1`,`REVERSE qs1 ++ zs2`,
        `n2w (LENGTH (ts1:word64 list))`] |> MP_TAC)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE]
  \\ Q.ABBREV_TAC `tt = mw_fix (REVERSE x1) ++
       REPLICATE (LENGTH x1 - LENGTH (mw_fix (REVERSE x1))) 0x0w`
  \\ `LENGTH tt = LENGTH rs1` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `tt`
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE]
    \\ `LENGTH (mw_fix (REVERSE x1)) <= LENGTH (REVERSE x1)` by
          FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
    \\ `LENGTH (REVERSE x1) = LENGTH x1` by SRW_TAC [] []
    \\ DECIDE_TAC)
  \\ Tactical.REVERSE (Cases_on `r3 = 0w`) \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.UNABBREV_TAC `tt` \\ FULL_SIMP_TAC std_ss
       [mw_fix_thm |> Q.SPEC `REVERSE xs` |> RW [LENGTH_REVERSE]]
    \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11,LENGTH_APPEND,LENGTH_REVERSE]
    \\ ASSUME_TAC (Q.ISPEC `REVERSE (x1:word64 list)` LENGTH_mw_fix)
    \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ DECIDE_TAC)
  \\ MP_TAC (x64_copy_down_thm |> Q.SPECL [`tt`,`REVERSE qs1`,`zs2`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [GSYM LENGTH_NIL] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ NTAC 3 (POP_ASSUM MP_TAC)
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE,APPEND_11]
  \\ `LENGTH (mw_fix (REVERSE x1)) < dimword (:64)` by ALL_TAC THEN1
      (`LENGTH (mw_fix (REVERSE x1)) <= LENGTH (REVERSE x1)` by
          FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
       \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [n2w_11,LENGTH_NIL]
  \\ NTAC 3 STRIP_TAC \\ DECIDE_TAC);

(* mwi_div -- addv zs [] c *)

val (res,x64_add1_def,x64_add1_pre_def) = x64_compile `
  x64_add1 (r2,r10,r11:word64,zs:word64 list) =
    if r10 = r11 then
      let r0 = 1w in
      let zs = LUPDATE r0 (w2n r10) zs in
      let r11 = r11 + 1w in
        (r11,zs)
    else
      let r0 = EL (w2n r10) zs in
        if r0 <> r2 then
          let r0 = r0 + 1w in
          let zs = LUPDATE r0 (w2n r10) zs in
            (r11,zs)
        else
          let r0 = 0w in
          let zs = LUPDATE r0 (w2n r10) zs in
          let r10 = r10 + 1w in
            x64_add1 (r2,r10,r11,zs)`

val (res,x64_add1_call_def,x64_add1_call_pre_def) = x64_compile `
  x64_add1_call (r2:word64,r6:word64,r11,zs) =
    if r2 = 0w then (r11,zs) else
    if r6 = 0w then (r11,zs) else
      let r2 = 0w in
      let r10 = r2 in
      let r2 = ~r2 in
      let (r11,zs) = x64_add1 (r2,r10,r11,zs) in
        (r11,zs)`

val x64_add1_thm = prove(
  ``!zs zs1.
      LENGTH (zs1 ++ zs) + 1 < dimword (:64) /\ zs2 <> [] ==>
      ?rest.
        x64_add1_pre (~0w,n2w (LENGTH zs1),n2w (LENGTH (zs1 ++ zs)),
                      zs1 ++ zs ++ zs2) /\
        (x64_add1 (~0w,n2w (LENGTH zs1),n2w (LENGTH (zs1 ++ zs)),
                   zs1 ++ zs ++ zs2) =
         (n2w (LENGTH (zs1 ++ mw_addv zs [] T)), zs1 ++ mw_addv zs [] T ++ rest)) /\
        LENGTH (zs1 ++ mw_addv zs [] T) < dimword (:64) /\
        (LENGTH (zs1 ++ mw_addv zs [] T ++ rest) = LENGTH (zs1 ++ zs ++ zs2))``,
  Cases_on `zs2` \\ SIMP_TAC std_ss []
  \\ Q.SPEC_TAC (`t`,`zs2`) \\ Q.SPEC_TAC (`h`,`t`) \\ STRIP_TAC \\ STRIP_TAC
  \\ Induct
  \\ SIMP_TAC std_ss [mw_addv_NIL,LENGTH_APPEND,APPEND,APPEND_NIL,LENGTH]
  \\ ONCE_REWRITE_TAC [x64_add1_def,x64_add1_pre_def] \\ REPEAT STRIP_TAC
  \\ `LENGTH zs1 < dimword (:64)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LET_DEF,w2n_n2w,LENGTH_APPEND,LENGTH,
         word_add_n2w,n2w_11,LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,APPEND_11,CONS_11]
  THEN1 DECIDE_TAC
  \\ `(LENGTH zs1 + SUC (LENGTH zs)) < dimword (:64) /\
      LENGTH zs1 <> LENGTH zs1 + SUC (LENGTH zs)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LET_DEF,w2n_n2w,LENGTH_APPEND,LENGTH,
       word_add_n2w,n2w_11,LUPDATE_LENGTH,EL_LENGTH]
  \\ Tactical.REVERSE (Cases_on `h = ~0x0w`) \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.EXISTS_TAC `t::zs2`
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,LENGTH]
    \\ DECIDE_TAC) \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.PAT_ASSUM `!zss.bbb` (MP_TAC o Q.SPEC `SNOC 0w zs1`)
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [SNOC_INTRO,AC ADD_COMM ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,
       APPEND_11,CONS_11] \\ DECIDE_TAC) |> Q.SPECL [`zs`,`[]`]
  |> SIMP_RULE std_ss [APPEND,LENGTH];

(* mwi_div -- subtraction *)

val (res,x64_div_sub_aux_def) = x64_decompile_no_status "x64_div_sub_aux" `
      xor r10,r10
      inc r1
      jmp L2
  L1: insert r8_el_r10_ys
      insert r9_el_r10_zs
      sbb r8,r9
      insert lupdate_r10_zs_with_r8
      lea r10,[r10+1]
  L2: loop L1`

val (x64_div_sub_res,x64_div_sub_def) = x64_decompile "x64_div_sub" `
  insert x64_div_sub_aux`

val _ = add_compiled [x64_div_sub_res]

val (res,x64_div_sub_call_def,x64_div_sub_call_pre_def) = x64_compile `
  x64_div_sub_call (r1,r2:word64,r6:word64,ys,zs) =
    if r2 = 0w then (r6,ys,zs) else
    if r6 = 0w then (r6,ys,zs) else
      let r8 = r6 in
      let r9 = r6 in
      let r3 = r1 in
      let (r1,r8,r9,r10,ys,zs) = x64_div_sub (r1,r8,r9,ys,zs) in
      let r10 = r3 in
      let (r8,r10,zs) = x64_fix (r8,r10,zs) in
      let r6 = r10 in
        (r6,ys,zs)`

val x64_div_sub_aux_thm = prove(
  ``!ys zs ys1 zs1 ys2 zs2
     z_af z_of c z_pf z_sf z_zf r8 r9.
      (LENGTH zs1 = LENGTH ys1) /\ (LENGTH zs = LENGTH ys) /\
      LENGTH (zs1 ++ zs) + 1 < dimword (:64) ==>
      ?r8' r9' z_af' z_of' z_pf' z_sf' z_zf'.
        x64_div_sub_aux1_pre (n2w (LENGTH zs + 1),r8,r9,n2w (LENGTH zs1),
          ys1 ++ ys ++ ys2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) /\
        (x64_div_sub_aux1 (n2w (LENGTH zs + 1),r8,r9,n2w (LENGTH zs1),
          ys1 ++ ys ++ ys2,z_af,SOME c,
          z_of,z_pf,z_sf,z_zf,zs1 ++ zs ++ zs2) =
          (0w,r8',r9',n2w (LENGTH (zs1++zs)),ys1 ++ ys ++ ys2,z_af',
             SOME (~SND (mw_sub ys zs ~c)),z_of',z_pf',z_sf',z_zf',
                        zs1 ++ FST (mw_sub ys zs ~c) ++ zs2))``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def]
    \\ ONCE_REWRITE_TAC [x64_div_sub_aux_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL,mw_sub_def,LET_DEF])
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [x64_div_sub_aux_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,ADD1,n2w_w2n,w2n_n2w]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  \\ `LENGTH ys1 < dimword (:64) /\
      LENGTH zs1 < dimword (:64) /\
      LENGTH ys + 1 + 1 < dimword (:64) /\
      1 < dimword (:64)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [EL_LENGTH,LUPDATE_LENGTH,GSYM APPEND_ASSOC,APPEND]
  \\ Q.PAT_ASSUM `LENGTH zs1 = LENGTH ys1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EL_LENGTH,LUPDATE_LENGTH,n2w_11,GSYM APPEND_ASSOC,APPEND]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [word_add_n2w]
  \\ SIMP_TAC std_ss [SNOC_INTRO]
  \\ `LENGTH zs1 + 1 = LENGTH (SNOC h' ys1)` by
        FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1]
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "x64_div_sub_aux1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC,mw_sub_def,
       LET_DEF,single_sub_def,bool2num_thm,single_add_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [b2w_def]
  \\ `(18446744073709551616 <= b2n ~c + (w2n h' + w2n (~h))) =
      ~(w2n h' < b2n c + w2n h)` by METIS_TAC [sub_borrow_lemma]
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]
  \\ REPEAT (STRIP_TAC THEN1 DECIDE_TAC)
  \\ Cases_on `c` \\ FULL_SIMP_TAC std_ss [b2n_def]
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ blastLib.BBLAST_TAC)
  |> Q.SPECL [`ys`,`zs`,`[]`,`[]`]
  |> SIMP_RULE std_ss [APPEND,LENGTH] |> GEN_ALL;

val x64_div_sub_thm = prove(
  ``(LENGTH zs = LENGTH ys) /\ LENGTH zs + 1 < dimword (:64) ==>
    ?r8' r9'.
      x64_div_sub_pre (n2w (LENGTH ys),r8,r9,ys ++ ys2,zs ++ zs2) /\
      (x64_div_sub (n2w (LENGTH ys),r8,r9,ys ++ ys2,zs ++ zs2) =
        (0x0w,r8',r9',n2w (LENGTH ys),ys ++ ys2,
         FST (mw_sub ys zs T) ++ zs2))``,
  SIMP_TAC std_ss [x64_div_sub_def]
  \\ ONCE_REWRITE_TAC [x64_div_sub_aux_def]
  \\ SIMP_TAC std_ss [LET_DEF,WORD_SUB_RZERO,word_add_n2w]
  \\ REPEAT STRIP_TAC \\ ASSUME_TAC x64_div_sub_aux_thm
  \\ SEP_I_TAC "x64_div_sub_aux1" \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []);


(* mwi_div -- integer division *)

val (res,x64_idiv_mod_header_def,x64_idiv_mod_header_pre_def) = x64_compile `
  x64_idiv_mod_header (r6:word64,r11:word64) =
    if r6 = 0w then r6 else
      let r6 = r6 << 1 in
        if r11 && 1w = 0w then r6 else
          let r6 = r6 + 1w in r6`;

val x64_idiv_mod_header_thm = prove(
  ``LENGTH xs < dimword (:64) ==>
    (x64_idiv_mod_header (n2w (LENGTH xs),x64_header (t,ys)) =
     x64_header (xs <> [] /\ t,xs))``,
  SIMP_TAC std_ss [x64_idiv_mod_header_def,x64_header_sign,n2w_11,
    ZERO_LT_dimword,LENGTH_NIL,LET_DEF,x64_header_def,word_lsl_n2w]
  \\ Cases_on `xs = []` \\ ASM_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ ASM_SIMP_TAC (srw_ss()) []);

val (x64_idiv_res,x64_idiv_def,x64_idiv_pre_def) = x64_compile `
  x64_idiv (r3,r10,r11,xs,ys,zs,ss) =
    let r0 = r10 >>> 1 in
    let r1 = r11 >>> 1 in
    let r10 = r10 ?? r11 in
    let r10 = r10 && 1w in
    let ss = r10 :: ss in
    let ss = r11 :: ss in
    let (r0,r3,r6,xs,ys,zs,ss) = x64_div (r0,r1,r3,xs,ys,zs,ss) in
    let (r11,ss) = (HD ss, TL ss) in
      if r3 <> 0w then
        let (r2,ss) = (HD ss, TL ss) in
        let r1 = r11 >>> 1 in
        let (r6,ys,zs) = x64_div_sub_call (r1,r2,r6,ys,zs) in
        let r6 = x64_idiv_mod_header (r6,r11) in
        let r11 = r6 in
          (r11,xs,ys,zs,ss)
      else
        let r10 = r0 in
        let r8 = r10 in
        let (r8,r10,zs) = x64_fix (r8,r10,zs) in
        let r11 = r10 in
        let (r2,ss) = (HD ss, TL ss) in
        let r3 = r2 in
        let (r11,zs) = x64_add1_call (r2,r6,r11,zs) in
          if r11 = 0w then (r11,xs,ys,zs,ss) else
            let r11 = r11 << 1 in
            let r11 = r11 + r3 in
              (r11,xs,ys,zs,ss)`

val x64_header_XOR = prove(
  ``!s t. ((x64_header (s,xs) ?? x64_header (t,ys)) && 0x1w:word64) =
          (b2w (s <> t)):word64``,
  SIMP_TAC std_ss [WORD_RIGHT_AND_OVER_XOR,x64_header_AND_1]
  \\ Cases \\ Cases \\ EVAL_TAC);

val b2w_EQ_0w = prove(
  ``!b. (b2w b = 0w:word64) = ~b``,
  Cases \\ EVAL_TAC);

val mwi_divmod_alt_def = Define `
  mwi_divmod_alt w s_xs t_ys =
    if w = 0w then mwi_div s_xs t_ys else mwi_mod s_xs t_ys`;

val x64_idiv_thm = prove(
  ``LENGTH xs + LENGTH ys <= LENGTH zs /\ LENGTH zs < dimword (:63) /\
    mw_ok xs /\ mw_ok ys /\ ys <> [] ==>
    ?zs1.
      x64_idiv_pre (r3,x64_header (s,xs),x64_header (t,ys),xs,ys,zs,ss) /\
      (x64_idiv (r3,x64_header (s,xs),x64_header (t,ys),xs,ys,zs,ss) =
        (x64_header ((mwi_divmod_alt r3 (s,xs) (t,ys))),xs,ys,
         SND ((mwi_divmod_alt r3 (s,xs) (t,ys)))++zs1,ss)) /\
      (LENGTH (SND ((mwi_divmod_alt r3 (s,xs) (t,ys)))++zs1) = LENGTH zs) ``,
  FULL_SIMP_TAC std_ss [x64_idiv_def,x64_idiv_pre_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [x64_header_EQ,mwi_mul_def,x64_length]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [x64_header_XOR]
  \\ `LENGTH xs < dimword (:63) /\ LENGTH ys < dimword (:63)` by DECIDE_TAC
  \\ `LENGTH zs < dimword (:64)` by (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ IMP_RES_TAC x64_length \\ FULL_SIMP_TAC std_ss []
  \\ `mw2n ys <> 0` by ALL_TAC THEN1
   (SIMP_TAC std_ss [GSYM mw_fix_NIL]
    \\ FULL_SIMP_TAC std_ss [mw_ok_mw_fix_ID])
  \\ `?res mod c. (mw_div xs ys = (res,mod,c))` by METIS_TAC [PAIR]
  \\ `c /\ (LENGTH mod = LENGTH ys)` by METIS_TAC [mw_div_thm,mw_ok_mw_fix_ID]
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (x64_div_thm |> GEN_ALL)
  \\ SEP_I_TAC "x64_div"
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ NTAC 3 (POP_ASSUM MP_TAC) \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ Cases_on `r3 <> 0w` \\ FULL_SIMP_TAC std_ss [mwi_divmod_alt_def] THEN1
   (FULL_SIMP_TAC std_ss [x64_div_sub_call_def,x64_div_sub_call_pre_def]
    \\ FULL_SIMP_TAC std_ss [TL,mwi_mod_def,mwi_divmod_def,LET_DEF,HD,NOT_CONS_NIL,
         x64_header_XOR]
    \\ Cases_on `s = t` \\ FULL_SIMP_TAC std_ss [EVAL ``b2w F``] THEN1
     (FULL_SIMP_TAC std_ss [x64_idiv_mod_header_thm]
      \\ ASSUME_TAC (Q.ISPEC `mod:word64 list` (GSYM mw_fix_thm))
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
      \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11]
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE]
      \\ `LENGTH (mw_fix mod) <= LENGTH mod` by METIS_TAC [LENGTH_mw_fix]
      \\ DECIDE_TAC)
    \\ Cases_on `mw_fix mod = []`
    \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND,LENGTH_APPEND]
    THEN1 (SIMP_TAC std_ss [x64_idiv_mod_header_def] \\ EVAL_TAC)
    \\ FULL_SIMP_TAC std_ss [EVAL ``b2w T = 0x0w:word64``,n2w_11,ZERO_LT_dimword]
    \\ FULL_SIMP_TAC std_ss [LENGTH_NIL]
    \\ (x64_div_sub_thm |> Q.INST [`ys2`|->`[]`]
        |> SIMP_RULE std_ss [APPEND_NIL] |> GEN_ALL |> ASSUME_TAC)
    \\ SEP_I_TAC "x64_div_sub" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL]
           \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `LENGTH ys = LENGTH (FST (mw_sub ys mod T))` by ALL_TAC THEN1
     (Cases_on `mw_sub ys mod T` \\ IMP_RES_TAC LENGTH_mw_sub
      \\ FULL_SIMP_TAC std_ss [])
    \\ ASM_SIMP_TAC std_ss []
    \\ ASSUME_TAC x64_fix_thm
    \\ SEP_I_TAC "x64_fix"
    \\ `LENGTH (FST (mw_sub ys mod T)) < dimword (:64)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM mw_subv_def]
    \\ `mw_subv ys (mw_fix mod) = mw_subv ys mod` by ALL_TAC
    THEN1 (SIMP_TAC std_ss [mw_subv_def,mw_sub_mw_fix])
    \\ FULL_SIMP_TAC std_ss []
    \\ `LENGTH (mw_subv ys mod) <= LENGTH ys` by ALL_TAC
    THEN1 (MATCH_MP_TAC LENGTH_mw_subv \\ FULL_SIMP_TAC std_ss [])
    \\ `LENGTH (mw_subv ys mod) < dimword (:64)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [x64_idiv_mod_header_thm]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11]
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE]
    \\ SIMP_TAC std_ss [mw_subv_def]
    \\ `LENGTH (mw_fix (FST (mw_sub ys mod T))) <= LENGTH (FST (mw_sub ys mod T))`
          by FULL_SIMP_TAC std_ss [LENGTH_mw_fix] \\ DECIDE_TAC)
  \\ `LENGTH res < dimword (:64)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [mwi_div_def]
  \\ MP_TAC (x64_fix_thm |> Q.SPECL
       [`res`,`zs2`,`n2w (LENGTH (res:word64 list))`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [HD,TL]
  \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [x64_add1_call_def,x64_add1_call_pre_def,
                           LET_DEF,mwi_divmod_def,b2w_EQ_0w]
  \\ `LENGTH (mw_fix res) <= LENGTH res` by
        FULL_SIMP_TAC std_ss [LENGTH_mw_fix]
  \\ `LENGTH (mw_fix res) < dimword (:64)` by DECIDE_TAC
  \\ Cases_on `s = t` \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword] THEN1
   (SIMP_TAC (srw_ss()) [word_lsl_n2w,b2w_def,b2n_def,x64_header_def]
    \\ Cases_on `LENGTH (mw_fix res) = 0` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11,
         LENGTH_APPEND,LENGTH_REPLICATE] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [LENGTH_NIL]
  \\ Cases_on `mw_fix mod = []`
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL] THEN1
   (Cases_on `mw_fix res = []` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11,
         LENGTH_APPEND,LENGTH_REPLICATE]
    \\ SIMP_TAC (srw_ss()) [word_lsl_n2w,b2w_def,b2n_def,x64_header_def]
    \\ DECIDE_TAC)
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ Q.ABBREV_TAC `ts1 = REPLICATE (LENGTH res - LENGTH (mw_fix res)) 0x0w ++ zs2`
  \\ ASSUME_TAC (x64_add1_thm |> GEN_ALL)
  \\ SEP_I_TAC "x64_add1" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
    (Q.UNABBREV_TAC `ts1`
     \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,GSYM LENGTH_NIL,
          LENGTH_REPLICATE,x64_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND]
     \\ DECIDE_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL]
  \\ Cases_on `mw_addv (mw_fix res) [] T = []`
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL,
       x64_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND]
  THEN1 (Q.UNABBREV_TAC `ts1`
    \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL,LENGTH_REPLICATE,
         x64_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND]
    \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL,LENGTH_REPLICATE,
         x64_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND,APPEND_11]
  \\ FULL_SIMP_TAC std_ss [b2w_def,b2n_def]
  \\ SIMP_TAC (srw_ss()) [word_lsl_n2w,word_add_n2w]
  \\ Q.UNABBREV_TAC `ts1`
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL,LENGTH_REPLICATE,
         x64_header_def,LENGTH,APPEND,word_add_n2w,LENGTH_APPEND]
  \\ DECIDE_TAC);


(* int to decimal conversion *)

val (res,x64_to_dec_def,x64_to_dec_pre_def) = x64_compile `
  x64_to_dec (r9,r10,zs,ss) =
    let r2 = 0w in
    let r11 = r10 in
    let (r2,r9,r10,zs) = x64_simple_div1 (r2,r9,r10,zs) in
    let r2 = r2 + 0x30w in
    let ss = r2 :: ss in
    let r8 = r10 in
    let r10 = r11 in
    let (r8,r10,zs) = x64_fix (r8,r10,zs) in
      if r10 = 0w then (zs,ss) else
        x64_to_dec (r9,r10,zs,ss)`

val (res,x64_int_to_dec_def,x64_int_to_dec_pre_def) = x64_compile `
  x64_int_to_dec (r10,xs,zs,ss) =
    let r1 = r10 in
    let r10 = r10 >>> 1 in
    let (xs,zs) = x64_copy_over (r10,xs,zs) in
    let r10 = r1 >>> 1 in
    let r9 = 10w in
    let (zs,ss) = x64_to_dec (r9,r10,zs,ss) in
      if r1 && 1w = 0w then (xs,zs,ss) else
        let r2 = 0x7Ew in
        let ss = r2 :: ss in
          (xs,zs,ss)`

val x64_to_dec_thm = prove(
  ``!xs ys zs ss.
      LENGTH xs < dimword (:64) /\ (mw_to_dec xs = (ys,T)) ==>
      ?zs1.
        x64_to_dec_pre (10w,n2w (LENGTH xs),xs++zs,ss) /\
        (x64_to_dec (10w,n2w (LENGTH xs),xs++zs,ss) = (zs1,ys ++ ss)) /\
        (LENGTH zs1 = LENGTH xs + LENGTH zs)``,
  HO_MATCH_MP_TAC mw_to_dec_ind \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [Once mw_to_dec_def]
  \\ FULL_SIMP_TAC std_ss [EVAL ``dimword (:64) <= 10``]
  \\ `?qs r c1. mw_simple_div 0x0w (REVERSE xs) 0xAw = (qs,r,c1)` by METIS_TAC [PAIR]
  \\ `?res c2. mw_to_dec (mw_fix (REVERSE qs)) = (res,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ ONCE_REWRITE_TAC [x64_to_dec_def,x64_to_dec_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ STRIP_TAC
  \\ `c1` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
  THEN1 (Cases_on `LENGTH (mw_fix (REVERSE qs)) = 0` \\ FULL_SIMP_TAC std_ss [])
  \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ IMP_RES_TAC x64_simple_div1_thm
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LENGTH_mw_simple_div
  \\ MP_TAC (x64_fix_thm |> Q.SPECL [`REVERSE qs`,`zs`,`0w`])
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ STRIP_TAC
  \\ `LENGTH (mw_fix (REVERSE qs)) <= LENGTH (REVERSE qs)` by
        METIS_TAC [LENGTH_mw_fix]
  \\ `LENGTH (mw_fix (REVERSE qs)) < dimword (:64)` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ FULL_SIMP_TAC std_ss [LENGTH_NIL]
  \\ Cases_on `mw_fix (REVERSE qs) = []` \\ FULL_SIMP_TAC std_ss [LENGTH]
  THEN1 (SIMP_TAC std_ss [LENGTH_REPLICATE,LENGTH_APPEND] \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ SEP_I_TAC "x64_to_dec"
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LENGTH_REPLICATE,LENGTH_APPEND,REVERSE_APPEND,REVERSE_DEF]
  \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ DECIDE_TAC);

val x64_int_to_dec_thm = prove(
  ``(mwi_to_dec (s,xs) = (res,T)) /\ LENGTH zs < dimword (:63) /\
    LENGTH xs <= LENGTH zs ==>
    ?zs1.
      (x64_int_to_dec_pre (x64_header(s,xs),xs,zs,ss)) /\
      (x64_int_to_dec (x64_header(s,xs),xs,zs,ss) = (xs,zs1,res ++ ss)) /\
      (LENGTH zs1 = LENGTH zs)``,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [x64_int_to_dec_def,x64_int_to_dec_pre_def,LET_DEF] \\ STRIP_TAC
  \\ `LENGTH xs < dimword (:63)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [x64_length]
  \\ IMP_RES_TAC LESS_EQ_LENGTH
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (x64_copy_over_thm |> Q.SPECL [`xs0`,`zs0`,`[]`] |> GEN_ALL)
  \\ FULL_SIMP_TAC std_ss [APPEND_NIL]
  \\ `LENGTH xs + LENGTH xs2 < dimword (:64)` by
        (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ SEP_I_TAC "x64_copy_over"
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [mwi_to_dec_def,LET_DEF]
  \\ Cases_on `mw_to_dec xs` \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ `LENGTH xs < dimword (:64)` by DECIDE_TAC
  \\ IMP_RES_TAC x64_to_dec_thm
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`xs2`,`ss`])
  \\ FULL_SIMP_TAC std_ss [x64_header_sign]
  \\ Cases_on `s` \\ FULL_SIMP_TAC std_ss [APPEND]);


(* top-level entry point *)

val int_op_rep_def = Define `
  (int_op_rep Add = 0w) /\
  (int_op_rep Sub = 1w) /\
  (int_op_rep Lt  = 2w) /\
  (int_op_rep Eq  = 3w) /\
  (int_op_rep Mul = 4w) /\
  (int_op_rep Div = 5w) /\
  (int_op_rep Mod = 6w) /\
  (int_op_rep Dec = 7w:'a word)`;

val (res,x64_isub_flip_def,x64_isub_flip_pre_def) = x64_compile `
  x64_isub_flip (r1:word64,r3:word64) =
    if r3 = 0w then (r1,r3) else let r1 = r1 ?? 1w in (r1,r3)`

val (res,x64_icmp_res_def,x64_icmp_res_pre_def) = x64_compile `
  x64_icmp_res (r10:word64,r3:word64) =
    if r3 = 2w then (* lt *)
      if r10 = 1w then let r10 = 1w in r10
                  else let r10 = 0w in r10
    else (* eq *)
      if r10 = 0w then let r10 = 1w in r10
                  else let r10 = 0w in r10:word64`

val (res,x64_full_cmp_def,x64_full_cmp_pre_def) = x64_compile `
  x64_full_cmp (r3,r10,r11,xs,ys,zs) =
    let (r10,xs,ys) = x64_icompare (r10,r11,xs,ys) in
    let r10 = x64_icmp_res (r10,r3) in
      if r10 = 0w then (r10,xs,ys,zs) else
        let r0 = 1w:word64 in
        let r10 = 0w:word64 in
        let zs = LUPDATE r0 (w2n r10) zs in
        let r10 = 2w in
          (r10,xs,ys,zs)`

val NumABS_LEMMA = prove(
  ``(Num (ABS (0:int)) = 0:num) /\ (Num (ABS (1:int)) = 1:num)``,
  intLib.COOPER_TAC);

val x64_full_cmp_lt = prove(
  ``((x64_header (s,xs) = 0x0w) <=> (xs = [])) /\ mw_ok xs /\
    ((x64_header (t,ys) = 0x0w) <=> (ys = [])) /\ mw_ok ys /\
    LENGTH xs < dimword (:63) /\ LENGTH ys < dimword (:63) /\
    LENGTH xs + LENGTH ys < LENGTH zs /\ LENGTH zs < dimword (:63) ==>
    ?zs1.
      x64_full_cmp_pre (2w,x64_header (s,xs),x64_header (t,ys),xs,ys,zs) /\
      (x64_full_cmp (2w,x64_header (s,xs),x64_header (t,ys),xs,ys,zs) =
       (x64_header (mwi_op Lt (s,xs) (t,ys)),xs,ys,
        SND (mwi_op Lt (s,xs) (t,ys)) ++ zs1)) /\
      (LENGTH (SND (mwi_op Lt (s,xs) (t,ys)) ++ zs1) = LENGTH zs)``,
  SIMP_TAC std_ss [x64_full_cmp_def,x64_full_cmp_pre_def,LET_DEF] \\ STRIP_TAC
  \\ MP_TAC x64_icompare_thm \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def] \\ SIMP_TAC std_ss [mwi_lt_def]
  \\ Cases_on `mwi_compare (s,xs) (t,ys)`
  \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,x64_icmp_res_def,n2w_11,LET_DEF]
  THEN1 (Q.EXISTS_TAC `zs` \\ SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``] \\ EVAL_TAC)
  \\ REV (Cases_on `x`)
  \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,x64_icmp_res_def,n2w_11,LET_DEF]
  THEN1 (Q.EXISTS_TAC `zs` \\ SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``] \\ EVAL_TAC)
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.EXISTS_TAC `t'` \\ FULL_SIMP_TAC std_ss [LUPDATE_def]
  \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [ADD1] \\ DECIDE_TAC);

val x64_full_cmp_eq = prove(
  ``((x64_header (s,xs) = 0x0w) <=> (xs = [])) /\ mw_ok xs /\
    ((x64_header (t,ys) = 0x0w) <=> (ys = [])) /\ mw_ok ys /\
    LENGTH xs < dimword (:63) /\ LENGTH ys < dimword (:63) /\
    LENGTH xs + LENGTH ys < LENGTH zs /\ LENGTH zs < dimword (:63) ==>
    ?zs1.
      x64_full_cmp_pre (3w,x64_header (s,xs),x64_header (t,ys),xs,ys,zs) /\
      (x64_full_cmp (3w,x64_header (s,xs),x64_header (t,ys),xs,ys,zs) =
       (x64_header (mwi_op Eq (s,xs) (t,ys)),xs,ys,
        SND (mwi_op Eq (s,xs) (t,ys)) ++ zs1)) /\
      (LENGTH (SND (mwi_op Eq (s,xs) (t,ys)) ++ zs1) = LENGTH zs)``,
  SIMP_TAC std_ss [x64_full_cmp_def,x64_full_cmp_pre_def,LET_DEF] \\ STRIP_TAC
  \\ MP_TAC x64_icompare_thm \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def] \\ SIMP_TAC std_ss [mwi_eq_def]
  \\ REV (Cases_on `mwi_compare (s,xs) (t,ys)`) THEN1
   (Cases_on `x`
    \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,x64_icmp_res_def,n2w_11,LET_DEF]
    \\ Q.EXISTS_TAC `zs` \\ SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``] \\ EVAL_TAC)
  \\ SIMP_TAC std_ss [cmp2w_def]
  \\ FULL_SIMP_TAC (srw_ss()) [cmp2w_def,x64_icmp_res_def,n2w_11,LET_DEF]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Q.EXISTS_TAC `t'` \\ FULL_SIMP_TAC std_ss [LUPDATE_def]
  \\ SIMP_TAC std_ss [i2mw_def,NumABS_LEMMA,EVAL ``n2mw 0``]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [ADD1] \\ DECIDE_TAC);

val (x64_iop_res,x64_iop_def,x64_iop_pre_def) = x64_compile `
  x64_iop (r0,r1,r3,xs,ys,zs,xa,ya,ss) =
    if r3 <+ 2w then (* + or - *)
      let (r1,r3) = x64_isub_flip (r1,r3) in
      let r2 = r1 in
      let r1 = r0 in
      let (r10,xs,ys,zs,xa,ya) = x64_iadd (r1,r2,xs,ys,zs,xa,ya) in
        (r10,xs,ys,zs,xa,ya,ss)
    else if r3 <+ 4w then (* < or = *)
      let r10 = r0 in
      let r11 = r1 in
      let (r10,xs,ys,zs) = x64_full_cmp (r3,r10,r11,xs,ys,zs) in
        (r10,xs,ys,zs,xa,ya,ss)
    else if r3 = 4w then (* * *)
      let r2 = r1 in
      let r1 = r0 in
      let (r10,xs,ys,zs) = x64_imul (r1,r2,xs,ys,zs) in
        (r10,xs,ys,zs,xa,ya,ss)
    else if r3 <+ 7w then (* / or % *)
      let r3 = r3 - 5w in
      let r10 = r0 in
      let r11 = r1 in
      let (r11,xs,ys,zs,ss) = x64_idiv (r3,r10,r11,xs,ys,zs,ss) in
      let r10 = r11 in
        (r10,xs,ys,zs,xa,ya,ss)
    else (* print to dec *)
      let r10 = r0 in
      let (xs,zs,ss) = x64_int_to_dec (r10,xs,zs,ss) in
      let r10 = 0w in
        (r10,xs,ys,zs,xa,ya,ss)`

val _ = save_thm("x64_iop_res",x64_iop_res);

val x64_header_XOR_1 = prove(
  ``x64_header (s,xs) ?? 1w = x64_header (~s,xs)``,
  Cases_on `s` \\ SIMP_TAC std_ss [x64_header_def,GSYM word_mul_n2w]
  \\ blastLib.BBLAST_TAC);

val x64_iop_thm = store_thm("x64_iop_thm",
  ``((x64_header (s,xs) = 0x0w) <=> (xs = [])) /\ mw_ok xs /\
    ((x64_header (t,ys) = 0x0w) <=> (ys = [])) /\ mw_ok ys /\
    LENGTH xs + LENGTH ys < LENGTH zs /\ LENGTH zs < dimword (:63) /\
    (((iop = Div) \/ (iop = Mod)) ==> ys <> []) ==>
    ?zs1.
      x64_iop_pre (x64_header (s,xs),x64_header (t,ys),int_op_rep iop,
                   xs,ys,zs,xa,ya,ss) /\
      (x64_iop (x64_header (s,xs),x64_header (t,ys),int_op_rep iop,
                xs,ys,zs,xa,ya,ss) =
       (x64_header (mwi_op iop (s,xs) (t,ys)),xs,ys,
        SND (mwi_op iop (s,xs) (t,ys)) ++ zs1,xa,ya,
        if iop = Dec then MAP (n2w o ORD) (int_to_str (mw2i (s,xs))) ++ ss
        else ss)) /\
      (LENGTH (SND (mwi_op iop (s,xs) (t,ys)) ++ zs1) = LENGTH zs)``,
  Cases_on `iop` \\ SIMP_TAC std_ss [int_op_rep_def] \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < dimword (:63) /\ LENGTH ys < dimword (:63)` by DECIDE_TAC
  \\ `LENGTH xs + LENGTH ys <= LENGTH zs` by DECIDE_TAC
  \\ SIMP_TAC std_ss [x64_iop_def,x64_iop_pre_def,WORD_LO]
  \\ SIMP_TAC (srw_ss()) [w2n_n2w,LET_DEF,x64_isub_flip_def]
  THEN1 (MP_TAC x64_iadd_thm \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (MP_TAC (x64_iadd_thm |> Q.INST [`t`|->`~t`])
    \\ FULL_SIMP_TAC std_ss [x64_header_XOR_1]
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def,mwi_sub_def]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (MP_TAC x64_imul_thm \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (MP_TAC (x64_idiv_thm |> Q.INST [`r3`|->`0w`])
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ FULL_SIMP_TAC (srw_ss()) [mwi_divmod_alt_def])
  THEN1 (MP_TAC (x64_idiv_thm |> Q.INST [`r3`|->`1w`])
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ FULL_SIMP_TAC (srw_ss()) [mwi_divmod_alt_def])
  THEN1 (MP_TAC x64_full_cmp_lt \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (MP_TAC x64_full_cmp_eq \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [mwi_op_def]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [mwi_op_def]
  \\ MP_TAC (INST_TYPE [``:'a``|->``:64``] mwi_to_dec_thm)
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ `((xs = []) ==> ~s)` by ALL_TAC
  THEN1 (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [EVAL ``x64_header (T,[])=0x0w``])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC x64_int_to_dec_thm
  \\ POP_ASSUM (MP_TAC o Q.SPEC `zs`) \\ POP_ASSUM (K ALL_TAC)
  \\ `LENGTH xs <= LENGTH zs /\ LENGTH zs < dimword (:63)` by
        (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `ss`)
  \\ FULL_SIMP_TAC std_ss []
  \\ EVAL_TAC);

val _ = export_theory();
