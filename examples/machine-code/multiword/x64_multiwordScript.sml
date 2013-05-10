
open HolKernel Parse boolLib bossLib;
val _ = new_theory "x64_multiword";

infix \\ val op \\ = op THEN;
open multiwordTheory;

open progTheory;
open decompilerLib x64_codegenLib prog_x64Lib x64_encodeLib x64_compilerLib;
open wordsTheory wordsLib addressTheory arithmeticTheory listTheory pairSyntax;
open addressTheory pairTheory set_sepTheory rich_listTheory integerTheory;

val REV = Tactical.REVERSE;

fun x64_decompile name asm =
  decompile_strings x64_tools_64 name (assemble asm);

fun x64_decompile_no_status name asm =
  decompile_strings x64_tools_64_no_status name (assemble asm);

(*

  This file produces a single blob of x64 machine code that is able to
  do any of the following arithmetic functions over arbitrary size
  integer inputs.

    + - * div mod < = dec

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
val mov_r10_xs = READ_XS x8 x10;
val mov_r11_xs = READ_XS x8 x11;
val mov_r12_xs = READ_XS x8 x12;

val _ = add_decompiled("r8_el_r10_xs",mov_r10_xs,5,SOME 5);

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

val mov_r10_ys = READ_YS x2 x10;
val mov_r11_ys = READ_YS x2 x11;
val mov_r12_ys = READ_YS x2 x12;
val mov_r10_ys = READ_YS x8 x10;
val mov_r11_ys = READ_YS x8 x11;
val mov_r12_ys = READ_YS x8 x12;
val mov_r10_ys = READ_YS x9 x10;
val mov_r11_ys = READ_YS x9 x11;
val mov_r12_ys = READ_YS x9 x12;

val _ = add_decompiled("r9_el_r10_ys",mov_r10_ys,4,SOME 4);

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

val mov_r10_zs = READ_ZS x3 x10;
val mov_r11_zs = READ_ZS x3 x11;
val mov_r12_zs = READ_ZS x3 x12;
val mov_r10_zs = READ_ZS x8 x10;
val mov_r11_zs = READ_ZS x8 x11;
val mov_r12_zs = READ_ZS x8 x12;

val _ = add_decompiled("r8_el_r10_zs",mov_r10_zs,4,SOME 4);

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

val (res,x64_icompare_def,x64_icompare_pre_def) = x64_compile `
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

val (x64_trailing_res,x64_trailing_def) = x64_decompile "x64_trailing" `
  L1: test r10,r10
      je L2
      dec r10
      insert r8_el_r10_zs
      test r8,r8
      je L1
      inc r10
  L2: `

val _ = add_compiled [x64_trailing_res];

val (x64_sub_res,x64_sub_def) = x64_decompile "x64_sub" `
      sub r2,r1
      insert x64_sub_loop
      insert x64_trailing`

val _ = add_compiled [x64_sub_res]

val REPLICATE_SNOC = prove(
  ``!n x. REPLICATE (SUC n) x = SNOC x (REPLICATE n x)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [REPLICATE]);

val x64_trailing_thm = prove(
  ``!zs zs1 r8.
      LENGTH zs < dimword(:64) ==>
      ?r8'.
        x64_trailing_pre (r8,n2w (LENGTH zs),zs++zs1) /\
        (x64_trailing (r8,n2w (LENGTH zs),zs++zs1) =
         (r8',n2w (LENGTH (mw_trailing zs)),
          mw_trailing zs ++ REPLICATE (LENGTH zs - LENGTH (mw_trailing zs)) 0w ++ zs1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [x64_trailing_def,mw_trailing_def]
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,ADD1,GSYM word_sub_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC (DECIDE ``n + 1 < k ==> n < k:num``)
  \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,
       rich_listTheory.EL_LENGTH_APPEND,NULL,HD]
  \\ REV (Cases_on `x = 0w`) \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,REPLICATE,APPEND,
      GSYM APPEND_ASSOC,word_add_n2w] \\ DECIDE_TAC)
  \\ SEP_I_TAC "x64_trailing" \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 DECIDE_TAC \\ AP_TERM_TAC
  \\ `LENGTH (mw_trailing zs) <= LENGTH zs` by
      FULL_SIMP_TAC std_ss [LENGTH_mw_trailing]
  \\ `LENGTH zs + 1 - LENGTH (mw_trailing zs) =
        SUC (LENGTH zs - LENGTH (mw_trailing zs))` by DECIDE_TAC
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
             SOME (~SND (mw_sub xs (MAP (\x.0w) xs) ~c)),z_of',z_pf',z_sf',z_zf',
                        zs1 ++ FST (mw_sub xs (MAP (\x.0w) xs) ~c) ++ zs2))``,
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
  \\ FULL_SIMP_TAC std_ss [mw_subv_def,LET_DEF,mw_sub2_def,
       rich_listTheory.DROP_LENGTH_APPEND,
       rich_listTheory.TAKE_LENGTH_APPEND]
  \\ `?qs1 c1. mw_sub xs1 ys T = (qs1,c1)` by METIS_TAC [PAIR]
  \\ `?qs2 c2. mw_sub xs2 (MAP (\x.0w) xs2) c1 = (qs2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
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
  \\ IMP_RES_TAC x64_trailing_thm \\ SEP_I_TAC "x64_trailing"
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

val (res,x64_iadd_def,x64_iadd_pre_def) = x64_compile `
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

val (res,x64_imul_def,x64_imul_pre_def) = x64_compile `
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
            let (r8,r10,zs) = x64_trailing (r8,r10,zs) in
            let r10 = r10 << 1 in
              (r10,xs,ys,zs)
          else
            let r7 = r1 >>> 1 in
            let r9 = r2 >>> 1 in
            let r10 = 0w in
            let r12 = r10 in
            let (r10,xs,ys,zs) = x64_mul (r7,r9,r10,r12,xs,ys,zs) in
            let r8 = 0w in
            let (r8,r10,zs) = x64_trailing (r8,r10,zs) in
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
        (x64_header (mwi_mul_simple (s,xs) (t,ys)),xs,ys,
         SND (mwi_mul_simple (s,xs) (t,ys))++zs1)) /\
      (LENGTH (SND (mwi_mul_simple (s,xs) (t,ys))++zs1) = LENGTH zs) ``,
  FULL_SIMP_TAC std_ss [x64_imul_def,x64_imul_pre_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [x64_header_EQ,mwi_mul_simple_def,x64_length]
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
  \\ ASSUME_TAC x64_trailing_thm \\ SEP_I_TAC "x64_trailing" \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `s = t` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [x64_header_def,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_REPLICATE,WORD_MUL_LSL,word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC]
  \\ Q.ABBREV_TAC `ts = mw_mul xs ys (MAP (\x. 0x0w) ys)`
  \\ `LENGTH (mw_trailing ts) <= LENGTH ts` by FULL_SIMP_TAC std_ss [LENGTH_mw_trailing]
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


val _ = export_theory();

