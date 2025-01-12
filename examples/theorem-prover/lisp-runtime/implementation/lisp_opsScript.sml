open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_ops";
val _ = ParseExtras.temp_loose_equality()
open lisp_symbolsTheory lisp_sexpTheory lisp_consTheory lisp_invTheory;
open lisp_equalTheory lisp_codegenTheory lisp_initTheory lisp_symbolsTheory;

(* --- *)

open compilerLib codegenLib decompilerLib;
open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory bitTheory;

open progTheory set_sepTheory helperLib;
open prog_x64Theory prog_x64Lib x64_encodeLib;
open stop_and_copyTheory;

fun allowing_rebinds f x = Feedback.trace ("Theory.allow_rebinds", 1) f x
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val LISP = lisp_inv_def |> SPEC_ALL |> concl |> dest_eq |> fst;
val REST = LISP |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;
val STATINV = LISP |> car |> car |> cdr;
val VAR_REST = LISP |> car |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;

(*

Use of cs list:
  EL 0..2 cs -- used by zIO
  EL 3 cs    -- used by parser, size of array to allocate (init only)
  EL 4 cs    -- code heap: pointer to start of code heap
  EL 5 cs    -- code heap: length (in bytes) of code heap (init only)

  EL 3 cs    -- code pointer: parse                DONE
  EL 5 cs    -- code pointer: gc                   DONE
  EL 6 cs    -- code pointer: equal                DONE
  EL 7 cs    -- code pointer: print                DONE
  EL 8 cs    -- code pointer: compile              DONE
  EL 9 cs    -- code pointer: compile instruction  DONE

*)


val zCODE_MEMORY_def = Define `
  (zCODE_MEMORY NONE dd d = emp) /\
  (zCODE_MEMORY (SOME F) dd d = zBYTE_MEMORY dd d) /\
  (zCODE_MEMORY (SOME T) dd d = zCODE (zCODE_SET dd d))`;

val zCODE_UNCHANGED_def = Define `
  (zCODE_UNCHANGED NONE dd d = emp) /\
  (zCODE_UNCHANGED (SOME x) dd d = cond (x = (dd,d)))`;

val zLISP_ALT_def = Define `
  zLISP_ALT side (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) =
    SEP_EXISTS tw0 tw1 tw2 wsp bp sp w0 w1 w2 w3 w4 w5 wi we df f dg g bp2 ds sa1 sa2 sa3 dd d.
      zR 0w tw0 * zR 1w tw1 * zR 2w tw2 * zR 3w wsp * zR 6w bp * zR 7w sp *
      zR 8w (w2w w0) * zR 9w (w2w w1) * zR 10w (w2w w2) *
      zR 11w (w2w w3) * zR 12w (w2w w4) * zR 13w (w2w w5) * zSTACK rbp qs *
      zR 14w wi * zR 15w we * zMEMORY df f * zBYTE_MEMORY dg g * zCODE_MEMORY ddd dd d *
      zIO (EL 0 cs,EL 1 cs,EL 2 cs,EL 0 ds) io * zCODE_UNCHANGED cu dd d *
        cond (lisp_inv (a1,a2,sl,sl1,e,ex,cs,ok) (x0,x1,x2,x3,x4,x5,^VAR_REST)
                 (w0,w1,w2,w3,w4,w5,df,f,^REST) /\
              side wsp wi we ds tw2)`;

val zLISP_R_def = Define `
  zLISP_R (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) =
    SEP_EXISTS tw0 tw1 tw2 wsp bp sp w0 w1 w2 w3 w4 w5 wi we df f dg g bp2 ds sa1 sa2 sa3 dd d.
      zR 0w tw0 * zR 2w (EL 1 cs) * zR 3w wsp * zR 6w bp * zR 7w sp *
      zR 8w (w2w w0) * zR 9w (w2w w1) * zR 10w (w2w w2) *
      zR 11w (w2w w3) * zR 12w (w2w w4) * zR 13w (w2w w5) * zSTACK rbp qs *
      zR 14w wi * zR 15w we * zMEMORY df f * zBYTE_MEMORY dg g * zCODE_MEMORY ddd dd d *
      zIO_R (EL 0 cs,EL 1 cs,EL 2 cs) io * zCODE_UNCHANGED cu dd d *
        cond (lisp_inv (a1,a2,sl,sl1,e,ex,cs,ok) (x0,x1,x2,x3,x4,x5,^VAR_REST)
                 (w0,w1,w2,w3,w4,w5,df,f,^REST))`;

val zLISP_INIT_def = Define `
  zLISP_INIT (a1,a2,sl,sl1,e,ex,rbp,cs,qs,ddd,cu) io =
    SEP_EXISTS df f dg g sp sa1 sa_len ds dd d.
      zBYTE_MEMORY dg g * zCODE_MEMORY ddd dd d * zMEMORY df f * ~zR 0x0w *
      ~zR 0x1w * ~zR 0x2w * ~zR 0x3w * ~zR 0x6w * zR 0x7w sp * zSTACK rbp qs *
      ~zR 0xBw * ~zR 0x9w * ~zR 0xDw * ~zR 0x8w * ~zR 0xCw * ~zR 0xAw *
      ~zR 0xEw * ~zR 0xFw * zIO (EL 0 cs,EL 1 cs,EL 2 cs,EL 0 ds) io *
       zCODE_UNCHANGED cu dd d *
        cond (lisp_init (a1,a2,sl,sl1,e,ex,cs) io (df,f,dg,g,dd,d,sp,sa1,sa_len,ds))`;

Definition zLISP_raw: zLISP = zLISP_ALT (\wsp wi we ds tw2. T)
End
val zLISP_def = SIMP_CONV std_ss [zLISP_ALT_def,zLISP_raw]
  ``zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)``
val _ = save_thm("zLISP_def",zLISP_def);

val SEP_IMP_zLISP_ALT_zLISP = prove(
  ``SEP_IMP (zLISP_ALT side vars1 vars2 * p) (zLISP vars1 vars2 * p)``,
  Q.SPEC_TAC (`vars1`,`vars1`) \\ Q.SPEC_TAC (`vars2`,`vars2`)
  \\ SIMP_TAC std_ss [FORALL_PROD] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC SEP_IMP_STAR \\ SIMP_TAC std_ss [SEP_IMP_REFL]
  \\ SIMP_TAC std_ss [zLISP_def,zLISP_ALT_def]
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR] \\ METIS_TAC []);

val STAT = zLISP_def |> SPEC_ALL |> concl |> dest_eq |> fst |> car |> cdr;

val zLISP_FAIL_def = Define `
  zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,dd,cu) =
    SEP_EXISTS ddd vars. zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) vars *
                         ~zS * zPC ex * cond ((dd = NONE) ==> (ddd = dd))`;

val _ = set_echo 0;
val (i,j) = (2,4)
val (spec,_,sts,_) = x64_tools

(* automation *)

fun dest_sep_exists tm = let
  val (x,y) = dest_comb tm
  val _ = if (fst o dest_const) x = "SEP_EXISTS" then () else fail()
  in dest_abs y end;

fun dest_sep_cond tm =
  if (fst o dest_const o fst o dest_comb) tm = "cond"
  then snd (dest_comb tm) else fail();

val prove_spec_blast = prove(
  ``((w2w (w1:word32) && 0x1w = 0x0w:word64) = (w1 && 0x1w = 0x0w)) /\
    ((w2w w1 = (w2w w2):word64) = (w1 = (w2:word32))) /\
    ((w2w w1 <+ (w2w w2):word64) = (w1 <+ (w2:word32))) /\
    (w2w ((w2w w1):word64) = w1) /\
    ((31 -- 0) (w2w w1 - 0x4w) = (w2w (w1 - 4w)):word64) /\
    ((w2w ((w2w w):word32)):word64 = (31 -- 0) w)``,
  blastLib.BBLAST_TAC);

val prove_spec_eval = LIST_CONJ [EVAL ``(w2w:word32->word64) 1w``,
                                 EVAL ``(w2w:word32->word64) 3w``,
                                 EVAL ``(w2w:word32->word64) 5w``,
                                 EVAL ``(w2w:word32->word64) 11w``];

fun AUTO_EXISTS_TAC (asm,tm) = let
      fun ex tm = let
        val (v,tm) = dest_exists tm
        in v :: ex tm end handle e => []
      val xs = ex tm
      val x = hd (list_dest dest_conj (repeat (snd o dest_exists) tm))
      val tm2 = hd (filter (can (match_term ``lisp_inv xx yy zz``)) asm)
      val (s,_) = match_term x tm2
      val ys = map (subst s) xs
      fun exx [] = ALL_TAC | exx (x::xs) = EXISTS_TAC x THEN exx xs
      in exx ys (asm,tm) end

fun prove_spec th imp def pre_tm post_tm = let
  val lemma = SIMP_CONV std_ss [SEP_HIDE_def] ``~zR x``
  val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [lemma])) th
  val th = SPEC_ALL (SIMP_RULE std_ss [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS] th)
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
  val s = map (fn (x,y) => x |-> y)
              (filter (fn x => is_var (fst x))
              (map (fn (x,y) => if is_comb x then (cdr x,cdr y handle HOL_ERR _ => y) else (x,y)) (map (rename fill3) res3)))
  val th = INST s th
  val th = UNDISCH_ALL (RW [SPEC_MOVE_COND] (SIMP_RULE (bool_ss++sep_cond_ss) [] th))
  val (m,p,_,q) = (dest_spec o concl o SPEC_ALL) th
  val fill = list_dest dest_star tm
  val res = list_dest dest_star p
  val fs = (filter (fn x => not (tmem x res)) fill)
  val fs = if can (find_term (aconv ``zCODE_MEMORY``)) (concl th) then
              filter (fn tm => repeat car tm !~ ``zCODE_MEMORY``) fs else fs
  val f = list_mk_star fs (type_of (hd fill))
  val th = SPEC f (MATCH_MP SPEC_FRAME th)
  val pre = (fst o dest_imp o snd o dest_imp) (concl imp) handle e => ``T:bool``
  val (_,p,_,_) = dest_spec (concl (PURE_REWRITE_RULE [GSYM SPEC_MOVE_COND] (DISCH pre th)))
  val x = (snd o dest_star) p
  val tmi = (fst o dest_eq o concl o SPEC_ALL) def
  val tmj = hd (list_dest dest_star pre_tm)
  val th = INST (fst (match_term tmi tmj)) th
  val th = SPEC x (MATCH_MP SPEC_FRAME th)
  val th = SPEC post_tm (MATCH_MP SPEC_WEAKEN th)
  val goal = (cdr o car o concl) th
  val lemma = prove(goal,
(*
    set_goal([],goal)
*)
    REWRITE_TAC [STAR_ASSOC,prove_spec_blast]
    \\ SIMP_TAC (std_ss++sep_cond_ss) []
    \\ REWRITE_TAC [SEP_IMP_MOVE_COND]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC (SIMP_RULE std_ss [] imp)
    \\ REPEAT (Q.PAT_X_ASSUM `xx ==> yy` (K ALL_TAC))
    \\ ASM_SIMP_TAC std_ss [LET_DEF,prove_spec_blast]
    \\ SIMP_TAC std_ss [def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REPEAT (Q.PAT_X_ASSUM `!xxx.bbb` (ASSUME_TAC o SPEC_ALL))
    \\ AUTO_EXISTS_TAC
    \\ FULL_SIMP_TAC std_ss [prove_spec_eval,prove_spec_blast,EL_UPDATE_NTH]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_n2w,bitTheory.BITS_THM]
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
(*
    set_goal([],goal)
*)
    SIMP_TAC std_ss [def,SEP_CLAUSES]
    \\ SIMP_TAC (bool_ss++sep_cond_ss) []
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR]
    \\ REPEAT STRIP_TAC
    \\ AUTO_EXISTS_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC (SIMP_RULE std_ss [] imp)
    \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT (Q.PAT_X_ASSUM `xx ==> yy` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ METIS_TAC [])
  val th = MATCH_MP th lemma
  val th = RW [SEP_CLAUSES] th
  in th end;

fun set_pc th = let
  val (_,_,_,q) = (dest_spec o concl o UNDISCH_ALL) th
  val tm = find_term (fn x => tmem (car x) [``zPC``,``xPC``,``aPC``,``pPC``]
                              handle e => false) q
  in subst [``p:word64``|->cdr tm,``rip:word64``|->cdr tm] end

fun swap_thm 0 = lisp_inv_swap0
  | swap_thm 1 = lisp_inv_swap1
  | swap_thm 2 = lisp_inv_swap2
  | swap_thm 3 = lisp_inv_swap3
  | swap_thm 4 = lisp_inv_swap4
  | swap_thm 5 = lisp_inv_swap5
  | swap_thm _ = fail()

fun x64_reg n = "r" ^ (int_to_string (n+8))

fun generate_swap i j =
  if i = 0 then swap_thm j else
  if j = 0 then swap_thm i else
  if i = j then swap_thm 1 else
  DISCH_ALL (MATCH_MP (swap_thm i) (MATCH_MP (swap_thm j) (UNDISCH (swap_thm i))));
  (* e.g. to swap 4 and 5 do generate_swap 4 5 *)

fun generate_copy i j =
  if i = j then generate_swap 0 0 else
  if j = 1 then let
    val sw0 = generate_swap 0 i
    val sw1 = generate_swap 0 1
    val th = MATCH_MP lisp_inv_copy (MATCH_MP sw1 (UNDISCH sw0))
    in DISCH_ALL (MATCH_MP sw0 th) end
  else if i = 1 then let
    val sw0 = generate_swap 0 j
    val th = MATCH_MP lisp_inv_copy (UNDISCH sw0)
    in DISCH_ALL (MATCH_MP sw0 th) end
  else let
    val sw0 = generate_swap 1 i
    val sw1 = generate_swap 0 j
    val th = MATCH_MP lisp_inv_copy (MATCH_MP sw1 (UNDISCH sw0))
    in DISCH_ALL (MATCH_MP sw0 (MATCH_MP sw1 th)) end;
  (* e.g. to copy 5 into 3 do generate_copy 3 5 *)

val all_regs = [0,1,2,3,4,5];

val all_reg_pairs = let
  fun pairs x [] = [] | pairs x (y::ys) = (x,y) :: pairs x ys
  fun cross [] ys = [] | cross (x::xs) ys = pairs x ys @ cross xs ys
  in cross [0,1,2,3,4,5] [0,1,2,3,4,5] end;

val all_distinct_reg_pairs = filter (fn (x,y) => not (x = y)) all_reg_pairs;

fun save_lisp_thm (name,th) = let
  val th = Q.INST [`rip`|->`p`] th
  val _ = add_compiled [th]
  in save_thm(name,th) end;


(* stack operations *)

val X64_LISP_CALL_R2 = save_thm("X64_LISP_CALL_R2", let
  val th = zSTACK_PROPS |> SPEC_ALL |> CONJUNCTS |> el 1
  val imp = lisp_inv_stack |> Q.SPECL [`p+3w::qs`,`tw2`]
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. tw2 = r2) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,p+3w::qs,code,amnt,ok) * zPC r2``
  val res = prove_spec th imp def pre_tm post_tm
  val res = RW [GSYM zLISP_raw] res
  in res end);

val X64_LISP_PUSH_R2 = save_thm("X64_LISP_PUSH_R2", let
  val th = zSTACK_PROPS |> SPEC_ALL |> CONJUNCTS |> el 2
  val imp = lisp_inv_stack |> Q.SPECL [`r2::qs`,`tw2`]
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. tw2 = r2) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,r2::qs,code,amnt,ok) * zPC (p+2w)``
  val res = prove_spec th imp def pre_tm post_tm
  val res = RW [GSYM zLISP_raw] res
  in res end);

val X64_LISP_RET = save_thm("X64_LISP_RET", let
  val th = zSTACK_PROPS |> SPEC_ALL |> CONJUNCTS |> el 3
  val imp = lisp_inv_stack |> Q.SPECL [`TL qs`,`tw2`] |> UNDISCH |> DISCH ``~(qs:word64 list = [])`` |> DISCH_ALL
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,TL qs,code,amnt,ok) * zPC (HD qs)``
  val res = prove_spec th imp def pre_tm post_tm
  val res = res |> Q.INST [`qs`|->`q::qs`] |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES]
  in res end);

val X64_LISP_ALT_RET = save_thm("X64_LISP_ALT_RET", let
  val th = zSTACK_PROPS |> SPEC_ALL |> CONJUNCTS |> el 3
  val th = SPEC_FRAME_RULE th ``~zS``
  val imp = lisp_inv_stack |> Q.SPECL [`TL qs`,`tw2`] |> UNDISCH |> DISCH ``~(qs:word64 list = [])`` |> DISCH_ALL
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT b ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = ``zLISP_ALT b ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,TL qs,code,amnt,ok) * zPC (HD qs) * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  val res = res |> Q.INST [`qs`|->`q::qs`] |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES]
  in res end);

val X64_LISP_POP_R2 = save_thm("X64_LISP_POP_R2", let
  val th = zSTACK_PROPS |> SPEC_ALL |> CONJUNCTS |> el 4
  val imp = lisp_inv_stack |> Q.SPECL [`TL qs`,`HD qs`] |> UNDISCH |> DISCH ``~(qs:word64 list = [])`` |> DISCH_ALL
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. tw2 = HD qs) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,TL qs,code,amnt,ok) * zPC (p+2w)``
  val res = prove_spec th imp def pre_tm post_tm
  val res = res |> Q.INST [`qs`|->`q::qs`] |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES]
  val res = RW [GSYM zLISP_raw] res
  in res end);

val X64_LISP_CALL_IMM = save_thm("X64_LISP_CALL_IMM", let
  val th = zSTACK_PROPS |> SPEC_ALL |> CONJUNCTS |> el 5
  val imp = lisp_inv_stack |> Q.SPECL [`p+6w::qs`,`tw2`]
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,p+6w::qs,code,amnt,ok) * zPC (p + n2w (6 + SIGN_EXTEND 32 64 (w2n (imm32:word32))))``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);


(* move *)

fun X64_LISP_MOVE (i,j) = let
  val _ = print "z"
  val s = "mov " ^ x64_reg i ^ ", " ^ x64_reg j
  val s = x64_encode s
  val (spec,_,_,_) = x64_tools
  val ((th,_,_),_) = spec s
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)``
  val (_,pre,_,post) = dest_spec (concl th)
  val pre_tm = mk_star(pre_tm,find_term (can (match_term ``zPC x``)) pre)
  val post_tm = mk_star(post_tm,find_term (can (match_term ``zPC x``)) post)
  val s = [[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> [QUOTE ("x" ^ int_to_string j)]]
  val sw = [[QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> [QUOTE ("w" ^ int_to_string j)]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val tm = ``lisp_inv ^STATINV (x0,x1,x2,x3,x4,x5,^VAR_REST)
               (w0,w1,w2,w3,w4,w5,df,f,^REST)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val imp = generate_copy i j
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_MOVE" ^ int_to_string i ^ int_to_string j,result) end

val _ = map X64_LISP_MOVE all_distinct_reg_pairs;


(* car *)

fun generate_car i = let
  val th = CONJUNCT1 (UNDISCH (UNDISCH lisp_inv_car))
  val th = DISCH_ALL (MATCH_MP (swap_thm i) th)
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  val th1 = CONJUNCT2 (UNDISCH (UNDISCH lisp_inv_car))
  val th1 = DISCH_ALL (MATCH_MP (DISCH_ALL th1) (UNDISCH (swap_thm i)))
  val th2 = UNDISCH (RW [AND_IMP_INTRO] th)
  val th3 = UNDISCH (RW [AND_IMP_INTRO] th1)
  in RW [GSYM AND_IMP_INTRO] (DISCH_ALL (CONJ th2 th3)) end;

val car_blast = prove(
  ``!w:word32 v u:word64.
       ((31 -- 0) (w2w w) = (w2w w):word64) /\
       (4w * v + u = u + 4w * v)``,
  blastLib.BBLAST_TAC);

fun X64_LISP_CAR (i,j) = let
  val _ = print "z"
  val s = "mov " ^ x64_reg i ^ "d, [r6+4*" ^ x64_reg j ^ "]"
  val s = x64_encode s
  val (spec,_,_,_) = x64_tools
  val ((th,_,_),_) = spec s
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)``
  val (_,pre,_,post) = dest_spec (concl th)
  val pre_tm = mk_star(pre_tm,find_term (can (match_term ``zPC x``)) pre)
  val post_tm = mk_star(post_tm,find_term (can (match_term ``zPC x``)) post)
  val s = [[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> [QUOTE ("CAR x" ^ int_to_string j)]]
  val sw = [[QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> [QUOTE ("(f:word64->word32) (bp + 0x4w * w2w w" ^ int_to_string j ^ ")")]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val tm = ``lisp_inv ^STATINV (x0,x1,x2,x3,x4,x5,^VAR_REST)
               (w0,w1,w2,w3,w4,w5,df,f,^REST)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val imp = generate_copy i j
  val imp = DISCH_ALL (MATCH_MP (generate_car i) (UNDISCH imp))
  val th = RW [car_blast] th
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_CAR" ^ int_to_string i ^ int_to_string j,result) end

val _ = map X64_LISP_CAR all_reg_pairs;


(* cdr *)

fun generate_cdr i = let
  val th = CONJUNCT1 (UNDISCH (UNDISCH lisp_inv_cdr))
  val th = DISCH_ALL (MATCH_MP (swap_thm i) th)
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  val th1 = CONJUNCT2 (UNDISCH (UNDISCH lisp_inv_cdr))
  val th1 = DISCH_ALL (MATCH_MP (DISCH_ALL th1) (UNDISCH (swap_thm i)))
  val th2 = UNDISCH (RW [AND_IMP_INTRO] th)
  val th3 = UNDISCH (RW [AND_IMP_INTRO] th1)
  in RW [GSYM AND_IMP_INTRO] (DISCH_ALL (CONJ th2 th3)) end;

val cdr_blast = prove(
  ``!w:word32 v u:word64.
       ((31 -- 0) (w2w w) = (w2w w):word64) /\
       (4w * v + u + 4w = u + 4w * v + 4w)``,
  blastLib.BBLAST_TAC);

fun X64_LISP_CDR (i,j) = let
  val _ = print "z"
  val s = "mov " ^ x64_reg i ^ "d, [r6+4*" ^ x64_reg j ^ "+4]"
  val s = x64_encode s
  val (spec,_,_,_) = x64_tools
  val ((th,_,_),_) = spec s
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)``
  val (_,pre,_,post) = dest_spec (concl th)
  val pre_tm = mk_star(pre_tm,find_term (can (match_term ``zPC x``)) pre)
  val post_tm = mk_star(post_tm,find_term (can (match_term ``zPC x``)) post)
  val s = [[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> [QUOTE ("CDR x" ^ int_to_string j)]]
  val sw = [[QUOTE ("w" ^ int_to_string i ^ ":word32")] |-> [QUOTE ("(f:word64->word32) (bp + 0x4w * w2w w" ^ int_to_string j ^ "+4w)")]]
  val post_tm = cdr (concl (Q.INST s (REFL post_tm)))
  val tm = ``lisp_inv ^STATINV (x0,x1,x2,x3,x4,x5,^VAR_REST)
               (w0,w1,w2,w3,w4,w5,df,f,^REST)``
  val tm2 = cdr (concl (Q.INST s (Q.INST sw (REFL tm))))
  val imp = generate_copy i j
  val imp = DISCH_ALL (MATCH_MP (generate_cdr i) (UNDISCH imp))
  val th = RW [cdr_blast] th
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_CDR" ^ int_to_string i ^ int_to_string j,result) end

val _ = map X64_LISP_CDR all_reg_pairs;


(* isDot *)

fun X64_LISP_ISDOT i = let
  val _ = print "z"
  val s = "test " ^ (x64_reg i) ^ ", 1"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val def = zLISP_def
  val imp = DISCH_ALL (MATCH_MP lisp_inv_type (UNDISCH (swap_thm i)))
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME (isDot x)) * ~zS1 Z_PF * ~zS1 Z_SF * ~zS1 Z_AF * ~zS1 Z_OF * ~zS1 Z_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_ISDOT" ^ int_to_string i,result) end;

val _ = map X64_LISP_ISDOT all_regs;


(* isSym *)

fun generate_sym i = let
  val th = CONJUNCT2 (UNDISCH lisp_inv_isSym)
  val th = DISCH_ALL (MATCH_MP (swap_thm i) th)
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  val th1 = CONJUNCT1 (UNDISCH lisp_inv_isSym)
  val th1 = DISCH_ALL (MATCH_MP (DISCH_ALL th1) (UNDISCH (swap_thm i)))
  val th2 = UNDISCH (RW [AND_IMP_INTRO] th)
  val th3 = UNDISCH (RW [AND_IMP_INTRO] th1)
  in RW [GSYM AND_IMP_INTRO] (DISCH_ALL (CONJ th2 th3)) end;

fun X64_LISP_ISSYM i = let
  val _ = print "z"
  val s = "mov r2, " ^ (x64_reg i)
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (x64_encode ("mov r2, " ^ (x64_reg i)))
  val ((th2,_,_),_) = spec (x64_encode ("and r2, r0"))
  val ((th3,_,_),_) = spec (x64_encode ("cmp r0, r2"))
  val th = SPEC_COMPOSE_RULE [th1,th2,th3]
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val th = GSYM th
  val def = zLISP_def
  val imp = generate_sym i
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME (isSym x)) * ~zS1 Z_PF * ~zS1 Z_SF * ~zS1 Z_AF * ~zS1 Z_OF * ~zS1 Z_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_ISSYM" ^ int_to_string i,result) end;

val _ = map X64_LISP_ISSYM all_regs;


(* isVal *)

fun generate_val i = let
  val th = CONJUNCT2 (UNDISCH lisp_inv_isVal)
  val th = DISCH_ALL (MATCH_MP (swap_thm i) th)
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  val th1 = CONJUNCT1 (UNDISCH lisp_inv_isVal)
  val th1 = DISCH_ALL (MATCH_MP (DISCH_ALL th1) (UNDISCH (swap_thm i)))
  val th2 = UNDISCH (RW [AND_IMP_INTRO] th)
  val th3 = UNDISCH (RW [AND_IMP_INTRO] th1)
  in RW [GSYM AND_IMP_INTRO] (DISCH_ALL (CONJ th2 th3)) end;

fun X64_LISP_ISVAL i = let
  val _ = print "z"
  val s = "mov r2, " ^ (x64_reg i)
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (x64_encode ("mov r2, " ^ (x64_reg i)))
  val ((th2,_,_),_) = spec (x64_encode ("and r2, r0"))
  val ((th3,_,_),_) = spec (x64_encode ("cmp r1, r2"))
  val th = SPEC_COMPOSE_RULE [th1,th2,th3]
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val th = GSYM th
  val def = zLISP_def
  val imp = generate_val i
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME (isVal x)) * ~zS1 Z_PF * ~zS1 Z_SF * ~zS1 Z_AF * ~zS1 Z_OF * ~zS1 Z_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_ISVAL" ^ int_to_string i,result) end;

val _ = map X64_LISP_ISVAL all_regs;


(* eq zero *)

fun X64_LISP_EQZERO i = let
  val _ = print "z"
  val s = "cmp r1, " ^ (x64_reg i)
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val def = zLISP_def
  val imp = UNDISCH lisp_inv_eq_zero
  val imp = DISCH_ALL (MATCH_MP (DISCH_ALL imp) (UNDISCH (swap_thm i)))
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME (x = Val 0)) * ~zS1 Z_PF * ~zS1 Z_SF * ~zS1 Z_AF * ~zS1 Z_OF * ~zS1 Z_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_EQZERO" ^ int_to_string i,result) end;

val _ = map X64_LISP_EQZERO all_regs;


(* eq val *)

val lisp_inv_eq_val = prove(
  ``!n. n < 1073741824 /\ ^LISP ==> ((w2w w0 = n2w (4 * n + 1):word64) = (x0 = Val n))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC lisp_inv_swap1
  \\ IMP_RES_TAC lisp_inv_Val_n2w
  \\ IMP_RES_TAC (RW [isDot_def] (Q.INST [`x0`|->`Val n`] lisp_inv_eq))
  \\ CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
  \\ Cases_on `w0` \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,w2w_def,w2n_n2w]
  \\ `(4 * n + 1) < 4294967296` by DECIDE_TAC
  \\ `(4 * n + 1) < 18446744073709551616` by DECIDE_TAC
  \\ `n' < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []);

fun X64_LISP_EQ_VAL n i = let
  val _ = print "z"
  val s = "cmp " ^ (x64_reg i) ^ ", " ^ int_to_string (4 * n + 1)
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val def = zLISP_def
  val imp = UNDISCH (SIMP_RULE std_ss [] (SPEC (numSyntax.term_of_int n) lisp_inv_eq_val))
  val imp = DISCH_ALL (MATCH_MP (DISCH_ALL imp) (UNDISCH (swap_thm i)))
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME (x = Val n)) * ~zS1 Z_PF * ~zS1 Z_SF * ~zS1 Z_AF * ~zS1 Z_OF * ~zS1 Z_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")],``n:num``|->numSyntax.term_of_int n] post_tm
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_EQ_VAL_" ^ int_to_string n ^ "_" ^ int_to_string i,result) end;

val X64_LISP_EQ_VAL = fn n => fn i => allowing_rebinds (X64_LISP_EQ_VAL n) i

val _ = map (X64_LISP_EQ_VAL 1) all_regs;
val _ = map (X64_LISP_EQ_VAL 2) all_regs;
val _ = map (X64_LISP_EQ_VAL 3) all_regs;
(* does 3 0 a second time *)
val _ = map (fn n => X64_LISP_EQ_VAL n 0) [3,4,5,6,7,8,9,10,11,12,13,14,15];

(* eq *)

fun X64_LISP_EQ (i,j) = if j <= i then (TRUTH,TRUTH) else let
  val _ = print "z"
  val s = "cmp " ^ (x64_reg i) ^ ", " ^ (x64_reg j)
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val def = zLISP_def
  val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM markerTheory.Abbrev_def])) lisp_inv_eq
  val lemma = RW [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] lemma))
  val lemma = if j = 1 then lemma else DISCH_ALL (MATCH_MP lemma (UNDISCH (generate_swap 1 j)))
  val lemma = if i = 0 then lemma else DISCH_ALL (MATCH_MP lemma (UNDISCH (generate_swap 0 i)))
  val imp = lemma
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME (x = y:SExp)) * ~zS1 Z_PF * ~zS1 Z_SF * ~zS1 Z_AF * ~zS1 Z_OF * ~zS1 Z_CF``
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]] post_tm
  val post_tm = subst [``y:SExp``|->Term [QUOTE ("x" ^ int_to_string j ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  val result2 = RW1 [EQ_SYM_EQ,DISJ_COMM] result
  val _ = save_lisp_thm("X64_LISP_EQ" ^ int_to_string i ^ int_to_string j,result)
  val _ = save_lisp_thm("X64_LISP_EQ" ^ int_to_string j ^ int_to_string i,result2)
  in (result,result2) end;

val _ = map X64_LISP_EQ all_reg_pairs;


(* less *)

val X64_LISP_LESS = let
  val _ = print "z"
  val s = "cmp " ^ (x64_reg 0) ^ ", " ^ (x64_reg 1)
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_ZF`` th
  val def = zLISP_def
  val lemma = METIS_PROVE [] ``(b==>c==>d) = (c==>b==>d)``
  val imp = RW1 [lemma] lisp_inv_less
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_CF (SOME (getVal x0 < getVal x1)) * ~zS1 Z_PF * ~zS1 Z_SF * ~zS1 Z_AF * ~zS1 Z_OF * ~zS1 Z_ZF``
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_LESS",result) end;

val X64_LISP_EVEN = let
  val _ = print "z"
  val s = "test r8, 4"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val th = Q.INST [`r8`|->`w2w (a:word32)`,`rip`|->`p`] th
  val def = zLISP_def
  val lemma = METIS_PROVE [] ``(b==>c==>d) = (c==>b==>d)``
  val imp = RW1 [lemma] lisp_inv_even
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_ZF (SOME (EVEN (getVal x0))) * ~zS1 Z_PF * ~zS1 Z_SF * ~zS1 Z_AF * ~zS1 Z_OF * ~zS1 Z_CF``
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_EVEN",result) end;


(* assign 0 and 1 to all regs *)

val SIGN_EXTEND_MOD = store_thm("SIGN_EXTEND_MOD",
  ``SIGN_EXTEND 32 64 (w2n imm32) MOD 4294967296 = w2n (imm32:word32)``,
  SIMP_TAC std_ss [SIGN_EXTEND_def,LET_DEF] \\ SRW_TAC [] []
  \\ (SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:32``] w2n_lt)
       |> Q.SPEC `imm32` |> ASSUME_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ REWRITE_TAC [GSYM (EVAL ``4294967295 * 4294967296``)]
  \\ IMP_RES_TAC MOD_MULT \\ FULL_SIMP_TAC std_ss []);

val imm32_lemma = prove(
  ``n < 2**30 ==>
    (SIGN_EXTEND 32 64 (w2n (n2w (4 * n + 1):word32)) MOD 4294967296 = 4 * n + 1)``,
  SIMP_TAC std_ss [SIGN_EXTEND_MOD]
  \\ SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w] \\ DECIDE_TAC);

val bound_lemma = prove(
  ``n < 1073741824 ==> 4 * n + 1 < 4294967296``,
  DECIDE_TAC);

val X64_LISP_ASSIGN_ANY_VAL = save_thm("X64_LISP_ASSIGN_ANY_VAL",let
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec "41B8"
  val def = zLISP_def
  val th = Q.INST [`imm32`|->`n2w (4 * n + 1)`,`rip`|->`p`] th
           |> DISCH ``n < 2**30`` |> SIMP_RULE bool_ss [imm32_lemma]
           |> RW [GSYM SPEC_MOVE_COND] |> SIMP_RULE std_ss []
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP ^STAT (Val n,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val imp = lisp_inv_Val_n2w |> SPEC_ALL |> RW1 [GSYM AND_IMP_INTRO]
            |> UNDISCH_ALL
            |> (fn th => CONJ th (UNDISCH bound_lemma))
            |> DISCH_ALL
  val result = prove_spec th imp def pre_tm post_tm
  in result end);

fun generate_assign_val n i = let
  val th1 = SIMP_RULE std_ss [] (SPEC n lisp_inv_Val_n2w);
  val th5 = UNDISCH th1
  val th5 = DISCH_ALL (MATCH_MP (swap_thm i) th5)
  val th5 = DISCH_ALL (MATCH_MP th5 (UNDISCH (swap_thm i)))
  in th5 end;

fun X64_LISP_ASSIGN_VAL n i = let
  val _ = print "z"
  val s = "mov " ^ (x64_reg i) ^ "d, " ^ int_to_string (4 * n + 1)
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val def = zLISP_def
  val n_tm = numSyntax.term_of_int n
  val imp = generate_assign_val n_tm i
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->mk_comb(``Val ``,n_tm)] post_tm
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_ASSIGN_" ^ int_to_string n ^ "_" ^ int_to_string i,result) end;

val _ = map (X64_LISP_ASSIGN_VAL 0) all_regs;
val _ = map (X64_LISP_ASSIGN_VAL 1) all_regs;
val _ = map (fn n => X64_LISP_ASSIGN_VAL n 0) [2,3,4,5,6,7,8,9,10,11,12,13,14,15];
val _ = map (fn n => X64_LISP_ASSIGN_VAL n 1) [2,3,4,5,6,7,8,9,10,11,12,13,14,15];


(* assign/test sym *)

val lisp_inv_sym_assigns = map (DISCH_ALL o CONJUNCT1 o UNDISCH) (CONJUNCTS lisp_inv_Sym);
val lisp_inv_sym_tests = map (DISCH_ALL o CONJUNCT2 o UNDISCH) (CONJUNCTS lisp_inv_Sym);

fun generate_assign_sym n i = let
  val th = UNDISCH (el (n+1) lisp_inv_sym_assigns)
  val th = DISCH_ALL (MATCH_MP (swap_thm i) th)
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  in th end;

fun generate_test_sym n i = let
  val th = el (n+1) lisp_inv_sym_tests
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  in th end;

fun X64_LISP_ASSIGN_SYM n i = let
  val _ = print "z"
  val imp = generate_assign_sym n i
  val k = cdr (find_term wordsSyntax.is_n2w (concl imp))
  val k = numSyntax.int_of_term k
  val s = "mov " ^ (x64_reg i) ^ "d, " ^ (int_to_string k)
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val sym = find_term (can (match_term ``Sym s``)) (concl imp)
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->sym] post_tm
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_ASSIGN_SYM_" ^ int_to_string n ^ "_" ^ int_to_string i,result) end;

fun X64_LISP_TEST_SYM n i = let
  val _ = print "z"
  val imp = generate_test_sym n i
  val k = cdr (find_term wordsSyntax.is_n2w (concl imp))
  val k = numSyntax.int_of_term k
  val s = "cmp " ^ (x64_reg i) ^ ", " ^ (int_to_string k)
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_PRE_STATUS_RULE sts th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME (x = res:SExp)) * ~zS1 Z_PF * ~zS1 Z_SF * ~zS1 Z_AF * ~zS1 Z_OF * ~zS1 Z_CF``
  val sym = find_term (can (match_term ``Sym s``)) (concl imp)
  val post_tm = subst [``x:SExp``|->Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")],``res:SExp``|->sym] post_tm
  val tm = find_term (can (match_term ``zPC (eip + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_TEST_SYM_" ^ int_to_string n ^ "_" ^ int_to_string i,result) end;

fun X64_LISP_SYM n i = (X64_LISP_ASSIGN_SYM n i, X64_LISP_TEST_SYM n i);

fun ilist i [] = [] | ilist i (x::xs) = i::ilist (i+1) xs;
val all_syms = ilist 0 lisp_inv_sym_tests;

val _ = map (X64_LISP_SYM 0) all_regs; (* NIL *)
val _ = map (X64_LISP_SYM 1) all_regs; (* T *)
val _ = map (X64_LISP_SYM 2) all_regs; (* QUOTE *)
val _ = map (fn x => allowing_rebinds (X64_LISP_SYM x) 0) all_syms;


(* error *)

val X64_LISP_ERROR = save_thm("X64_LISP_ERROR",let
  val s = "jmp [r7-200]"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC ex``
  val imp = lisp_inv_error
  val def = zLISP_def
  val res = prove_spec th imp def pre_tm post_tm
  val res = SPEC_FRAME_RULE res ``~zS``
  val post_tm = ``zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)``
  val th = SPEC post_tm (MATCH_MP SPEC_WEAKEN res)
  val goal = (cdr o car o concl) th
  val lemma = prove(goal,
    SIMP_TAC std_ss [zLISP_FAIL_def,SEP_EXISTS_THM,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `ddd`
    \\ Q.EXISTS_TAC `(x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES])
  val th = MP th lemma
  in th end);

val X64_LISP_SET_OK_F = save_lisp_thm("X64_LISP_SET_OK_F",let
  val th = X64_LISP_ERROR
  val (th,goal) = SPEC_WEAKEN_RULE th
     ``zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)
             (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,F) * zPC (rip+7w) * ~zS \/
       zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)``
  val lemma = prove(goal,SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def])
  val th = MP th lemma
  in th end);


(* is_quote *)

val X64_LISP_IS_QUOTE = save_lisp_thm("X64_LISP_IS_QUOTE",let
  val th = mc_is_quote_full_spec
  val imp = mc_is_quote_full_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (LISP_TEST (isQuote x0),x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);


(* gc *)

val X64_LISP_GC = save_lisp_thm("X64_LISP_GC",let
  val th = lisp_consTheory.mc_full_thm
  val imp = SIMP_RULE std_ss [LET_DEF] lisp_inv_gc
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);


(* calls to code pointers *)

val align_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a - w && 3w = 0w) = (w && 3w = 0w:word64))``

val imp4 = prove(
  ``^LISP ==> (sp - 0x6Cw && 0x3w = 0x0w) /\ (sp - 0x70w && 0x3w = 0x0w) /\
              (sp - 0x74w && 0x3w = 0x0w) /\ (sp - 0x78w && 0x3w = 0x0w) /\
              (sp - 0x7Cw && 0x3w = 0x0w) /\ (sp - 0x80w && 0x3w = 0x0w) /\
              (sp - 0x84w && 0x3w = 0x0w) /\ (sp - 0x88w && 0x3w = 0x0w) /\
              (sp - 0x8Cw && 0x3w = 0x0w) /\ (sp - 0x90w && 0x3w = 0x0w) /\
              (sp - 0x98w && 0x3w = 0x0w) /\ (sp - 0x94w && 0x3w = 0x0w) /\
              (sp - 0x9Cw && 0x3w = 0x0w) /\ (sp - 0xA0w && 0x3w = 0x0w) /\
              (sp - 0xC8w && 0x3w = 0x0w) /\ (sp - 0xA4w && 0x3w = 0x0w) /\
              (sp - 0xC4w && 0x3w = 0x0w) /\ (sp - 0xA8w && 0x3w = 0x0w) /\
              (sp - 0xC0w && 0x3w = 0x0w) /\ (sp - 0xACw && 0x3w = 0x0w) /\
              (sp - 0xBCw && 0x3w = 0x0w) /\ (sp - 0xB0w && 0x3w = 0x0w) /\
              (sp - 0xB8w && 0x3w = 0x0w) /\ (sp - 0xB4w && 0x3w = 0x0w)``,
  SIMP_TAC std_ss [lisp_inv_def] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3]) |> UNDISCH

fun X64_LISP_CALL_EL i = save_thm("X64_LISP_CALL_EL" ^ (int_to_string i),let
  val addr = "mov r2,[r7-" ^ int_to_string (192 - 8 * i) ^ "]"
  val ((th,_,_),_) = x64_spec (x64_encodeLib.x64_encode addr)
  val th = Q.INST [`rip`|->`p`] th
  val th = RW [INSERT_SUBSET,EMPTY_SUBSET] th
  val tm = subst [``i:num``|->numSyntax.term_of_int i] ``(EL i cs):word64``
  val imp0 = UNDISCH (INST [``temp:word64``|->tm] lisp_inv_ignore_tw2)
  val imp1 = el (3*i+10+3) (CONJUNCTS (UNDISCH lisp_inv_cs_read))
  val imp2 = el (3*i+11+3) (CONJUNCTS (UNDISCH lisp_inv_cs_read))
  val imp3 = el (3*i+12+3) (CONJUNCTS (UNDISCH lisp_inv_cs_read))
  val imp = DISCH_ALL (LIST_CONJ [imp0,imp1,imp2,imp3,imp4])
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. tw2 = ^tm) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val res = prove_spec th imp def pre_tm post_tm
  val res = SPEC_COMPOSE_RULE [res,Q.INST [`r2`|->`^tm`] X64_LISP_CALL_R2]
  val res = RW [GSYM zLISP_raw] res
  in res end);

val X64_LISP_CALL_EL3 = X64_LISP_CALL_EL 3;
val X64_LISP_CALL_EL5 = X64_LISP_CALL_EL 5;
val X64_LISP_CALL_EL6 = X64_LISP_CALL_EL 6;
val X64_LISP_CALL_EL7 = X64_LISP_CALL_EL 7;
val X64_LISP_CALL_EL8 = X64_LISP_CALL_EL 8;
val X64_LISP_CALL_EL9 = X64_LISP_CALL_EL 9;


(* store r2 into cs *)

val write_cs_blast = blastLib.BBLAST_PROVE
  ``(w2w ((w2w (w >>> 32)):word32) << 32 !! w2w ((w2w (w:word64)):word32) = w) /\
    ((63 >< 32) w = (w2w (w >>> 32)):word32) /\ ((31 >< 0) w = (w2w w):word32)``;

fun X64_LISP_WRITE_CS i = save_thm("X64_LISP_WRITE_CS" ^ (int_to_string i),let
  val addr = "mov [r7-" ^ int_to_string (192 - 8 * i) ^ "],r2"
  val ((th,_,_),_) = x64_spec (x64_encodeLib.x64_encode addr)
  val th = Q.INST [`rip`|->`p`] th
  val th = RW [INSERT_SUBSET,EMPTY_SUBSET] th
  val tm = subst [``i:num``|->numSyntax.term_of_int i] ``(UPDATE_NTH i r2 cs):word64 list``
  val imp1 = if i = 3 then last (CONJUNCTS (UNDISCH (Q.INST [`w`|->`tw2`] lisp_inv_cs_write)))
             else el (10-i) (CONJUNCTS (UNDISCH (Q.INST [`w`|->`tw2`] lisp_inv_cs_write)))
  val imp2 = el (3*i+11+3) (CONJUNCTS (UNDISCH lisp_inv_cs_read))
  val imp3 = el (3*i+12+3) (CONJUNCTS (UNDISCH lisp_inv_cs_read))
  val imp = DISCH_ALL (LIST_CONJ [imp1,imp2,imp3,imp4])
  val NEW_STAT = subst [mk_var("cs",``:word64 list``) |-> tm] STAT
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. tw2 = r2) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. T) ^NEW_STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val th = RW [write_cs_blast] th
  val finder = find_term (fn tm => is_comb tm andalso combinSyntax.is_update (car tm))
  val tm1 = finder (concl (Q.INST [`r7`|->`sp`,`r2`|->`tw2`] th))
  val tm2 = finder (concl imp)
  val goal = mk_eq(tm1,tm2)
  val lemma = prove(goal,MATCH_MP_TAC UPDATE_COMMUTES \\ blastLib.BBLAST_TAC)
  val th = RW1 [lemma] th
  val res = prove_spec th imp def pre_tm post_tm
  val res = SPEC_COMPOSE_RULE [X64_LISP_POP_R2,(Q.INST [`r2`|->`q`] res)]
  val res = RW [GSYM zLISP_raw] res
  in res end);

val X64_LISP_WRITE_CS3 = X64_LISP_WRITE_CS 3;
val X64_LISP_WRITE_CS5 = X64_LISP_WRITE_CS 5;
val X64_LISP_WRITE_CS6 = X64_LISP_WRITE_CS 6;
val X64_LISP_WRITE_CS7 = X64_LISP_WRITE_CS 7;
val X64_LISP_WRITE_CS8 = X64_LISP_WRITE_CS 8;
val X64_LISP_WRITE_CS9 = X64_LISP_WRITE_CS 9;


(* equal *)

val X64_LISP_EQUAL = save_lisp_thm("X64_LISP_EQUAL",let
  val th = mc_full_equal_spec
  val imp = mc_full_equal_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (LISP_TEST (x0 = x1:SExp),Sym "NIL",x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  val res = Q.INST [`qs`|->`q::qs`] res
  val res = SPEC_COMPOSE_RULE [res,X64_LISP_RET]
  val (_,_,c,_) = dest_spec (concl res)
  val name = mk_var("abbrev_code_for_equal",mk_type("fun",[``:word64``,type_of c]))
  val def = Define [ANTIQUOTE (mk_eq(mk_comb(name,``p:word64``),c))]
  val res = RW [GSYM def] res
  val res = SPEC_COMPOSE_RULE [fetch "-" "X64_LISP_CALL_EL6",res]
  in res end);


(* add, add1 *)

val select_twice = blastLib.BBLAST_PROVE
  ``((31 -- 0) ((31 -- 0) w) = (31 -- 0) w:word64) /\
    ((31 -- 0) (w2w a - 0x1w:word64) = w2w ((a:word32) - 1w)) /\
    ((31 -- 0) (w2w a) = (w2w a):word64) /\
    ((31 -- 0) (w2w a + w2w b) = (w2w (a + b)):word64) /\
    ((31 -- 0) (w2w a + 4w) = (w2w (a + 4w)):word64)``;

val SEP_IMP_LEMMA = prove(
  ``SEP_IMP p (p \/ q) /\ SEP_IMP p (q \/ p)``,
  SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]);

val SPEC_MERGE_LEMMA = prove(
  ``SPEC m (p * cond b) c1 q1 ==>
    SPEC m (p * cond ~b) c2 q2 ==>
    SPEC m (p) (c1 UNION c2) (q1 \/ q2)``,
  Cases_on `b` \\ SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]
  \\ METIS_TAC [SPEC_ADD_CODE,SEP_IMP_LEMMA,SPEC_WEAKEN,UNION_COMM]);

val X64_LISP_ADD = save_lisp_thm("X64_LISP_ADD",let
  val add_code =
    (codegenLib.assemble "x64" `
       dec r8d
       add r8d,r9d
       jnb L
       mov r8,r1
       mov r2d, 2
       jmp [r7-200]
    L: `)
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (el 1 add_code)
  val ((th2,_,_),_) = spec (el 2 add_code)
  val ((th3,_,_),th3a) = spec (el 3 add_code)
  val ((th4,_,_),_) = spec (el 4 add_code)
  val ((th5,_,_),_) = spec (el 5 add_code)
  fun the (SOME x) = x | the _ = fail();
  val (th3b,_,_) = the th3a
  val th = SPEC_COMPOSE_RULE [th1,th2,th3]
  val th = HIDE_STATUS_RULE true sts th
  val th = Q.INST [`r8`|->`w2w (a:word32)`] th
  val th = Q.INST [`r9`|->`w2w (b:word32)`] th
  val th = RW [select_twice] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_w2w,GSYM NOT_LESS,precond_def] th
  val imp = lisp_inv_add
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (LISP_ADD x0 x1,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val def = zLISP_def
  val res1 = prove_spec th imp def pre_tm post_tm
  val th = SPEC_COMPOSE_RULE [th1,th2,th3b,th4,th5]
  val th = HIDE_STATUS_RULE true sts th
  val th = Q.INST [`r8`|->`w2w (a:word32)`] th
  val th = Q.INST [`r9`|->`w2w (b:word32)`] th
  val th = RW [select_twice] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_w2w,precond_def] th
  val imp = lisp_inv_add_nop
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (Val 0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  val res2 = SPEC_COMPOSE_RULE [res,X64_LISP_ERROR]
  val lemma = prove(``cond b * cond c = cond (b /\ c)``,SIMP_TAC std_ss [SEP_CLAUSES])
  val res1 = RW [GSYM lemma, STAR_ASSOC] res1
  val res2 = RW [GSYM lemma, STAR_ASSOC] res2
  val set_lemma = prove(
    ``{x1;x2;x3} UNION {x1;x2;x3;x4;x5;x6} = {x1;x2;x3;x4;x5;x6}``,
    SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  val res = MATCH_MP (MATCH_MP SPEC_MERGE_LEMMA res1) res2
  val res = RW [STAR_ASSOC] (RW [set_lemma,lemma,GSYM STAR_ASSOC] res)
  in res end);

fun generate_add1 i = let
  val th = CONJUNCT1 (UNDISCH (UNDISCH lisp_inv_add1))
  val th = DISCH_ALL (MATCH_MP (swap_thm i) th)
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  val th1 = CONJUNCT2 (UNDISCH (UNDISCH lisp_inv_add1))
  val th1 = DISCH_ALL (MATCH_MP (DISCH_ALL th1) (UNDISCH (swap_thm i)))
  val th2 = UNDISCH th
  val th3 = UNDISCH th1
  val tm = fst (dest_imp (concl th2))
  in DISCH_ALL (DISCH tm (CONJ (UNDISCH th2) (UNDISCH th3))) end;

fun generate_add1_nop i = let
  val th = CONJUNCT1 (UNDISCH (UNDISCH lisp_inv_add1_nop))
  val th = DISCH_ALL (MATCH_MP (swap_thm i) th)
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  val th1 = CONJUNCT2 (UNDISCH (UNDISCH lisp_inv_add1_nop))
  val th1 = DISCH_ALL (MATCH_MP (DISCH_ALL th1) (UNDISCH (swap_thm i)))
  val th2 = UNDISCH th
  val th3 = UNDISCH th1
  val tm = fst (dest_imp (concl th2))
  in DISCH_ALL (DISCH tm (CONJ (UNDISCH th2) (UNDISCH th3))) end;

fun X64_LISP_ADD1 i = let
  val add_code =
    (codegenLib.assemble "x64" `
       add r8d,4
       jnb L
       mov r8,r1
       mov r2d, 2
       jmp [r7-200]
    L: `)
  val ((th1,_,_),_) = spec (x64_encode ("add " ^ (x64_reg i) ^ "d, 4"))
  val ((th2,_,_),th2a) = spec (el 2 add_code)
  val ((th3,_,_),_) = spec (x64_encode ("mov " ^ (x64_reg i) ^ ", r1"))
  val ((th4,_,_),_) = spec (el 4 add_code)
  fun the (SOME x) = x | the _ = fail();
  val (th2b,_,_) = the th2a
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val th = HIDE_STATUS_RULE true sts th
  val th = Q.INST [[QUOTE (x64_reg i ^ ":word64")]|->`w2w (a:word32)`] th
  val th = RW [select_twice] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_w2w,GSYM NOT_LESS,precond_def] th
  val imp = generate_add1 i
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->
                       Term [QUOTE ("LISP_ADD (x" ^ int_to_string i ^ ": SExp) (Val 1)")]] post_tm
  val def = zLISP_def
  val res1 = prove_spec th imp def pre_tm post_tm
  val th = SPEC_COMPOSE_RULE [th1,th2b,th3,th4]
  val th = HIDE_STATUS_RULE true sts th
  val th = Q.INST [[QUOTE (x64_reg i ^ ":word64")]|->`w2w (a:word32)`] th
  val th = RW [select_twice] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_w2w,precond_def] th
  val imp = generate_add1_nop i
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->``Val 0``] post_tm
  val res = prove_spec th imp def pre_tm post_tm
  val res2 = SPEC_COMPOSE_RULE [res,X64_LISP_ERROR]
  val lemma = prove(``cond b * cond c = cond (b /\ c)``,SIMP_TAC std_ss [SEP_CLAUSES])
  val res1 = RW [GSYM lemma, STAR_ASSOC] res1
  val res2 = RW [GSYM lemma, STAR_ASSOC] res2
  val set_lemma = prove(
    ``{x1;x2} UNION {x1;x2;x4;x5;x6} = {x1;x2;x4;x5;x6}``,
    SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  val res = MATCH_MP (MATCH_MP SPEC_MERGE_LEMMA res1) res2
  val res = RW [STAR_ASSOC] (RW [set_lemma,lemma,GSYM STAR_ASSOC] res)
  in save_lisp_thm("X64_LISP_ADD1_" ^ int_to_string i,res) end;

val _ = map X64_LISP_ADD1 all_regs;


(* sub, sub1 *)

val X64_LISP_SUB = save_lisp_thm("X64_LISP_SUB",let
  val (thm,temp_func_def) = decompile_io_strings x64_tools "temp_func"
    (SOME (``(r1:word64,r8:word64,r9:word64)``,``(r1:word64,r8:word64,r9:word64)``))
    (codegenLib.assemble "x64" `
       inc r8d
       sub r8d,r9d
       cmovb r8d,r1d `)
  val PUSH_IF = METIS_PROVE []
    ``((if b then (x,y,z) else (x,y2,z)) = (x,(if b then y else y2), z))``
  val temp_def = SIMP_RULE std_ss [LET_DEF,PUSH_IF] temp_func_def
  val sub_blast = prove(
    ``((31 -- 0) ((31 -- 0) (w2w a + 0x1w) - w2w b) = (w2w ((a+1w)-b:word32)):word64) /\
      ((31 -- 0) ((31 -- 0) (w2w a + 0x1w)) = (w2w (a + 1w)):word64) /\
      (w2w a <+ (w2w b):word64 = a <+ b)``,
    blastLib.BBLAST_TAC)
  val sub_blast2 = prove(
    ``((31 -- 0) a = w2w ((w2w (a:word64)):word32)) /\
      ((if b then w2w x else w2w y) = w2w (if b then x else y))``,
    STRIP_TAC THEN1 blastLib.BBLAST_TAC \\ METIS_TAC [])
  val th = SIMP_RULE std_ss [temp_def,LET_DEF] thm
    |> Q.INST [`r8`|->`w2w (a:word32)`,`r9`|->`w2w (b:word32)`]
    |> RW [car_blast,sub_blast] |> RW [sub_blast2]
  val lemma = METIS_PROVE [] ``(b==>c==>d) = (c==>b==>d)``
  val imp = RW1 [lemma] lisp_inv_sub
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (LISP_SUB x0 x1,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);

fun generate_sub1 i = let
  val th = UNDISCH (UNDISCH lisp_inv_sub1)
  val th = DISCH_ALL (MATCH_MP (swap_thm i) th)
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  in th end;

fun X64_LISP_SUB1 i = let
  val _ = print "z"
  val s = "sub " ^ (x64_reg i) ^ "d, 4"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_STATUS_RULE true sts th
  val def = zLISP_def
  val imp = generate_sub1 i
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->Term [QUOTE ("LISP_SUB (x" ^ int_to_string i ^ ": SExp) (Val 1)")]] post_tm
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_SUB1_" ^ int_to_string i,result) end;

val _ = map X64_LISP_SUB1 all_regs;

val X64_LISP_DIV2 = let
  val _ = print "z"
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (x64_encode "shr r8, 3")
  val ((th2,_,_),_) = spec (x64_encode "shl r8, 2")
  val ((th3,_,_),_) = spec (x64_encode "inc r8")
  val th = SPEC_COMPOSE_RULE [th1,th2,th3]
  val th = HIDE_STATUS_RULE true sts th
  val th = Q.INST [`r8:word64`|->`w2w (a:word32)`] th
  val th = Q.INST [`a`|->`r8`,`rip`|->`p`] th
  val lemma = blastLib.BBLAST_PROVE
    ``w2w a >>> 3 << 2 + 0x1w = (w2w:word32->word64) (a >>> 3 << 2 + 0x1w)``
  val th = RW [lemma] th
  val def = zLISP_def
  val lemma = METIS_PROVE [] ``(b==>c==>d) = (c==>b==>d)``
  val imp = RW1 [lemma] lisp_inv_div2
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (Val (getVal x0 DIV 2),x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_DIV2",result) end;


(* safe car and cdr *)

fun X64_LISP_SAFE_CAR_AUX i = let
  val _ = print "z"
  val enc = x64_encodeLib.x64_encode
  val hex = enc ("mov "^ x64_reg i ^"d, [r6+4*"^ x64_reg i ^"]")
  val code = [enc ("test "^ x64_reg i ^",1"),
              enc ("cmovne "^ x64_reg i ^",r0"),
              enc ("jne " ^ int_to_string (size hex div 2)),
              hex]
  val (th,f) = basic_decompile_strings x64_tools "foo" NONE code
  val def = SIMP_RULE std_ss [LET_DEF] (CONJ (GSYM mc_safe_car_def) (GSYM mc_safe_car_pre_def))
  val f = RW [def] (SIMP_RULE std_ss [LET_DEF,def] f)
  val th = RW [f] th
  val imp = DISCH_ALL (el (i+1) (CONJUNCTS (UNDISCH mc_safe_car_thm)))
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val s = [Term[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> Term[QUOTE ("SAFE_CAR x" ^ int_to_string i)]]
  val post_tm = subst s post_tm
  val res = prove_spec th imp def pre_tm post_tm
  in res end;

fun X64_LISP_SAFE_CDR_AUX i = let
  val _ = print "z"
  val enc = x64_encodeLib.x64_encode
  val hex = enc ("mov "^ x64_reg i ^"d, [r6+4*"^ x64_reg i ^"+4]")
  val code = [enc ("test "^ x64_reg i ^",1"),
              enc ("cmovne "^ x64_reg i ^",r0"),
              enc ("jne " ^ int_to_string (size hex div 2)),
              hex]
  val (th,f) = basic_decompile_strings x64_tools "foo" NONE code
  val def = SIMP_RULE std_ss [LET_DEF] (CONJ (GSYM mc_safe_cdr_def) (GSYM mc_safe_cdr_pre_def))
  val f = RW [def] (SIMP_RULE std_ss [LET_DEF,def] f)
  val th = RW [f] th
  val imp = DISCH_ALL (el (i+1) (CONJUNCTS (UNDISCH mc_safe_cdr_thm)))
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val s = [Term[QUOTE ("x" ^ int_to_string i ^ ":SExp")] |-> Term[QUOTE ("SAFE_CDR x" ^ int_to_string i)]]
  val post_tm = subst s post_tm
  val res = prove_spec th imp def pre_tm post_tm
  in res end;

val ALL_X64_LISP_SAFE_CAR = map X64_LISP_SAFE_CAR_AUX [0,1,2,3,4,5]
val ALL_X64_LISP_SAFE_CDR = map X64_LISP_SAFE_CDR_AUX [0,1,2,3,4,5]

fun X64_LISP_SAFE_CAR_CDR (i,j) = (print "z";
  if i = j then let
  val postfix = (int_to_string i) ^ (int_to_string j)
  val th_car = el (i+1) ALL_X64_LISP_SAFE_CAR
  val th_cdr = el (i+1) ALL_X64_LISP_SAFE_CDR
  val _ = save_lisp_thm("X64_LISP_SAFE_CAR" ^ postfix,th_car)
  val _ = save_lisp_thm("X64_LISP_SAFE_CDR" ^ postfix,th_cdr)
  in (th_car,th_cdr) end else let
  val postfix = (int_to_string i) ^ (int_to_string j)
  val th = fetch "-" ("X64_LISP_MOVE" ^ postfix)
  val th_car = SPEC_COMPOSE_RULE [th,el (i+1) ALL_X64_LISP_SAFE_CAR]
  val th_cdr = SPEC_COMPOSE_RULE [th,el (i+1) ALL_X64_LISP_SAFE_CDR]
  val _ = save_lisp_thm("X64_LISP_SAFE_CAR" ^ postfix,th_car)
  val _ = save_lisp_thm("X64_LISP_SAFE_CDR" ^ postfix,th_cdr)
  in (th_car,th_cdr) end);

val _ = map X64_LISP_SAFE_CAR_CDR all_reg_pairs;


(* sfix *)

val fix_lemma = prove(
  ``(b ==> SPEC m p c (q1 * q)) ==>
    (~b ==> SPEC m p c (q2 * q)) ==>
    SPEC m p c ((if b then q1 else q2) * q)``,
  METIS_TAC []);

val SFIX_def = Define `SFIX s = if isSym s then s else Sym "NIL"`;

fun X64_LISP_SFIX i = let
  val _ = print "z"
  val s = "cmovne " ^ (x64_reg i) ^ "d, r0d"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),ex) = spec s
  fun the (SOME x) = x | the _ = fail();
  val (th2,_,_) = the ex
  val def = zLISP_def
  val imp = lisp_inv_swap0
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME z_zf) * precond z_zf``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME z_zf)``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th2)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result2 = prove_spec th2 imp def pre_tm post_tm
  val imp = UNDISCH lisp_inv_nil
  val imp = DISCH_ALL (MATCH_MP (swap_thm i) imp)
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH (swap_thm i)))
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME z_zf) * precond ~z_zf``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME z_zf)``
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->``Sym "NIL"``] post_tm
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th1)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result1 = prove_spec th1 imp def pre_tm post_tm
  val res1 = RW [GSYM STAR_ASSOC] (RW [precond_def,SPEC_MOVE_COND] result1)
  val res2 = RW [GSYM STAR_ASSOC] (RW [precond_def,SPEC_MOVE_COND] result2)
  val res = RW [STAR_ASSOC] (MATCH_MP (MATCH_MP fix_lemma res2) res1)
  val test = fetch "-" ("X64_LISP_ISSYM" ^ int_to_string i)
  val res = SPEC_COMPOSE_RULE [test,res]
  val res = HIDE_STATUS_RULE true sts res
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->Term [QUOTE ("SFIX x" ^ int_to_string i ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl res)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val th = SPEC post_tm (MATCH_MP SPEC_WEAKEN res)
  val goal = (cdr o car o concl) th
  val lemma = prove(goal,SRW_TAC [] [] \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,SFIX_def])
  val th = MP th lemma
  in save_lisp_thm("X64_LISP_SFIX_" ^ int_to_string i,th) end;

val _ = map X64_LISP_SFIX all_regs;


(* nfix *)

val NFIX_def = Define `NFIX s = if isVal s then s else Val 0`;

fun X64_LISP_NFIX i = let
  val _ = print "z"
  val s = "cmovne " ^ (x64_reg i) ^ "d, r1d"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),ex) = spec s
  fun the (SOME x) = x | the _ = fail();
  val (th2,_,_) = the ex
  val def = zLISP_def
  val imp = lisp_inv_swap0
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME z_zf) * precond z_zf``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME z_zf)``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th2)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result2 = prove_spec th2 imp def pre_tm post_tm
  val imp = UNDISCH lisp_inv_zero
  val imp = DISCH_ALL (MATCH_MP (swap_thm i) imp)
  val imp = DISCH_ALL (MATCH_MP imp (UNDISCH (swap_thm i)))
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME z_zf) * precond ~z_zf``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * zS1 Z_ZF (SOME z_zf)``
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->``Val 0``] post_tm
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th1)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val result1 = prove_spec th1 imp def pre_tm post_tm
  val res1 = RW [GSYM STAR_ASSOC] (RW [precond_def,SPEC_MOVE_COND] result1)
  val res2 = RW [GSYM STAR_ASSOC] (RW [precond_def,SPEC_MOVE_COND] result2)
  val res = RW [STAR_ASSOC] (MATCH_MP (MATCH_MP fix_lemma res2) res1)
  val test = fetch "-" ("X64_LISP_ISVAL" ^ int_to_string i)
  val res = SPEC_COMPOSE_RULE [test,res]
  val res = HIDE_STATUS_RULE true sts res
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->Term [QUOTE ("NFIX x" ^ int_to_string i ^ ": SExp")]] post_tm
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl res)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val th = SPEC post_tm (MATCH_MP SPEC_WEAKEN res)
  val goal = (cdr o car o concl) th
  val lemma = prove(goal,SRW_TAC [] [] \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,NFIX_def])
  val th = MP th lemma
  in save_lisp_thm("X64_LISP_NFIX_" ^ int_to_string i,th) end;

val _ = map X64_LISP_NFIX all_regs;


(* print statistics -- used before and after gc *)

val stats = [(``1``, mc_print_stats1_spec, mc_print_stats1_thm, "1"),
             (``2``, mc_print_stats2_spec, mc_print_stats2_thm, "2")]

fun X64_LISP_PRINT_STATS (tm,th,imp,name) = let
  val th = Q.INST [`ior`|->`EL 0 cs`,
                   `iow`|->`EL 1 cs`,
                   `iod`|->`EL 2 cs`,
                   `ioi`|->`EL 0 ds`,
                   `r8`|->`w2w (w0:word32)`] th
  val imp = SIMP_RULE std_ss [LET_DEF] imp
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,IO_STATS ^tm io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_PRINT_STATS" ^ name, res) end;

val X64_LISP_PRINT_STATS_BEGIN = X64_LISP_PRINT_STATS (el 1 stats);
val X64_LISP_PRINT_STATS_END = X64_LISP_PRINT_STATS (el 2 stats);


(* push and cons test *)

val SPEC_MERGE_LEMMA = prove(
  ``SPEC m p c q ==> SPEC m p (c UNION c') (q \/ q') /\
                     SPEC m p (c' UNION c) (q' \/ q)``,
  `SEP_IMP q (q \/ q')` by SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]
  \\ `SEP_IMP q (q' \/ q)` by SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC SPEC_WEAKEN
  \\ METIS_TAC [SPEC_ADD_CODE,UNION_COMM]);

val push_lemma = prove(
  ``SPEC X64_MODEL
     (zLISP_ALT b1 ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * p) c1 q1 ==>
    SPEC X64_MODEL
     (zLISP_ALT b2 ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * p) c2 q2 ==>
    (!wsp wi we ds tw2. b1 wsp wi we ds tw2 \/ b2 wsp wi we ds tw2) ==>
    SPEC X64_MODEL
     (zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * p) (c1 UNION c2) (q1 \/ q2)``,
  SIMP_TAC (std_ss++sep_cond_ss) [zLISP_def,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS,
     SPEC_MOVE_COND,zLISP_ALT_def]
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!wsp wi we ds tw2. b1 wsp wi we ds tw2 \/ b2 wsp wi we ds tw2` (STRIP_ASSUME_TAC o SPEC_ALL)
  \\ RES_TAC \\ METIS_TAC [SPEC_MERGE_LEMMA]);

val X64_LISP_PUSH_TEST = let
  val branch_taken_prefix = "3E"
  val x1 = x64_encodeLib.x64_encode "test r3,r3"
  val x2 = branch_taken_prefix ^ (x64_encodeLib.x64_encode "jne 9")
  val x3 = x64_encodeLib.x64_encode "mov r2d,r1d"
  val x4 = x64_encodeLib.x64_encode "jmp [r7-200]"
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec x1
  val ((th2,_,_),th2a) = spec x2
  val ((th3,_,_),_) = spec x3
  fun the (SOME x) = x | the _ = fail();
  val (th2b,_,_) = the th2a
  val th = SPEC_COMPOSE_RULE [th1,th2b,th3]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] th
  val def = zLISP_ALT_def
  val imp = Q.INST [`temp`|->`(31 -- 0) tw1`] lisp_inv_ignore_tw2
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (wsp = 0w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (wsp = 0w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post1_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val post1_tm = subst [``rip:word64`` |-> cdr tm] post1_tm
  val result2 = prove_spec th imp def pre_tm post_tm
  val (th,goal) = SPEC_WEAKEN_RULE result2 post1_tm
  val lemma = prove(goal,SIMP_TAC std_ss [GSYM STAR_ASSOC,SEP_IMP_zLISP_ALT_zLISP])
  val res2 = SPEC_COMPOSE_RULE [MP th lemma,X64_LISP_ERROR]
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] th
  val def = zLISP_ALT_def
  val imp = lisp_inv_swap0
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ~(wsp = 0w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ~(wsp = 0w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val res1 = prove_spec th imp def pre_tm post_tm
  val th = MATCH_MP push_lemma (RW [GSYM STAR_ASSOC] res1)
  val th = MATCH_MP th (RW [GSYM STAR_ASSOC] res2)
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [markerTheory.Abbrev_def])) th
  val set_lemma = prove(
    ``{x1;x2} UNION {x1;x2;x3;x4} = {x1;x2;x3;x4}``,
    SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  val th = RW [STAR_ASSOC,set_lemma] th
  in th end;

val X64_LISP_CONS_TEST = let
  val cons_test_code =
    (codegenLib.assemble "x64" `
       cmp r14,r15
       jne L
       xor r2d,r2d
       jmp [r7-200]
    L: `)
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (el 1 cons_test_code)
  val ((th2,_,_),th2a) = spec (el 2 cons_test_code)
  val ((th3,_,_),_) = spec (el 3 cons_test_code)
  fun the (SOME x) = x | the _ = fail();
  val (th2b,_,_) = the th2a
  val th = SPEC_COMPOSE_RULE [th1,th2b,th3]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] th
  val def = zLISP_ALT_def
  val imp = Q.INST [`temp`|->`0w`] lisp_inv_ignore_tw2
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (wi = we)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (wi = we)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post1_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val post1_tm = subst [``rip:word64`` |-> cdr tm] post1_tm
  val result2 = prove_spec th imp def pre_tm post_tm
  val (th,goal) = SPEC_WEAKEN_RULE result2 post1_tm
  val lemma = prove(goal,SIMP_TAC std_ss [GSYM STAR_ASSOC,SEP_IMP_zLISP_ALT_zLISP])
  val res2 = SPEC_COMPOSE_RULE [MP th lemma,X64_LISP_ERROR]
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] th
  val def = zLISP_ALT_def
  val imp = lisp_inv_swap0
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ~(wi = we)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ~(wi = we)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val res1 = prove_spec th imp def pre_tm post_tm
  val th = MATCH_MP push_lemma (RW [GSYM STAR_ASSOC] res1)
  val th = MATCH_MP th (RW [GSYM STAR_ASSOC] res2)
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [markerTheory.Abbrev_def])) th
  val set_lemma = prove(
    ``{x1;x2} UNION {x1;x2;x3;x4} = {x1;x2;x3;x4}``,
    SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  val th = RW [STAR_ASSOC,set_lemma] th
  in th end;

val SPEC_DISJ_FRAME_LEMMA = prove(
  ``(s \/ SEP_F = s) /\ (SEP_F \/ s = s)``,
  SIMP_TAC std_ss [FUN_EQ_THM,SEP_DISJ_def,SEP_F_def]);

val SPEC_DISJ_FRAME = prove(
  ``!x p c q. SPEC x p c q ==> !r. SPEC x (p \/ r) c (q \/ r)``,
  METIS_TAC [SPEC_MERGE,SPEC_REFL,UNION_IDEMPOT,SPEC_DISJ_FRAME_LEMMA]);

val SPEC_DISJ_COMPOSE = prove(
  ``SPEC m q c2 q1 ==>
    SPEC m p c1 (q \/ q2) ==>
    SPEC m p (c1 UNION c2) (q1 \/ q2)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_COMPOSE \\ Q.EXISTS_TAC `q \/ q2`
  \\ ASM_SIMP_TAC std_ss [SPEC_DISJ_FRAME]);

val X64_LISP_FULL_GC = let
  val lemma = prove(``!x n. IO_STATS n x = x``,Cases THEN SIMP_TAC std_ss [IO_STATS_def])
  val th0 = fetch "-" "X64_LISP_CALL_EL5"
  val th1 = X64_LISP_PRINT_STATS_BEGIN
  val th2 = X64_LISP_GC
  val th3 = X64_LISP_PRINT_STATS_END
  val th4 = X64_LISP_CONS_TEST
  val th5 = Q.INST [`b`|->`(\wsp wi we ds tw2. Abbrev (wi <> we))`] X64_LISP_ALT_RET
  val th = RW [lemma] (SPEC_COMPOSE_RULE [th1,th2,th3,th4])
  val th = MATCH_MP (MATCH_MP SPEC_DISJ_COMPOSE th5) (Q.INST [`qs`|->`q::qs`] th)
  val th = RW [INSERT_UNION_EQ,UNION_EMPTY] th
  val (_,_,c,_) = dest_spec (concl th)
  val name = mk_var("abbrev_code_for_cons",mk_type("fun",[``:word64``,type_of c]))
  val def = Define [ANTIQUOTE (mk_eq(mk_comb(name,``p:word64``),c))]
  val th = RW [GSYM def] th
  val th = SPEC_COMPOSE_RULE [th0,th]
  in th end;

val X64_LISP_CONS_TEST_WITH_GC = let
  val branch_taken_prefix = "3E"
  val x1 = x64_encodeLib.x64_encode "cmp r14,r15"
  val x2 = branch_taken_prefix ^ (x64_encodeLib.x64_encode "jne 10")
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec x1
  val ((th2,_,_),th2a) = spec x2
  fun the (SOME x) = x | the _ = fail();
  val (th2b,_,_) = the th2a
  (* case: gc call *)
  val th = SPEC_COMPOSE_RULE [th1,th2b]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] th
  val th = Q.INST [`rip` |-> `p`] th
  val def = zLISP_ALT_def
  val imp = lisp_inv_swap0
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (wi = we)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res2 = prove_spec th imp def pre_tm post_tm
  val res2 = RW [GSYM zLISP_raw] res2
  val res2 = SPEC_COMPOSE_RULE [res2,X64_LISP_FULL_GC]
  (* case: no gc call *)
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] th
  val th = Q.INST [`rip` |-> `p`] th
  val def = zLISP_ALT_def
  val imp = lisp_inv_swap0
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ~(wi = we)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ~(wi = we)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res1 = prove_spec th imp def pre_tm post_tm
  val th = MATCH_MP push_lemma (RW [GSYM STAR_ASSOC] res1)
  val th = MATCH_MP th (RW [GSYM STAR_ASSOC] res2)
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [markerTheory.Abbrev_def])) th
  val set_lemma = prove(
    ``(x1 INSERT s) UNION (x1 INSERT t) = x1 INSERT (s UNION t)``,
    SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  val th = RW [STAR_ASSOC,set_lemma,UNION_EMPTY] th
  val th = RW [SEP_CLAUSES,GSYM SEP_DISJ_ASSOC] th
  in th end;


(* push *)

val SPEC_DISJ_COMPOSE = prove(
  ``SPEC m q c2 q1 ==>
    SPEC m p c1 (q \/ q2) ==>
    SPEC m p (c1 UNION c2) (q1 \/ q2)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_COMPOSE \\ Q.EXISTS_TAC `q \/ q2`
  \\ ASM_SIMP_TAC std_ss [SPEC_DISJ_FRAME]);

fun X64_LISP_PUSH i = let
  val _ = print "z"
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (x64_encode ("dec r3"))
  val ((th2,_,_),_) = spec (x64_encode ("mov [r7+4*r3], " ^ x64_reg i ^ "d"))
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [car_blast] th
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (wsp <> 0x0w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,x::xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val s = [``x:SExp`` |-> (Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")])]
  val post_tm = subst s post_tm
  val imp = UNDISCH (CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM markerTheory.Abbrev_def])) lisp_inv_push)
  val assum = hd (hyp imp)
  val thi = CONJUNCT1 (UNDISCH (imp))
  val thi = DISCH_ALL (MATCH_MP (swap_thm i) thi)
  val thi = DISCH_ALL (MATCH_MP thi (UNDISCH (swap_thm i)))
  val thj = CONJUNCT2 (UNDISCH (imp))
  val thj = DISCH_ALL (MATCH_MP (DISCH_ALL thj) (UNDISCH (swap_thm i)))
  val imp = (CONJ (UNDISCH_ALL thi) (UNDISCH_ALL thj))
  val assum2 = hd (filter (fn x => x !~ assum) (hyp imp))
  val imp = DISCH assum2 imp
  val result = prove_spec th imp def pre_tm post_tm
  val result = RW [GSYM zLISP_raw] result
  val th = MATCH_MP (MATCH_MP SPEC_DISJ_COMPOSE result) X64_LISP_PUSH_TEST
  val th = SIMP_RULE std_ss [INSERT_UNION_EQ,UNION_EMPTY,word_arith_lemma1] th
  in save_lisp_thm("X64_LISP_PUSH_" ^ int_to_string i,th) end;

val _ = map X64_LISP_PUSH all_regs;


(* cons *)

val lisp_inv_cons_alt =
  CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM markerTheory.Abbrev_def])) lisp_inv_cons;

fun aux_swap th i j = let
  val thi = CONJUNCT1 (UNDISCH_ALL th)
  val thi = DISCH_ALL (MATCH_MP (generate_swap i j) thi)
  val thi = DISCH_ALL (MATCH_MP thi (UNDISCH (generate_swap i j)))
  val thj = CONJUNCT2 (UNDISCH_ALL th)
  val thj = DISCH_ALL (MATCH_MP (DISCH_ALL thj) (UNDISCH (generate_swap i j)))
  in CONJ (UNDISCH_ALL thi) (UNDISCH_ALL thj) end

fun generate_cons i j =
  if i = 0 andalso j = 1 then UNDISCH_ALL lisp_inv_cons_alt else
  if i = 0 then aux_swap lisp_inv_cons_alt 1 j else
  if i = 1 then let
    val th = aux_swap lisp_inv_cons_alt 0 1
    val th = aux_swap th 0 j
    in th end
  else if j = 1 then aux_swap lisp_inv_cons_alt 0 i else let
    val th = aux_swap lisp_inv_cons_alt 0 i
    val th = aux_swap th 1 j
    in th end;

fun X64_LISP_CONS (i,j) = if i = j then TRUTH else let
  val _ = print "z"
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (x64_encode ("mov [r6+4*r14+4], " ^ x64_reg j ^ "d"))
  val ((th2,_,_),_) = spec (x64_encode ("mov [r6+4*r14], " ^ x64_reg i ^ "d"))
  val ((th3,_,_),_) = spec (x64_encode ("mov " ^ x64_reg i ^ "d, r14d"))
  val ((th4,_,_),_) = spec (x64_encode ("add r14,2"))
  val th = SPEC_COMPOSE_RULE [th1,th2,th3,th4]
  val th = HIDE_STATUS_RULE true sts th
  val th = Q.INST [[QUOTE (x64_reg i ^ ":word64")]|->`w2w (a:word32)`] th
  val th = Q.INST [[QUOTE (x64_reg j ^ ":word64")]|->`w2w (b:word32)`] th
  val th = RW [car_blast] th
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (wi <> we)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val s = [Term [QUOTE ("x" ^ int_to_string i ^ ":SExp")] |->
           Term [QUOTE ("Dot x" ^ int_to_string i ^ " x" ^ int_to_string j)]]
  val post_tm = subst s post_tm
  val imp = generate_cons i j
  val h = lisp_inv_cons_alt |> concl |> dest_imp |> fst
  val assum = hd (filter (fn x => x !~ h) (hyp imp))
  val imp = DISCH assum imp
  val result = prove_spec th imp def pre_tm post_tm
  val result = RW [GSYM zLISP_raw] result
  val th = MATCH_MP (MATCH_MP SPEC_DISJ_COMPOSE result) X64_LISP_CONS_TEST_WITH_GC
  val th = SIMP_RULE std_ss [word_arith_lemma1,INSERT_UNION_EQ] th
  in save_lisp_thm("X64_LISP_CONS_" ^ int_to_string i ^ int_to_string j,th) end;

val _ = map X64_LISP_CONS all_distinct_reg_pairs;


(* pop *)

val X64_LISP_POP = save_lisp_thm("X64_LISP_POP",let
  val _ = print "z"
  val s = "inc r3"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = HIDE_STATUS_RULE true sts th
  val lemma = METIS_PROVE [] ``(b==>c==>d) = (c==>b==>d)``
  val imp = RW1 [lemma] lisp_inv_pop
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,TL xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);


(* top *)

fun generate_top i = let
  val th = CONJUNCT1 (UNDISCH (UNDISCH lisp_inv_top))
  val th = DISCH_ALL (MATCH_MP (swap_thm i) th)
  val th = DISCH_ALL (MATCH_MP th (UNDISCH (swap_thm i)))
  val th1 = CONJUNCT2 (UNDISCH (UNDISCH lisp_inv_top))
  val th1 = DISCH_ALL (MATCH_MP (DISCH_ALL th1) (UNDISCH (swap_thm i)))
  val th2 = UNDISCH (RW [AND_IMP_INTRO] th)
  val th3 = UNDISCH (RW [AND_IMP_INTRO] th1)
  in RW [GSYM AND_IMP_INTRO] (DISCH_ALL (CONJ th2 th3)) end;

fun X64_LISP_TOP i = let
  val _ = print "z"
  val s = "mov " ^ (x64_reg i) ^ "d, [r7+4*r3]"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val def = zLISP_def
  val imp = generate_top i
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = subst [Term [QUOTE ("x" ^ int_to_string i ^ ": SExp")]|->``(HD xs):SExp``] post_tm
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val th = RW [car_blast] th
  val result = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_TOP_" ^ int_to_string i,result) end;

val _ = map X64_LISP_TOP all_regs;


(* load *)

val load_blast = prove(
  ``!j. n2w (SIGN_EXTEND 32 64 (w2n ((0x4w:word32) * w2w (j:29 word)))) =
        4w * (w2w j):word64``,
  Cases \\ ASM_SIMP_TAC std_ss [w2w_def,w2n_n2w,word_mul_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ `(4 * n) < 4294967296` by DECIDE_TAC
  \\ `(4 * n) < 2147483648` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ FULL_SIMP_TAC std_ss [SIGN_EXTEND_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [BIT_def,BITS_THM,LESS_DIV_EQ_ZERO]);

val X64_LISP_LOAD = save_lisp_thm("X64_LISP_LOAD",let
  val s = "mov r8d, [r7+4*r3+6000]"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec (String.substring(s,0,size(s)-8))
  val th = RW [GSYM w2w_def,car_blast] th
  val th = Q.INST [`imm32`|->`4w*w2w (j:29 word)`] th
  val th = RW [load_blast] th
  val lemma = METIS_PROVE [] ``(b==>c==>d) = (c==>b==>d)``
  val imp = RW1[lemma]lisp_inv_load
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = set_pc th ``zLISP ^STAT (EL (w2n (j:29 word)) xs,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);


(* store *)

val X64_LISP_STORE = save_lisp_thm("X64_LISP_STORE",let
  val s = "mov [r7+4*r3+256], r8d"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec (String.substring(s,0,size(s)-8))
  val th = RW [GSYM w2w_def,car_blast] th
  val th = Q.INST [`imm32`|->`4w*w2w (j:29 word)`] th
  val th = RW [load_blast] th
  val lemma = METIS_PROVE [] ``(b==>c==>d) = (c==>b==>d)``
  val imp = RW1[lemma]lisp_inv_store
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,UPDATE_NTH (w2n (j:29 word)) x0 xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);


(* pops *)

val X64_LISP_POPS_LEMMA = prove(
  ``SIGN_EXTEND 32 64 (w2n ((w2w imm30):word32)) = w2n (imm30:word30)``,
  Cases_on `imm30` \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [bitTheory.SIGN_EXTEND_def,
     LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM,w2w_def,w2n_n2w]
  \\ `n < 4294967296` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `n < 2147483648` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LESS_DIV_EQ_ZERO \\ ASM_SIMP_TAC std_ss []);

val X64_LISP_POPS = save_lisp_thm("X64_LISP_POPS",let
  val _ = print "z"
  val s = "add r3,5000"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec (String.substring(s,0,size(s)-8))
  val th = Q.INST [`imm32`|->`w2w (imm30:word30)`] th
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [X64_LISP_POPS_LEMMA,GSYM w2w_def] th
  val th = Q.INST [`imm30`|->`j`] th
  val lemma = METIS_PROVE [] ``(b==>c==>d) = (c==>b==>d)``
  val imp = RW1 [lemma] (SIMP_RULE std_ss [LET_DEF] lisp_inv_pops)
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,DROP (w2n (j:word30)) xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);


(* print various strings *)

val prints = [(``"\n"``, mc_print_nl_spec,mc_print_nl_thm,"NEWLINE"),
              (``"'"``, mc_print_qt_spec,mc_print_qt_thm,"QUOTE"),
              (``"("``, mc_print_open_spec,mc_print_open_thm,"OPEN"),
              (``")"``, mc_print_close_spec,mc_print_close_thm,"CLOSE"),
              (``" . "``, mc_print_dot_spec,mc_print_dot_thm,"DOT"),
              (``" "``, mc_print_sp_spec,mc_print_sp_thm,"SPACE")]

fun X64_LISP_PRINT (tm,th,imp,name) = let
  val th = Q.INST [`ior`|->`EL 0 cs`,
                   `x`|->`EL 1 cs`,
                   `y`|->`EL 2 cs`,
                   `z`|->`EL 0 ds`] th
  val imp = SIMP_RULE std_ss [LET_DEF] imp
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,IO_WRITE io ^tm,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_PRINT_" ^ name, res) end;

val _ = map X64_LISP_PRINT prints;


(* print number *)

val X64_LISP_PRINT_NUMBER = save_lisp_thm("X64_LISP_PRINT_NUMBER",let
  val th = Q.INST [`ior`|->`EL 0 cs`,
                   `x`|->`EL 1 cs`,
                   `y`|->`EL 2 cs`,
                   `z`|->`EL 0 ds`] mc_print_num_full_spec
  val imp = mc_print_num_full_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",x4,x5,xs,xs1,IO_WRITE io (num2str (getVal x0)),xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);


(* print symbol *)

val X64_LISP_PRINT_SYMBOL = save_lisp_thm("X64_LISP_PRINT_SYMBOL",let
  val th = Q.INST [`ior`|->`EL 0 cs`,
                   `x`|->`EL 1 cs`,
                   `y`|->`EL 2 cs`,
                   `z`|->`EL 0 ds`] mc_print_sym_full_spec
  val imp = mc_print_sym_full_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",x4,x5,xs,xs1,IO_WRITE io (sym2str (getSym x0)),xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);


(* init *)

val X64_LISP_INIT = save_thm("X64_LISP_INIT",let
  val th = SPEC_FRAME_RULE mc_full_init_spec ``zIO (EL 0 cs,EL 1 cs,EL 2 cs,EL 0 ds) io * zCODE_MEMORY ddd dd d * zSTACK rbp qs * zCODE_UNCHANGED cu dd d * cond (lisp_init (a1,a2,sl,sl1,e,ex,cs) io (df,f,dg,g,dd,d,sp,sa1,sa_len,ds))``
  val th = Q.INST [`r7`|->`sp`] th
  val post = set_pc th ``zLISP ^STAT (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",[],[],io,0,qs,NO_CODE,w2n (EL 3 cs),T) * zPC p * ~zS``
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND,STAR_ASSOC] \\ STRIP_TAC
    \\ IMP_RES_TAC mc_full_init_thm \\ ASM_SIMP_TAC std_ss [LET_DEF,zLISP_def]
    \\ ASM_SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_EXISTS_THM,SEP_CLAUSES,cond_STAR]
    \\ Q.PAT_X_ASSUM `!qs.bbb` (MP_TAC o SPEC_ALL) \\ STRIP_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ AUTO_EXISTS_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [EL_UPDATE_NTH])
  val th = MP th lemma
  val th = foldr (uncurry Q.GEN) th [`df`,`f`,`dg`,`g`,`sp`,`sa1`,`sa_len`,`ds`,`dd`,`d`]
  val th = SIMP_RULE std_ss [SPEC_PRE_EXISTS] th
  val pre = ``zLISP_INIT (a1,a2,sl,sl1,e,ex,rbp,cs,qs,ddd,cu) io * zPC p * ~zS``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zLISP_INIT_def,SEP_CLAUSES]
    \\ SIMP_TAC (std_ss++star_ss) [] \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_REFL,mc_full_init_pre_thm])
  val th = MP th lemma
  in th end);


(* Produce "syntax error" *)

val remove_parse_stack_def = PmatchHeuristics.with_classic_heuristic Define `
  (remove_parse_stack (Sym "NIL"::xs) = xs) /\
  (remove_parse_stack (Sym "CONS"::[]) = []) /\
  (remove_parse_stack (Sym "CONS"::x::xs) = remove_parse_stack xs) /\
  (remove_parse_stack (Val n::xs) = remove_parse_stack xs) /\
  (remove_parse_stack (Sym "CAR"::xs) = remove_parse_stack xs) /\
  (remove_parse_stack (Sym "CDR"::xs) = remove_parse_stack xs) /\
  (remove_parse_stack (Sym "QUOTE"::xs) = remove_parse_stack xs)`;

val X64_LISP_SYNTAX_ERROR = save_lisp_thm("X64_LISP_SYNTAX_ERROR",let
  val s = x64_encode "mov r2d,5"
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val imp = Q.INST [`temp`|->`5w`] lisp_inv_ignore_tw2
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val res = prove_spec th imp def pre_tm post_tm
  val th = SPEC_COMPOSE_RULE [res,X64_LISP_ERROR]
  val s2 = x64_encode "jmp [r7-200]"
  val s_len = numSyntax.term_of_int (size (s ^ s2) div 2)
  val (_,_,_,post2_tm) = dest_spec (concl th)
  val post1_tm = subst [``n:num``|->s_len] ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,remove_parse_stack xs,xs1,io,xbp,qs,code,amnt,ok) * ~zS * zPC (rip + n2w n)``
  val (th,goal) = SPEC_WEAKEN_RULE th (mk_sep_disj(post1_tm,post2_tm))
  val lemma = prove(goal,SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def])
  val th = MP th lemma
  in th end);

val X64_LISP_RAW_RUNTIME_ERROR = save_thm("X64_LISP_RAW_RUNTIME_ERROR",let
  val s = x64_encode "mov r2d,4"
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val imp = Q.INST [`temp`|->`4w`] lisp_inv_ignore_tw2
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val res = prove_spec th imp def pre_tm post_tm
  val th = SPEC_COMPOSE_RULE [res,X64_LISP_ERROR]
  in th end);

val X64_LISP_RUNTIME_ERROR = save_lisp_thm("X64_LISP_RUNTIME_ERROR",let
  val s = x64_encode "mov r2d,4"
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = X64_LISP_RAW_RUNTIME_ERROR
  val s2 = x64_encode "jmp [r7-200]"
  val s_len = numSyntax.term_of_int (size (s ^ s2) div 2)
  val (_,_,_,post2_tm) = dest_spec (concl th)
  val post1_tm = subst [``n:num``|->s_len] ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,remove_parse_stack xs,io,xbp,qs,code,amnt,ok) * ~zS * zPC (rip + n2w n)``
  val (th,goal) = SPEC_WEAKEN_RULE th (mk_sep_disj(post1_tm,post2_tm))
  val lemma = prove(goal,SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def])
  val th = MP th lemma
  in th end);

val no_such_function_def = Define `no_such_function x0 = x0:SExp`;
val X64_LISP_ERROR_11 = save_lisp_thm("X64_LISP_ERROR_11",let
  val s = x64_encode "mov r2d,11"
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val imp = Q.INST [`temp`|->`11w`] lisp_inv_ignore_tw2
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip``
  val res = prove_spec th imp def pre_tm post_tm
  val th = SPEC_COMPOSE_RULE [res,X64_LISP_ERROR]
  val s2 = x64_encode "jmp [r7-200]"
  val s_len = numSyntax.term_of_int (size (s ^ s2) div 2)
  val (_,_,_,post2_tm) = dest_spec (concl th)
  val post1_tm = subst [``n:num``|->s_len] ``zLISP ^STAT (no_such_function x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * ~zS * zPC (rip + n2w n)``
  val (th,goal) = SPEC_WEAKEN_RULE th (mk_sep_disj(post1_tm,post2_tm))
  val lemma = prove(goal,SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def])
  val th = MP th lemma
  in th end);


(* LISP_R intro and elim *)

val (mc_lisp_r_intro_spec,mc_lisp_r_intro_def) = basic_decompile_strings x64_tools "mc_lisp_r_intro"
  (SOME (``(r1:word64,r2:word64,r7:word64,df:word64 set,f:word64->word32)``,
         ``(r1:word64,r2:word64,r7:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
      mov r2,[r7-184]
      mov r1,[r7-112]  `);

val align_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a - w && 3w = 0w) = (w && 3w = 0w:word64))``

val X64_LISP_R_INTRO = let
  val th = SPEC_FRAME_RULE mc_lisp_r_intro_spec
    ``zR 0x0w tw0 * zR 0x3w wsp *
      zR 0x6w bp * zR 0x8w (w2w w0) * zR 0x9w (w2w w1) *
      zR 0xAw (w2w w2) * zR 0xBw (w2w w3) * zR 0xCw (w2w w4) *
      zR 0xDw (w2w w5) * zR 0xEw wi * zR 0xFw we * zSTACK rbp qs *
      zBYTE_MEMORY dg g * zCODE_MEMORY ddd dd d * zIO (EL 0 cs,EL 1 cs,EL 2 cs,EL 0 ds) io *
      zCODE_UNCHANGED cu dd d *
      cond
        (lisp_inv ^STATINV (x0,x1,x2,x3,x4,x5,^VAR_REST)
           (w0,w1,w2,w3,w4,w5,df,f,dg,g,bp,bp2,wsp,wi,we,tw0,tw1,tw2,sp,
            ds,sa1,sa2,sa3,dd,d))``
  val th = Q.INST [`r7`|->`sp`,`r1`|->`tw1`,`r2`|->`tw2`] th
  val post = set_pc th ``zLISP_R ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND,STAR_ASSOC] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [mc_lisp_r_intro_def]
    \\ IMP_RES_TAC lisp_inv_cs_read
    \\ IMP_RES_TAC lisp_inv_ds_read
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ ASM_SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_EXISTS_THM,SEP_CLAUSES,cond_STAR,zLISP_R_def]
    \\ REPEAT STRIP_TAC \\ AUTO_EXISTS_TAC \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [zIO_R_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ Q.EXISTS_TAC `EL 0 ds` \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = foldr (uncurry Q.GEN) th [`tw0`,`tw1`,`tw2`,`wsp`,`bp`,`sp`,`w0`,`w1`,`w2`,`w3`,`w4`,`w5`,`wi`,`we`,`df`,`f`,`dg`,`g`,`bp2`,`ds`,`sa1`,`sa2`,`sa3`,`dd`,`d`]
  val th = SIMP_RULE std_ss [SPEC_PRE_EXISTS] th
  val pre = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val lemma2 = prove(
    ``mc_lisp_r_intro_pre (r1,r2,sp,df,f) /\ ^LISP = ^LISP``,
    REPEAT STRIP_TAC \\ EQ_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [mc_lisp_r_intro_def]
    \\ IMP_RES_TAC lisp_inv_cs_read
    \\ IMP_RES_TAC lisp_inv_ds_read
    \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
    \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,LET_DEF,align_blast]
    \\ FULL_SIMP_TAC std_ss [n2w_and_3])
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zLISP_def,SEP_CLAUSES]
    \\ SIMP_TAC (std_ss++star_ss) [] \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_REFL,lemma2])
  val th = MP th lemma
  in th end;

val (mc_lisp_r_elim_spec,mc_lisp_r_elim_def) = basic_decompile_strings x64_tools "mc_lisp_r_elim"
  (SOME (``(r1:word64,r2:word64,r7:word64,df:word64 set,f:word64->word32)``,
         ``(r1:word64,r2:word64,r7:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
      mov [r7-112],r1
      mov r1d,1
      mov r2,r1`);

val mc_lisp_r_elim_blast = blastLib.BBLAST_PROVE
  ``(w2w ((w2w (w >>> 32)):word32) << 32 !! w2w ((w2w (w:word64)):word32) = w) /\
    ((63 >< 32) w = (w2w (w >>> 32)):word32) /\ ((31 >< 0) w = (w2w w):word32)``;

val X64_LISP_R_ELIM = let
  val th = SPEC_FRAME_RULE mc_lisp_r_elim_spec
    ``zR 0x0w tw0 * zR 0x3w wsp *
      zR 0x6w bp * zR 0x8w (w2w w0) * zR 0x9w (w2w w1) *
      zR 0xAw (w2w w2) * zR 0xBw (w2w w3) * zR 0xCw (w2w w4) *
      zR 0xDw (w2w w5) * zR 0xEw wi * zR 0xFw we * zSTACK rbp qs *
      zBYTE_MEMORY dg g * zCODE_MEMORY ddd dd d * zIO (EL 0 cs,EL 1 cs,EL 2 cs,r1) io *
      zCODE_UNCHANGED cu dd d *
      cond
        (lisp_inv ^STATINV (x0,x1,x2,x3,x4,x5,^VAR_REST)
           (w0,w1,w2,w3,w4,w5,df,f,dg,g,bp,bp2,wsp,wi,we,tw0,tw1,tw2,sp,
            ds,sa1,sa2,sa3,dd,d))``
  val th = Q.INST [`r7`|->`sp`,`r1`|->`r1`,`r2`|->`EL 1 cs`] th
  val post = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND,STAR_ASSOC] \\ STRIP_TAC
    \\ SIMP_TAC std_ss [zIO_R_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [mc_lisp_r_elim_def]
    \\ IMP_RES_TAC lisp_inv_cs_read
    \\ IMP_RES_TAC lisp_inv_ds_read
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ ASM_SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_EXISTS_THM,SEP_CLAUSES,cond_STAR,zLISP_def]
    \\ FULL_SIMP_TAC std_ss [mc_lisp_r_elim_blast]
    \\ IMP_RES_TAC (DISCH_ALL (el 2 (CONJUNCTS (UNDISCH lisp_inv_ds_write))))
    \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `r1`)
    \\ IMP_RES_TAC (GEN_ALL lisp_inv_ignore_tw2)
    \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `1w`)
    \\ REPEAT STRIP_TAC \\ AUTO_EXISTS_TAC \\ ASM_SIMP_TAC std_ss []
    \\ `EL 0 (UPDATE_NTH 0 r1 ds) = r1` by
      (FULL_SIMP_TAC std_ss [lisp_inv_def]
       \\ Cases_on `ds` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
       \\ ASM_SIMP_TAC std_ss [UPDATE_NTH_def,EL,HD])
    \\ `tw1 = 1w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = Q.INST [`r1`|->`ioi`] th
  val th = foldr (uncurry Q.GEN) th [`tw0`,`tw1`,`tw2`,`wsp`,`bp`,`sp`,`w0`,`w1`,`w2`,`w3`,`w4`,`w5`,`wi`,`we`,`df`,`f`,`dg`,`g`,`bp2`,`ds`,`sa1`,`sa2`,`sa3`,`dd`,`d`,`ioi`]
  val th = SIMP_RULE std_ss [SPEC_PRE_EXISTS] th
  val pre = ``zLISP_R ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val lemma2 = prove(
    ``mc_lisp_r_elim_pre (ioi,EL 1 cs,sp,df,f) /\ ^LISP = ^LISP``,
    REPEAT STRIP_TAC \\ EQ_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [mc_lisp_r_elim_def]
    \\ IMP_RES_TAC lisp_inv_cs_read
    \\ IMP_RES_TAC lisp_inv_ds_read
    \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
    \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,LET_DEF,align_blast]
    \\ FULL_SIMP_TAC std_ss [n2w_and_3])
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zLISP_R_def,SEP_CLAUSES,zIO_R_def]
    \\ SIMP_TAC (std_ss++star_ss) [] \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_REFL,lemma2])
  val th = MP th lemma
  in th end;


(* test for EOF *)

val X64_LISP_TEST_EOF = save_lisp_thm("X64_LISP_TEST_EOF",let
  val th = Q.INST [`x`|->`EL 0 cs`,
                   `r2`|->`EL 1 cs`,
                   `y`|->`EL 2 cs`] mc_test_eof_spec
  val imp = SIMP_RULE std_ss [LET_DEF] mc_test_eof_thm
  val def = zLISP_R_def
  val pre_tm = ``zLISP_R ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_R ^STAT (
           LISP_TEST (FST (is_eof (getINPUT io))),x1,x2,x3,x4,x5,xs,xs1,
           IO_INPUT_APPLY (SND o is_eof) io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  val res = SPEC_COMPOSE_RULE [X64_LISP_R_INTRO,res,X64_LISP_R_ELIM]
  in res end);


(* next token *)

val next_token1_def = Define `next_token1 s = FST (FST (next_token s))`;
val next_token2_def = Define `next_token2 s = SND (FST (next_token s))`;

val X64_LISP_NEXT_TOKEN = save_lisp_thm("X64_LISP_NEXT_TOKEN",let
  (* part 1 *)
  val th = SPEC_FRAME_RULE mc_next_token_spec
     ``zR 0x3w wsp * zR 0x6w bp * zR 0xCw (w2w w4) * zR 0xDw (w2w w5) * zR 0xEw wi *
       zCODE_MEMORY ddd dd d * zSTACK rbp qs *
       zCODE_UNCHANGED cu dd d *
       cond (lisp_inv ^STATINV (x0,x1,x2,x3,x4,x5,^VAR_REST)
            (w0,w1,w2,w3,w4,w5,df,f,dg,g,bp,bp2,wsp,wi,we,tw0,tw1,tw2,
             sp,ds,sa1,sa2,sa3,dd,d))``
  val th = Q.INST [`r7`|->`sp`,`r15`|->`we`,`r2`|->`EL 1 cs`,`x`|->`EL 0 cs`,`y`|->`EL 2 cs`] th
  val post = set_pc th ``SEP_EXISTS io1 ok1 zX z0 z1. zLISP_R ^STAT (if ok1 then z0 else zX,if ok1 then z1 else Sym "NIL",Sym "NIL",
                           Sym "NIL",x4,x5,xs,xs1,io1,xbp,qs,code,amnt,ok) * zPC p * ~zS * cond (if ok1 then FST (next_token (getINPUT io)) = (z0,z1) else isVal zX) * cond (ok1 ==> (IO_INPUT_APPLY (SND o next_token) io = io1))``
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND,STAR_ASSOC] \\ STRIP_TAC
    \\ IMP_RES_TAC mc_next_token_thm \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ IMP_RES_TAC lisp_inv_ignore_io \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `IO_INPUT_APPLY (SND o next_token) io`)
    \\ ASM_SIMP_TAC std_ss [LET_DEF,zLISP_R_def]
    \\ ASM_SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_EXISTS_THM,SEP_CLAUSES,cond_STAR]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`io2`,`ok1`,`zX`,`z0`,`z1`]
    \\ ASM_SIMP_TAC std_ss []
    \\ AUTO_EXISTS_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ METIS_TAC [lisp_inv_ignore_io])
  val th = MP th lemma
  val th = foldr (uncurry Q.GEN) th [`tw0`,`tw1`,`tw2`,`wsp`,`bp`,`sp`,`w0`,`w1`,`w2`,`w3`,`w4`,`w5`,`wi`,`we`,`df`,`f`,`dg`,`g`,`bp2`,`ds`,`sa1`,`sa2`,`sa3`,`dd`,`d`]
  val th = SIMP_RULE std_ss [SPEC_PRE_EXISTS] th
  val pre = ``zLISP_R ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val lemma2 = prove(
    ``mc_next_token_pre (sp,we,io,dg,g,df,f) /\ ^LISP = ^LISP``,
    REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ IMP_RES_TAC mc_next_token_thm \\ ASM_SIMP_TAC std_ss [LET_DEF])
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zLISP_R_def,SEP_CLAUSES]
    \\ SIMP_TAC (std_ss++star_ss) [] \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_REFL,lemma2]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [cond_STAR]
    \\ AUTO_EXISTS_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ Q.LIST_EXISTS_TAC [`x`,`tw0`,`w2w w3`,`w2w w1`,`w2w w0`,`w2w w2`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [X64_LISP_R_INTRO,th]
  val (_,_,_,q) = dest_spec (concl th)
  val lemma = prove(
    (subst [mk_var("qq",type_of q)|->q] o set_pc th)
    ``SEP_IMP qq (zLISP_R ^STAT
           (next_token1 (getINPUT io),next_token2 (getINPUT io),Sym "NIL",Sym "NIL",x4,x5,xs,xs1,IO_INPUT_APPLY (SND o next_token) io,xbp,qs,code,amnt,ok) *
          zPC p * ~zS * cond ~(next_token2 (getINPUT io) = Sym "NIL") \/
         SEP_EXISTS z0 io.
           zLISP_R ^STAT
           (z0,Sym "NIL",Sym "NIL",Sym "NIL",x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS)``,
    SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,SEP_DISJ_def,cond_STAR]
    \\ REPEAT STRIP_TAC \\ REVERSE (Cases_on `ok1`)
    THEN1 (DISJ2_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [next_token2_def,next_token1_def]
    \\ Cases_on `z1 = Sym "NIL"` \\ ASM_SIMP_TAC std_ss []
    \\ METIS_TAC [])
  val part1 = MATCH_MP (MATCH_MP SPEC_WEAKEN th) lemma
  (* part 2 *)
  val code =
  (assemble "x64" `
      cmp r9,3
      jne SKIP
      mov [r7-112],r1
      mov r1d,1
      mov r2,r1
      mov r2,r8
      shr r2,2
      jmp [r7-200]
  SKIP: `);
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (el 1 code)
  val ((th2a,_,_),th2c) = spec (el 2 code)
  fun the (SOME x) = x | the _ = fail();
  val (th2b,_,_) = the th2c
  val ((th3,_,_),_) = spec (el 6 code)
  val ((th4,_,_),_) = spec (el 7 code)
  (* path A *)
  val thA = SPEC_COMPOSE_RULE [th1,th2a]
  val thA = HIDE_STATUS_RULE true sts thA
  val imp = prove(
    ``^LISP ==> ~(x1 = Sym "NIL") ==> ~(w2w w1 = 3w:word64) /\ ^LISP``,
    SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] THEN1
     (IMP_RES_TAC lisp_inv_swap1 \\ IMP_RES_TAC (hd (CONJUNCTS lisp_inv_Sym))
      \\ FULL_SIMP_TAC std_ss [])
    \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ METIS_TAC []) |> SIMP_RULE std_ss [LET_DEF]
  val th = RW [precond_def] (Q.INST [`r8`|->`w2w (v:word32)`,`r9`|->`w2w (w:word32)`,`rip`|->`p`] thA)
  val pre_tm = ``zLISP_R ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_R ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val def = zLISP_R_def
  val thA = prove_spec th imp def pre_tm post_tm
  (* path B *)
  val thB = SPEC_COMPOSE_RULE [th1,th2b]
  val thB = HIDE_STATUS_RULE true sts thB
  val imp = prove(
    ``^LISP ==> (x1 = Sym "NIL") ==> (w2w w1 = 3w:word64) /\ ^LISP``,
    SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] THEN1
     (IMP_RES_TAC lisp_inv_swap1 \\ IMP_RES_TAC (hd (CONJUNCTS lisp_inv_Sym))
      \\ FULL_SIMP_TAC std_ss [])
    \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ METIS_TAC []) |> SIMP_RULE std_ss [LET_DEF]
  val th = RW [precond_def] (Q.INST [`r8`|->`w2w (v:word32)`,`r9`|->`w2w (w:word32)`,`rip`|->`p`] thB)
  val pre_tm = ``zLISP_R ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_R ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val def = zLISP_R_def
  val thB = prove_spec th imp def pre_tm post_tm
  val thB = SPEC_COMPOSE_RULE [thB,X64_LISP_R_ELIM]
  val th = SPEC_COMPOSE_RULE [th3,th4]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] (Q.INST [`r8`|->`w2w (v:word32)`,`r9`|->`w2w (w:word32)`,`rip`|->`p`] th)
  val imp = prove(
    ``^LISP ==> let tw2 = w2w w0 >>> 2 in ^LISP``,
    SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ METIS_TAC []) |> SIMP_RULE std_ss [LET_DEF]
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val def = zLISP_def
  val th = prove_spec th imp def pre_tm post_tm
  val thB = SPEC_COMPOSE_RULE [thB,th,X64_LISP_ERROR]
  val thB = RW [SEP_CLAUSES] (Q.INST [`x1`|->`Sym "NIL"`,`x2`|->`Sym "NIL"`,`x3`|->`Sym "NIL"`,`x0`|->`z0`] thB)
  val thB = foldr (uncurry Q.GEN) thB [`z0`,`io`]
  val thB = SIMP_RULE std_ss [SPEC_PRE_EXISTS] thB
  (* path A \/ B *)
  val SPEC_BASIC_MERGE = RW [SEP_CLAUSES,GSYM AND_IMP_INTRO]
         (GEN_ALL (Q.SPECL [`x`,`p1`,`p2`,`c1`,`SEP_F`] SPEC_MERGE))
  val th = remove_primes (MATCH_MP (MATCH_MP SPEC_BASIC_MERGE thA) thB)
  val set_lemma = prove(
    ``({} UNION s = s) /\ ((x INSERT s) UNION (x INSERT t) = x INSERT (s UNION t))``,
    SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  val part2 = RW [set_lemma] th
  (* part1 and part2 *)
  val imp = RW[GSYM AND_IMP_INTRO](RW1[CONJ_COMM]SPEC_COMPOSE)
  val th = MATCH_MP (MATCH_MP imp part2) part1
  val th = SIMP_RULE std_ss [INSERT_UNION_EQ,UNION_EMPTY,word_arith_lemma1] th
  val th = SPEC_COMPOSE_RULE [th,X64_LISP_R_ELIM]
  in th end);


(* xbp related ops *)

val X64_LISP_XBP_SET = let
  val th = mc_xbp_set_spec
  val imp = SIMP_RULE std_ss [LET_DEF] mc_xbp_set_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,LENGTH xs,qs,code,amnt,ok) * zPC p``
  val res = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_XBP_SET",res) end;

val X64_LISP_XBP_LOAD = let
  val th = mc_xbp_load_spec
  val imp = SIMP_RULE std_ss [LET_DEF] mc_xbp_load_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,EL (LENGTH xs + getVal x1 - xbp) xs,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val res = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_XBP_LOAD",res) end;

val X64_LISP_XBP_STORE = let
  val th = mc_xbp_store_spec
  val imp = SIMP_RULE std_ss [LET_DEF] mc_xbp_store_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,UPDATE_NTH (LENGTH xs + getVal x1 - xbp) x0 xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val res = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_XBP_STORE",res) end;


(* load const amnt *)

val X64_LISP_LOAD_AMNT = let
  val th = mc_load_amnt_spec
  val imp = SIMP_RULE std_ss [LET_DEF] mc_load_amnt_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,Val amnt,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_LOAD_AMNT",res) end;


(* pops by a var *)

val X64_LISP_POPS_BY_VAR = let
  val th = mc_pops_by_var_spec
  val imp = SIMP_RULE std_ss [LET_DEF] mc_pops_by_var_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,DROP (getVal x1) xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_POPS_BY_VAR",res) end;


(* read SND code *)

val X64_LISP_READ_SND_CODE = let
  val th  = mc_read_snd_code_spec
  val imp = mc_read_snd_code_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (Val (code_ptr code),x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_READ_SND_CODE",res) end;


(* const load *)

val X64_LISP_CONST_LOAD = let
  val th  = mc_const_load_spec
  val imp = mc_const_load_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP ^STAT (EL (getVal x0) xs1,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val res = prove_spec th imp def pre_tm post_tm
  in save_lisp_thm("X64_LISP_CONST_LOAD",res) end;


(* const store *)

val imp4x = prove(
  ``^LISP ==> (sp - 0x6Cw && 0x3w = 0x0w) /\ (sp - 0x70w && 0x3w = 0x0w) /\
              (sp - 0x64w && 0x3w = 0x0w) /\ (sp - 0x68w && 0x3w = 0x0w) /\
              (sp - 0x5Cw && 0x3w = 0x0w) /\ (sp - 0x60w && 0x3w = 0x0w) /\
              (sp - 0x54w && 0x3w = 0x0w) /\ (sp - 0x58w && 0x3w = 0x0w) /\
              (sp - 0x4Cw && 0x3w = 0x0w) /\ (sp - 0x50w && 0x3w = 0x0w) /\
              (sp - 0x44w && 0x3w = 0x0w) /\ (sp - 0x48w && 0x3w = 0x0w) /\
              (sp - 0x3Cw && 0x3w = 0x0w) /\ (sp - 0x40w && 0x3w = 0x0w) /\
              (sp - 0x34w && 0x3w = 0x0w) /\ (sp - 0x38w && 0x3w = 0x0w) /\
              (sp - 0x2Cw && 0x3w = 0x0w) /\ (sp - 0x30w && 0x3w = 0x0w) /\
              (sp - 0x24w && 0x3w = 0x0w) /\ (sp - 0x28w && 0x3w = 0x0w)``,
  SIMP_TAC std_ss [lisp_inv_def] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3]) |> UNDISCH

fun X64_LISP_LOAD_EL i = let
  val addr = "mov r2,[r7-" ^ int_to_string (112 - 8 * i) ^ "]"
  val ((th,_,_),_) = x64_spec (x64_encodeLib.x64_encode addr)
  val th = Q.INST [`rip`|->`p`] th
  val th = RW [INSERT_SUBSET,EMPTY_SUBSET] th
  val tm = subst [``i:num``|->numSyntax.term_of_int i] ``(EL i ds):word64``
  val imp0 = UNDISCH (INST [``temp:word64``|->tm] lisp_inv_ignore_tw2)
  val imp1 = el (3*i+1) (CONJUNCTS (UNDISCH lisp_inv_ds_read))
  val imp2 = el (3*i+2) (CONJUNCTS (UNDISCH lisp_inv_ds_read))
  val imp3 = el (3*i+3) (CONJUNCTS (UNDISCH lisp_inv_ds_read))
  val imp = DISCH_ALL (LIST_CONJ [imp0,imp1,imp2,imp3,imp4x])
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. tw2 = ^tm) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val res = prove_spec th imp def pre_tm post_tm
  in res end;

val const_store_test_lemma = prove(
  ``SPEC X64_MODEL
     (zLISP_ALT b1 ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * p) c1 q1 ==>
    SPEC X64_MODEL
     (zLISP_ALT b2 ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * p) c2 q2 ==>
    SPEC X64_MODEL
     (zLISP_ALT (\wsp wi we ds tw2. b1 wsp wi we ds tw2 \/ b2 wsp wi we ds tw2)
        ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * p) (c1 UNION c2) (q1 \/ q2)``,
  SIMP_TAC (std_ss++sep_cond_ss) [zLISP_def,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS,
     SPEC_MOVE_COND,zLISP_ALT_def] \\ METIS_TAC [SPEC_MERGE_LEMMA]);

val X64_LISP_TEST_R2_EQ_ZERO = let
  val branch_taken_prefix = "3E"
  val x1 = x64_encodeLib.x64_encode "test r2,r2"
  val x2 = branch_taken_prefix ^ (x64_encodeLib.x64_encode "jne 12")
  val x3 = x64_encodeLib.x64_encode "mov r2d,12"
  val x4 = x64_encodeLib.x64_encode "jmp [r7-200]"
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec x1
  val ((th2,_,_),th2a) = spec x2
  val ((th3,_,_),_) = spec x3
  fun the (SOME x) = x | the _ = fail();
  val (th2b,_,_) = the th2a
  val th = SPEC_COMPOSE_RULE [th1,th2b,th3]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] th
  val def = zLISP_ALT_def
  val imp = Q.INST [`temp`|->`12w`] lisp_inv_ignore_tw2
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ((tw2 = EL 7 ds) /\ (tw2 = 0w))) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post1_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val post1_tm = subst [``rip:word64`` |-> cdr tm] post1_tm
  val result2 = prove_spec th imp def pre_tm post_tm
  val res2 = RW [GSYM zLISP_raw] result2
  val res2 = SPEC_COMPOSE_RULE [res2,X64_LISP_ERROR]
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] th
  val def = zLISP_ALT_def
  val imp = lisp_inv_swap0
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ((tw2 = EL 7 ds) /\ ~(tw2 = 0w))) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (~(EL 7 ds = 0w))) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val res1 = prove_spec th imp def pre_tm post_tm
  val th = MATCH_MP const_store_test_lemma (RW [GSYM STAR_ASSOC] res1)
  val th = MATCH_MP th (RW [GSYM STAR_ASSOC] res2)
  val set_lemma = prove(
    ``{x1;x2} UNION {x1;x2;x3;x4} = {x1;x2;x3;x4}``,
    SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  val th = RW [STAR_ASSOC,set_lemma] th
  val lemma = prove(``(\wsp wi we ds tw2.
                        (tw2 = EL 7 ds) /\ tw2 <> 0x0w \/
                        (tw2 = EL 7 ds) /\ (tw2 = 0x0w)) =
                      (\wsp wi we ds tw2. (tw2 = EL 7 ds))``, METIS_TAC [])
  val th = SIMP_RULE std_ss [markerTheory.Abbrev_def,lemma] th
  in th end;

val X64_LISP_CONST_STORE = let
  val th  = mc_const_store_spec
  val imp = mc_const_store_thm
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. ~(EL 7 ds = 0x0w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (Val (LENGTH xs1),x1,x2,x3,x4,x5,xs,xs1 ++ [x0],io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  val res = RW [GSYM zLISP_raw] res
  val th1 = X64_LISP_LOAD_EL 7 |> RW [GSYM zLISP_raw]
  val th2 = X64_LISP_TEST_R2_EQ_ZERO
  val th3 = res
  val res = SPEC_COMPOSE_RULE [th1,th2,th3]
  in save_lisp_thm("X64_LISP_CONST_STORE",res) end;


(* check for space in code heap *)

val X64_LISP_CODE_TEST = let
  val stack_test_code =
    (codegenLib.assemble "x64" `
       cmp QWORD [r7-88],256
       mov r2d,3
       ja L
       jmp [r7-200]
    L: `)
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (el 1 stack_test_code)
  val ((th2,_,_),_) = spec (el 2 stack_test_code)
  val ((th3,_,_),th3a) = spec (el 3 stack_test_code)
  fun the (SOME x) = x | the _ = fail();
  val (th3b,_,_) = the th3a
  val th = SPEC_COMPOSE_RULE [th1,th2,th3b]
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [precond_def] th
  val def = zLISP_ALT_def
  val imp = mc_code_heap_space_thm
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val th = RW [GSYM WORD_LOWER_OR_EQ] th
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (EL 3 ds <=+ 0x100w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev (EL 3 ds <=+ 0x100w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post1_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val post1_tm = subst [``rip:word64`` |-> cdr tm] post1_tm
  val result2 = prove_spec th imp def pre_tm post_tm
  val (th,goal) = SPEC_WEAKEN_RULE result2 post1_tm
  val lemma = prove(goal,SIMP_TAC std_ss [GSYM STAR_ASSOC,SEP_IMP_zLISP_ALT_zLISP])
  val res2 = SPEC_COMPOSE_RULE [MP th lemma,X64_LISP_ERROR]
  val th = SPEC_COMPOSE_RULE [th1,th2,th3]
  val th = HIDE_STATUS_RULE true sts th
  val lemma = GSYM (SIMP_CONV std_ss [WORD_LOWER_OR_EQ] ``~(x <=+ y:'a word)``)
  val th = RW [precond_def,lemma] th
  val def = zLISP_ALT_def
  val imp = mc_code_heap_space_thm
  val lemma = METIS_PROVE [] ``cond b = cond (Abbrev b)``
  val th = RW1 [lemma] (SIMP_RULE (std_ss++sep_cond_ss) [] th)
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ~(EL 3 ds <=+ 0x100w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. Abbrev ~(EL 3 ds <=+ 0x100w)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val tm = find_term (can (match_term ``zPC (p + n2w n)``)) (concl th)
  val post_tm = subst [``rip:word64`` |-> cdr tm] post_tm
  val res1 = prove_spec th imp def pre_tm post_tm
  val th = MATCH_MP push_lemma (RW [GSYM STAR_ASSOC] res1)
  val th = MATCH_MP th (RW [GSYM STAR_ASSOC] res2)
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [markerTheory.Abbrev_def])) th
  val set_lemma = prove(
    ``{x1;x2;x3} UNION {x1;x2;x3;x4} = {x1;x2;x3;x4}``,
    SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  val th = RW [STAR_ASSOC,set_lemma] th
  val th = RW [WORD_NOT_LOWER_EQUAL] th
  in th end;


(* code heap - write *)

val code_write_counter = ref 0;

fun X64_LISP_WRITE save (th,imp) = let
  val th = Q.INST [`dg`|->`dd`,`g`|->`d`] th
  val imp = SIMP_RULE std_ss [LET_DEF] imp
  val s = [``ddd:bool option``|->``SOME F``,``cu:((bool[64] -> bool) # (bool[64] -> bool[8])) option``|->``NONE:((bool[64] -> bool) # (bool[64] -> bool[8])) option``]
  val NEWSTAT = subst s STAT
  val def = RW [zCODE_MEMORY_def,SEP_CLAUSES,zCODE_UNCHANGED_def] (INST s (SPEC_ALL zLISP_ALT_def))
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. 0x100w <+ EL 3 ds) ^NEWSTAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. T) ^NEWSTAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val code = find_term (can (match_term LISP)) (imp |> concl |> cdr)
  val (s,_) = match_term LISP code
  val post_tm = subst s post_tm
  val res = prove_spec th imp def pre_tm post_tm
  val res = UNDISCH_ALL (RW [SPEC_MOVE_COND] res)
  val th2 = Q.INST [`ddd`|->`SOME F`,`cu`|->`NONE`] X64_LISP_CODE_TEST
  val th = MATCH_MP (MATCH_MP SPEC_DISJ_COMPOSE res) (RW [markerTheory.Abbrev_def] th2)
  val th = SIMP_RULE std_ss [INSERT_UNION_EQ,UNION_EMPTY,word_arith_lemma1] th
  val th = RW [GSYM zLISP_raw] th
  val th = RW [GSYM SPEC_MOVE_COND] (DISCH_ALL th)
  val name = "X64_LISP_WRITE_" ^ int_to_string (!code_write_counter)
  val _ = (code_write_counter := !code_write_counter+1)
  val _ = if save then save_lisp_thm(name,th) else th
  in th end;

val (X64_LISP_WRITE_THMS,iLOAD_LEMMA,iSTORE_LEMMA) = let
  val xs = CONJUNCTS lisp_inv_write_consts_thm
  fun fsts (x::y::xs) = x::fsts xs | fsts _ = []
  fun snds (x::y::xs) = y::snds xs | snds _ = []
  val xs = zip (fsts xs) (snds xs)
  fun is_iSTORE (x,y) = can (find_term (aconv ``iSTORE``)) (concl y)
  fun is_iLOAD (x,y) = can (find_term (aconv ``iLOAD``)) (concl y)
  val ys = filter (fn x => not (is_iSTORE x) andalso not (is_iLOAD x)) xs
  in (map (X64_LISP_WRITE true) ys,
      X64_LISP_WRITE false (first is_iLOAD xs),
      X64_LISP_WRITE false (first is_iSTORE xs)) end;

val lisp_inv_load_test = prove(
  ``^LISP ==>
    isVal x0 /\ getVal x0 < 536870912 ==>
    (let tw2 = 0x80000001w in ^LISP) /\
    w2w w0 <+ 0x80000001w:word64``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [LET_DEF]
  THEN1 (MATCH_MP_TAC lisp_inv_ignore_tw2 \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,isVal_thm,EVERY_DEF,lisp_x_def]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,isVal_thm,EVERY_DEF,lisp_x_def]
  \\ Q.PAT_X_ASSUM `s0 = bbb` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt]
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [getVal_def]
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `w2w (n2w a) << 2 + 0x1w = w0` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (std_ss++SIZES_ss) [w2w_def,WORD_MUL_LSL,word_mul_n2w,
       word_add_n2w,word_lo_n2w,w2n_n2w]
  \\ `a < 1073741824` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `(4 * a + 1) < 4294967296` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `(4 * a + 1) < 18446744073709551616` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ DECIDE_TAC) |> SIMP_RULE std_ss [LET_DEF];

val lisp_inv_load_test_nop = prove(
  ``^LISP ==>
    isVal x0 /\ ~(getVal x0 < 536870912) ==>
    (let tw2 = 0x80000001w in ^LISP) /\
    ~(w2w w0 <+ 0x80000001w:word64)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [LET_DEF]
  THEN1 (MATCH_MP_TAC lisp_inv_ignore_tw2 \\ ASM_SIMP_TAC std_ss [])
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,isVal_thm,EVERY_DEF,lisp_x_def]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,isVal_thm,EVERY_DEF,lisp_x_def]
  \\ Q.PAT_X_ASSUM `s0 = bbb` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt]
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [getVal_def]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC
  \\ Q.PAT_X_ASSUM `w2w (n2w a) << 2 + 0x1w = w0` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (std_ss++SIZES_ss) [w2w_def,WORD_MUL_LSL,word_mul_n2w,
       word_add_n2w,word_lo_n2w,w2n_n2w]
  \\ `a < 1073741824` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `(4 * a + 1) < 4294967296` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `(4 * a + 1) < 18446744073709551616` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ DECIDE_TAC) |> SIMP_RULE std_ss [LET_DEF];

val SPEC_MERGE_LEMMA2 = prove(
  ``SPEC m (p * cond g * cond b) c1 q1 ==>
    SPEC m (p * cond g * cond ~b) c2 q2 ==>
    SPEC m (p * cond g) (c1 UNION c2) (q1 * cond g * cond b \/ q2)``,
  Cases_on `b` \\ Cases_on `g` \\ SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]
  \\ METIS_TAC [SPEC_ADD_CODE,SEP_IMP_LEMMA,SPEC_WEAKEN,UNION_COMM]);

val X64_LISP_LOAD_TEST = let
  val add_code =
    (codegenLib.assemble "x64" `
       mov r2,2147483649
       cmp r8d,r2d
       jb L
       jmp [r7-200]
    L: `)
  val (spec,_,sts,_) = x64_tools
  val ((th1,_,_),_) = spec (el 1 add_code)
  val ((th2,_,_),_) = spec (el 2 add_code)
  val ((th3,_,_),th3a) = spec (el 3 add_code)
  fun the (SOME x) = x | the _ = fail();
  val (th3b,_,_) = the th3a
  val th = SPEC_COMPOSE_RULE [th1,th2,th3]
  val th = HIDE_STATUS_RULE true sts th
  val th = Q.INST [`r8`|->`w2w (a:word32)`] th
  val th = RW [select_twice,EVAL ``(31 -- 0) 0x80000001w:word64``] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_w2w,GSYM NOT_LESS,precond_def] th
  val imp = lisp_inv_load_test
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val def = zLISP_def
  val res1 = prove_spec th imp def pre_tm post_tm
  val th = SPEC_COMPOSE_RULE [th1,th2,th3b]
  val th = HIDE_STATUS_RULE true sts th
  val th = Q.INST [`r8`|->`w2w (a:word32)`] th
  val th = RW [select_twice,EVAL ``(31 -- 0) 0x80000001w:word64``] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_w2w,precond_def] th
  val imp = lisp_inv_load_test_nop
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC rip * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  val res2 = SPEC_COMPOSE_RULE [res,X64_LISP_ERROR]
  val lemma = prove(``cond b * cond c = cond (b /\ c)``,SIMP_TAC std_ss [SEP_CLAUSES])
  val res1 = RW [GSYM lemma, STAR_ASSOC] res1
  val res2 = RW [GSYM lemma, STAR_ASSOC] res2
  val set_lemma = prove(
    ``{x1;x2;x3} UNION {x1;x2;x3;x4} = {x1;x2;x3;x4}``,
    SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  val res = MATCH_MP (MATCH_MP SPEC_MERGE_LEMMA2 res1) res2
  val res = RW [STAR_ASSOC] (RW [set_lemma,lemma,GSYM STAR_ASSOC] res)
  in res end;

val X64_LISP_WRITE_iLOAD = save_lisp_thm("X64_LISP_WRITE_iLOAD",
  SPEC_COMPOSE_RULE [Q.INST [`ddd`|->`SOME F`,`cu`|->`NONE`] X64_LISP_LOAD_TEST,iLOAD_LEMMA]);

val X64_LISP_WRITE_iSTORE = save_lisp_thm("X64_LISP_WRITE_iSTORE",
  SPEC_COMPOSE_RULE [Q.INST [`ddd`|->`SOME F`,`cu`|->`NONE`] X64_LISP_LOAD_TEST,iSTORE_LEMMA]);


(* call generated code *)

val X64_LISP_JUMP_R2 = let
  val s = x64_encode "jmp r2"
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th = Q.INST [`rip`|->`p`] th
  val imp = lisp_inv_swap0
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. tw2 = r2) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC r2``
  val res = prove_spec th imp def pre_tm post_tm
  val res = RW [GSYM zLISP_raw] res
  in res end;

val X64_LISP_JUMP_TO_EL4CS_R2 = let
  val th  = mc_calc_addr_spec
  val imp = SIMP_RULE std_ss [LET_DEF] mc_calc_addr_thm
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. tw2 = EL 4 cs + n2w (getVal x2)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  val res = RW [GSYM zLISP_raw] res
  val res = SPEC_COMPOSE_RULE [res,Q.INST [`r2`|->`EL 4 cs + n2w (getVal x2)`] X64_LISP_JUMP_R2]
  in res end;

fun X64_LISP_PUSH_EL i = let
  val addr = "mov r2,[r7-" ^ int_to_string (192 - 8 * i) ^ "]"
  val ((th,_,_),_) = x64_spec (x64_encodeLib.x64_encode addr)
  val th = Q.INST [`rip`|->`p`] th
  val th = RW [INSERT_SUBSET,EMPTY_SUBSET] th
  val tm = subst [``i:num``|->numSyntax.term_of_int i] ``(EL i cs):word64``
  val imp0 = UNDISCH (INST [``temp:word64``|->tm] lisp_inv_ignore_tw2)
  val imp1 = el (3*i+10+3) (CONJUNCTS (UNDISCH lisp_inv_cs_read))
  val imp2 = el (3*i+11+3) (CONJUNCTS (UNDISCH lisp_inv_cs_read))
  val imp3 = el (3*i+12+3) (CONJUNCTS (UNDISCH lisp_inv_cs_read))
  val imp = DISCH_ALL (LIST_CONJ [imp0,imp1,imp2,imp3,imp4])
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. tw2 = ^tm) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val res = prove_spec th imp def pre_tm post_tm
  val res = SPEC_COMPOSE_RULE [res,Q.INST [`r2`|->`^tm`] X64_LISP_PUSH_R2]
  val res = RW [GSYM zLISP_raw] res
  in res end;

val pattern = ``(p1,xs1,b1) INSERT (p2:word64,xs2:word8 list,b2:bool) INSERT s``
fun sort_swap_conv tm = let
  val m = fst (match_term pattern tm)
  val p1 = subst m (mk_var("p1",``:word64``))
  val p2 = subst m (mk_var("p2",``:word64``))
  fun foo tm = if is_var tm then 0 else tm |> cdr |> cdr |> numSyntax.int_of_term
  val _ = foo p2 < foo p1 orelse fail()
  val (x1,s1) = pred_setSyntax.dest_insert tm
  val (x2,s2) = pred_setSyntax.dest_insert s1
  in ISPECL [x1,x2,s2] INSERT_COMM end

fun SORT_CODE th = CONV_RULE (REDEPTH_CONV sort_swap_conv) th

val X64_LISP_JUMP_TO_CODE_FOR_EVAL = save_thm("X64_LISP_JUMP_TO_CODE_FOR_EVAL",let
  val i = 4
  val addr = "mov r2,[r7-" ^ int_to_string (192 - 8 * i) ^ "]"
  val code = assemble "x64" `
    jmp L
G:  mov r2,[r7-160]
    push r2
    mov r2,r10
    shr r2,2
    add r2,[r7-160]
    jmp r2
L:  jmp G`
  val s = hd code
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec s
  val th0 = Q.INST [`rip`|->`p`] th
  val th1 = X64_LISP_PUSH_EL 4
  val th2 = X64_LISP_JUMP_TO_EL4CS_R2
  val call = Q.INST [`imm32`|->`0w - 0x20w`] X64_LISP_CALL_IMM
             |> SIMP_RULE (std_ss++SIZES_ss) [word_arith_lemma2,word_2comp_n2w]
  val tm = find_term (can (match_term ``n2w (m + n)``)) (concl call)
  val call_thm = RW [EVAL tm] call
  val res = SPEC_COMPOSE_RULE [th0,call_thm,th1,th2]
  val (_,_,c,_) = dest_spec (concl res)
  val f = EVAL
          THENC ONCE_REWRITE_CONV [GSYM n2w_mod]
          THENC SIMP_CONV (std_ss++SIZES_ss) []
  val res = SORT_CODE (RW [f c] res)
  in res end);

val X64_LISP_JUMP_TO_CODE_NO_RET = let
  val th  = mc_calc_addr_spec
  val imp = SIMP_RULE std_ss [LET_DEF] mc_calc_addr_thm
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. tw2 = EL 4 cs + n2w (getVal x2)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  val res = RW [GSYM zLISP_raw] res
  val res = SPEC_COMPOSE_RULE [res,Q.INST [`r2`|->`EL 4 cs + n2w (getVal x2)`] X64_LISP_JUMP_R2]
  in save_thm("X64_LISP_JUMP_TO_CODE_NO_RET",res) end;

val X64_LISP_JUMP_TO_CODE = let
  val th  = mc_calc_addr_spec
  val imp = SIMP_RULE std_ss [LET_DEF] mc_calc_addr_thm
  val def = zLISP_ALT_def
  val pre_tm = ``zLISP_ALT (\wsp wi we ds tw2. T) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP_ALT (\wsp wi we ds tw2. tw2 = EL 4 cs + n2w (getVal x2)) ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  val res = RW [GSYM zLISP_raw] res
  val res = SPEC_COMPOSE_RULE [res,Q.INST [`r2`|->`EL 4 cs + n2w (getVal x2)`] X64_LISP_CALL_R2]
  in save_thm("X64_LISP_JUMP_TO_CODE",res) end;


(* converting code into data *)

val PULL_FORALL_IMP = METIS_PROVE [] ``(Q ==> !x. P x) = (!x. Q ==> P x)``;

val zBYTE_MEMORY_Z_thm = prove(
  ``zBYTE_MEMORY dd d = zBYTE_MEMORY_Z dd d``,
  SIMP_TAC std_ss [zBYTE_MEMORY_Z_def,zBYTE_MEMORY_def]);

val X64_LISP_WEAKEN_CODE = store_thm("X64_LISP_WEAKEN_CODE",
  ``SPEC X64_MODEL
      (zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,cu) (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)) {}
      (zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,SOME F,cu) (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok))``,
  SIMP_TAC std_ss [zLISP_def]
  \\ REPEAT (HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC)
  \\ REPEAT (MATCH_MP_TAC (SIMP_RULE std_ss [PULL_FORALL_IMP] SPEC_FRAME))
  \\ REPEAT (MATCH_MP_TAC (RW1 [STAR_COMM] (SIMP_RULE std_ss [PULL_FORALL_IMP] SPEC_FRAME)))
  \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (SPEC_ALL SPEC_REFL))
  \\ SIMP_TAC std_ss [zCODE_MEMORY_def,zCODE_IMP_BYTE_MEMORY,zBYTE_MEMORY_Z_thm]);


(* converting data into code *)

val X64_LISP_STRENGTHEN_CODE = save_thm("X64_LISP_STRENGTHEN_CODE",let
  val ((th0,_,_),_) = x64_spec (x64_encode "mov r15, r3")
  val ((th1,_,_),_) = x64_spec (x64_encode "xor rax, rax")
  val th4 = RW [GSYM zR_def] (Q.INST [`rip`|->`p`,`df`|->`dd`,`f`|->`d`] X64_SPEC_CPUID)
  val ((th5,_,_),_) = x64_spec (x64_encode "mov r3, r15")
  val ((th6,_,_),_) = x64_spec (x64_encode "mov r15,[r7-240]")
  val ((th7,_,_),_) = x64_spec (x64_encode "add r15,r15")
  val ((th8,_,_),_) = x64_spec (x64_encode "mov r0d, 3")
  val ((th9,_,_),_) = x64_spec (x64_encode "mov r1d, 1")
  val th = SPEC_COMPOSE_RULE [th0,th1,th4,th5,th6,th7,th8,th9]
  val (spec,_,sts,_) = x64_tools
  val th = HIDE_STATUS_RULE true sts th
  val thi = RW [GSYM zCODE_MEMORY_def,GSYM zBYTE_MEMORY_Z_thm] th
  val PULL_EXISTS_CONJ = METIS_PROVE []  ``(?x. P x) /\ Q = ?x. P x /\ Q``
  val lemma = prove(
    ``^LISP ==>
      (let we = ((w2w (f (sp - 0xECw)) << 32 !! w2w (f (sp - 0xF0w))) +
                 (w2w (f (sp - 0xECw)) << 32 !! w2w (f (sp - 0xF0w)))) in
       let tw0 = 3w in let tw1 = 1w in let tw2 = ARB in ^LISP) /\
      {sp - 0xECw; sp - 0xF0w} SUBSET df /\ (sp - 0xECw && 0x3w = 0x0w) /\
      (sp - 0xF0w && 0x3w = 0x0w)``,
    SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC \\ IMP_RES_TAC lisp_inv_cs_read
    \\ ASM_SIMP_TAC std_ss [word_add_n2w,INSERT_SUBSET,EMPTY_SUBSET]
    \\ FULL_SIMP_TAC std_ss [lisp_inv_def,PULL_EXISTS_CONJ]
    \\ Q.LIST_EXISTS_TAC (map (fn tm => [ANTIQUOTE tm])
         (butlast (list_dest dest_exists (cdr (concl (SPEC_ALL lisp_inv_def))))))
    \\ FULL_SIMP_TAC std_ss [DECIDE ``2*e = e+e:num``]
    \\ Q.PAT_X_ASSUM `sp && 3w = 0w` MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ blastLib.BBLAST_TAC)
    |> SIMP_RULE std_ss [LET_DEF];
  val th  = Q.INST [`rip`|->`p`] thi
  val imp = lemma
  val def = zLISP_def
  val pre_tm = ``zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,SOME F,cu) (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,cu) (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in res end);



(* implementations of LISP_TEST *)

val X64_LISP_TEST = let
  fun the NONE = hd [] | the (SOME x) = x
  val ((th1,_,_),_) = x64_spec (x64_encode "mov r2d,11")
  val ((th2,_,_),th2a) = x64_spec (x64_encode "cmove r8,r2")
  val ((th3,_,_),th3a) = x64_spec (x64_encode "cmovne r8d,r0d")
  val (th2a,_,_) = the th2a
  val (th3a,_,_) = the th3a
  val pass1 = SPEC_COMPOSE_RULE [th1,th2,th3a]
  val pass2 = SPEC_COMPOSE_RULE [th1,th2a,th3]
  val th1 = SIMP_RULE (std_ss++sep_cond_ss) [precond_def] pass1
  val th2 = SIMP_RULE (std_ss++sep_cond_ss) [precond_def] pass2
  val th1 = RW [SEP_CLAUSES] (Q.INST [`z_zf`|->`T`,`rip`|->`p`] th1)
  val th2 = RW [SEP_CLAUSES] (Q.INST [`z_zf`|->`F`,`rip`|->`p`] th2)
  (* case 1 *)
  val th = th1
  val imp = SPEC_ALL (SIMP_RULE std_ss [LET_DEF] lisp_inv_T)
  val imp2 = Q.INST [`temp`|->`0xBw`] lisp_inv_ignore_tw2
  val imp = DISCH_ALL (MATCH_MP imp2 (UNDISCH imp))
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_ZF (SOME T)``
  val post_tm = set_pc th ``zLISP ^STAT (Sym "T",x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_ZF (SOME T)``
  val res1 = prove_spec th imp def pre_tm post_tm
  (* case 2 *)
  val th = th2
  val imp = SIMP_RULE std_ss [LET_DEF] lisp_inv_nil
  val imp2 = Q.INST [`temp`|->`0xBw`] lisp_inv_ignore_tw2
  val imp = DISCH_ALL (MATCH_MP imp2 (UNDISCH imp))
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_ZF (SOME F)``
  val post_tm = set_pc th ``zLISP ^STAT (Sym "NIL",x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_ZF (SOME F)``
  val res2 = prove_spec th imp def pre_tm post_tm
  (* combine *)
  val lemma = CONJ (GSYM (EVAL ``LISP_TEST F``)) (GSYM (EVAL ``LISP_TEST T``))
  val res1 = RW [lemma] res1
  val res2 = RW [lemma] res2
  val goal = subst [``T``|->``sf:bool``] (concl res1)
  val res = prove(goal,Cases_on `sf` THEN SIMP_TAC std_ss [res1,res2])
  in res end;

val X64_LISP_NOT_TEST = let
  fun the NONE = hd [] | the (SOME x) = x
  val ((th1,_,_),_) = x64_spec (x64_encode "mov r2d,11")
  val ((th2,_,_),th2a) = x64_spec (x64_encode "cmovne r8,r2")
  val ((th3,_,_),th3a) = x64_spec (x64_encode "cmove r8d,r0d")
  val (th2a,_,_) = the th2a
  val (th3a,_,_) = the th3a
  val pass1 = SPEC_COMPOSE_RULE [th1,th2,th3a]
  val pass2 = SPEC_COMPOSE_RULE [th1,th2a,th3]
  val th1 = SIMP_RULE (std_ss++sep_cond_ss) [precond_def] pass1
  val th2 = SIMP_RULE (std_ss++sep_cond_ss) [precond_def] pass2
  val th1 = RW [SEP_CLAUSES] (Q.INST [`z_zf`|->`F`,`rip`|->`p`] th1)
  val th2 = RW [SEP_CLAUSES] (Q.INST [`z_zf`|->`T`,`rip`|->`p`] th2)
  (* case 1 *)
  val th = th1
  val imp = SPEC_ALL (SIMP_RULE std_ss [LET_DEF] lisp_inv_T)
  val imp2 = Q.INST [`temp`|->`0xBw`] lisp_inv_ignore_tw2
  val imp = DISCH_ALL (MATCH_MP imp2 (UNDISCH imp))
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_ZF (SOME F)``
  val post_tm = set_pc th ``zLISP ^STAT (Sym "T",x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_ZF (SOME F)``
  val res1 = prove_spec th imp def pre_tm post_tm
  (* case 2 *)
  val th = th2
  val imp = SIMP_RULE std_ss [LET_DEF] lisp_inv_nil
  val imp2 = Q.INST [`temp`|->`0xBw`] lisp_inv_ignore_tw2
  val imp = DISCH_ALL (MATCH_MP imp2 (UNDISCH imp))
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_ZF (SOME T)``
  val post_tm = set_pc th ``zLISP ^STAT (Sym "NIL",x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_ZF (SOME T)``
  val res2 = prove_spec th imp def pre_tm post_tm
  (* combine *)
  val lemma = CONJ (GSYM (EVAL ``LISP_TEST ~F``)) (GSYM (EVAL ``LISP_TEST ~T``))
  val res1 = PURE_REWRITE_RULE [lemma] res1
  val res2 = PURE_REWRITE_RULE [lemma] res2
  val goal = subst [``T``|->``sf:bool``] (concl res2)
  val res = prove(goal,Cases_on `sf`
                       THEN ASSUME_TAC res1 THEN ASSUME_TAC res2
                       THEN FULL_SIMP_TAC std_ss [LISP_TEST_def])
  in res end;

val X64_LISP_TEST_CF = let
  fun the NONE = hd [] | the (SOME x) = x
  val ((th1,_,_),_) = x64_spec (x64_encode "mov r2d,11")
  val ((th2,_,_),th2a) = x64_spec (x64_encode "cmovb r8,r2")
  val ((th3,_,_),th3a) = x64_spec (x64_encode "cmovnb r8d,r0d")
  val (th2a,_,_) = the th2a
  val (th3a,_,_) = the th3a
  val pass1 = SPEC_COMPOSE_RULE [th1,th2,th3a]
  val pass2 = SPEC_COMPOSE_RULE [th1,th2a,th3]
  val th1 = SIMP_RULE (std_ss++sep_cond_ss) [precond_def] pass1
  val th2 = SIMP_RULE (std_ss++sep_cond_ss) [precond_def] pass2
  val th1 = RW [SEP_CLAUSES] (Q.INST [`z_cf`|->`T`,`rip`|->`p`] th1)
  val th2 = RW [SEP_CLAUSES] (Q.INST [`z_cf`|->`F`,`rip`|->`p`] th2)
  (* case 1 *)
  val th = th1
  val imp = SPEC_ALL (SIMP_RULE std_ss [LET_DEF] lisp_inv_T)
  val imp2 = Q.INST [`temp`|->`0xBw`] lisp_inv_ignore_tw2
  val imp = DISCH_ALL (MATCH_MP imp2 (UNDISCH imp))
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_CF (SOME T)``
  val post_tm = set_pc th ``zLISP ^STAT (Sym "T",x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_CF (SOME T)``
  val res1 = prove_spec th imp def pre_tm post_tm
  (* case 2 *)
  val th = th2
  val imp = SIMP_RULE std_ss [LET_DEF] lisp_inv_nil
  val imp2 = Q.INST [`temp`|->`0xBw`] lisp_inv_ignore_tw2
  val imp = DISCH_ALL (MATCH_MP imp2 (UNDISCH imp))
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_CF (SOME F)``
  val post_tm = set_pc th ``zLISP ^STAT (Sym "NIL",x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * zS1 Z_CF (SOME F)``
  val res2 = prove_spec th imp def pre_tm post_tm
  (* combine *)
  val lemma = CONJ (GSYM (EVAL ``LISP_TEST F``)) (GSYM (EVAL ``LISP_TEST T``))
  val res1 = RW [lemma] res1
  val res2 = RW [lemma] res2
  val goal = subst [``T``|->``cf:bool``] (concl res1)
  val res = prove(goal,Cases_on `cf` THEN SIMP_TAC std_ss [res1,res2])
  in res end;


(* prove a few theorems which imply that the bytecode does the right thing *)

val X64_POP0 = SPEC_COMPOSE_RULE [allowing_rebinds X64_LISP_TOP 0,X64_LISP_POP]
val X64_POP1 = SPEC_COMPOSE_RULE [allowing_rebinds X64_LISP_TOP 1,X64_LISP_POP]

val X64_LISP_SWAP1 = let
  val ((th,_,_),_) = x64_spec (x64_encode "xchg r8,r9")
  val th = Q.INST [`rip`|->`p`] th
  val imp = lisp_inv_swap1
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val post_tm = set_pc th ``zLISP ^STAT (x1,x0,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p``
  val res = prove_spec th imp def pre_tm post_tm
  in res end;

val X64_LISP_SYMBOL_LESS = let
  val th = mc_symbol_less_spec
  val imp = mc_symbol_less_thm
  val def = zLISP_def
  val pre_tm = ``zLISP ^STAT (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val post_tm = set_pc th ``zLISP ^STAT (LISP_SYMBOL_LESS x0 x1,Sym "NIL",Sym "NIL",Sym "NIL",x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) * zPC p * ~zS``
  val res = prove_spec th imp def pre_tm post_tm
  in res end;

fun BC_save name th = save_thm("X64_BYTECODE_" ^ name,th)

val _ = BC_save "POP" X64_POP0
val X64_LISP_SAFE_CAR = BC_save "CAR" (fetch "-" "X64_LISP_SAFE_CAR00")
val X64_LISP_SAFE_CDR = BC_save "CDR" (fetch "-" "X64_LISP_SAFE_CDR00")

val X64_CONSP = BC_save "CONSP" let
  val th = SPEC_COMPOSE_RULE [fetch "-" "X64_LISP_ISDOT0",X64_LISP_TEST]
  val th = RW [GSYM LISP_CONSP_def] th
  val (spec,_,sts,_) = x64_tools
  val th = HIDE_STATUS_RULE true sts th
  in th end;

val X64_NATP = BC_save "NATP" let
  val th = SPEC_COMPOSE_RULE [fetch "-" "X64_LISP_ISVAL0",X64_LISP_TEST]
  val th = RW [GSYM LISP_NUMBERP_def] th
  val (spec,_,sts,_) = x64_tools
  val th = HIDE_STATUS_RULE true sts th
  in th end;

val X64_SYMBOLP = BC_save "SYMBOLP" let
  val th = SPEC_COMPOSE_RULE [fetch "-" "X64_LISP_ISSYM0",X64_LISP_TEST]
  val th = RW [GSYM LISP_SYMBOLP_def] th
  val (spec,_,sts,_) = x64_tools
  val th = HIDE_STATUS_RULE true sts th
  in th end;

val X64_ATOMP = BC_save "ATOMP" let
  val th = SPEC_COMPOSE_RULE [fetch "-" "X64_LISP_ISDOT0",X64_LISP_NOT_TEST]
  val th = RW [GSYM LISP_ATOMP_def] th
  val (spec,_,sts,_) = x64_tools
  val th = HIDE_STATUS_RULE true sts th
  in th end;

val isVal_NFIX = prove(``!x. isVal (NFIX x) /\ (getVal (NFIX x) = getVal x)``, Cases \\ EVAL_TAC);
val isSym_SFIX = prove(``!x. isSym (SFIX x) /\ (getSym (SFIX x) = getSym x)``, Cases \\ EVAL_TAC);

val X64_ADD = BC_save "ADD" let
  val th0 = X64_POP1
  val th1 = fetch "-" "X64_LISP_NFIX_0"
  val th2 = fetch "-" "X64_LISP_NFIX_1"
  val th3 = X64_LISP_ADD
  val th = SPEC_COMPOSE_RULE [th0,th1,th2,th3]
  val th = RW [isVal_NFIX,isSym_SFIX,SEP_CLAUSES,LISP_ADD_def] th
  val th = RW1 [ADD_COMM] th
  val th = RW [GSYM LISP_ADD_def] th
  in th end;

val X64_SUB = BC_save "SUB" let
  val th0 = X64_LISP_SWAP1
  val th1 = X64_POP0
  val th2 = fetch "-" "X64_LISP_NFIX_0"
  val th3 = fetch "-" "X64_LISP_NFIX_1"
  val th4 = X64_LISP_SUB
  val th = SPEC_COMPOSE_RULE [th0,th1,th2,th3,th4]
  val th = RW [isVal_NFIX,isSym_SFIX,SEP_CLAUSES,LISP_SUB_def] th
  val th = RW [GSYM LISP_SUB_def] th
  in th end;

val X64_SYMBOL_LESS = BC_save "SYMBOL_LESS" let
  val th0 = X64_LISP_SWAP1
  val th1 = X64_POP0
  val th2 = fetch "-" "X64_LISP_SFIX_0"
  val th3 = fetch "-" "X64_LISP_SFIX_1"
  val th4 = X64_LISP_SYMBOL_LESS
  val th = SPEC_COMPOSE_RULE [th0,th1,th2,th3,th4]
  val th = RW [isVal_NFIX,isSym_SFIX,SEP_CLAUSES,LISP_SYMBOL_LESS_def] th
  val th = RW [GSYM LISP_SYMBOL_LESS_def] th
  in th end;

val X64_LESS = BC_save "LESS" let
  val th0 = X64_LISP_SWAP1
  val th1 = X64_POP0
  val th2 = fetch "-" "X64_LISP_NFIX_0"
  val th3 = fetch "-" "X64_LISP_NFIX_1"
  val th4 = X64_LISP_LESS
  val th5 = X64_LISP_TEST_CF
  val th = SPEC_COMPOSE_RULE [th0,th1,th2,th3,th4,th5]
  val th = RW [isVal_NFIX,isSym_SFIX,SEP_CLAUSES,LISP_LESS_def] th
  val th = RW [GSYM LISP_LESS_def] th
  in th end;

val X64_CONS = BC_save "CONS" let
  val th0 = X64_LISP_SWAP1
  val th1 = X64_POP0
  val th2 = fetch "-" "X64_LISP_CONS_01"
  val th = SPEC_COMPOSE_RULE [th0,th1,th2]
  val th = RW [isVal_NFIX,isSym_SFIX,SEP_CLAUSES,GSYM LISP_CONS_def] th
  in th end;

val X64_EQUAL = BC_save "EQUAL" let
  val th0 = X64_POP1
  val th1 = X64_LISP_EQUAL
  val th = SPEC_COMPOSE_RULE [th0,th1]
  in th end

val X64_POPS = BC_save "POPS" X64_LISP_POPS

val X64_LOAD = BC_save "LOAD"
  (SPEC_COMPOSE_RULE [fetch "-" "X64_LISP_PUSH_0",X64_LISP_LOAD])

val X64_STORE = BC_save "STORE"
  (SPEC_COMPOSE_RULE [X64_LISP_STORE,X64_POP0])

fun get_code th = let
  val (_,_,c,_) = dest_spec (concl th)
  fun dest_code_piece tm = let
    val (x,y) = pairSyntax.dest_pair tm
    val (y,z) = pairSyntax.dest_pair y
    val (v,n) = wordsSyntax.dest_word_add x handle HOL_ERR _ => (``n:num``,``(n2w 0):word64``)
    val _ = dest_var v
    val n = (numSyntax.int_of_term o cdr) n
    in (n,y) end
  val xs = map dest_code_piece (find_terms (can dest_code_piece) c)
  val xs = sort (fn (x,_) => fn (y,_) => x <= y) xs
  fun mk_appends [] = fail()
    | mk_appends [x] = snd x
    | mk_appends (x::xs) = listSyntax.mk_append(snd x,mk_appends xs)
  val cs = mk_appends xs |> QCONV (REWRITE_CONV [APPEND])
                         |> concl |> cdr
  in cs end;


val _ = print_compiler_grammar()
val _ = export_theory();
