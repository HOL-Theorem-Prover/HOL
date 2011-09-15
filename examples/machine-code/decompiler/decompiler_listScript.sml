
open HolKernel boolLib bossLib Parse;
open progTheory set_sepTheory addressTheory prog_armTheory;
open listTheory pred_setTheory arithmeticTheory wordsTheory;
open helperLib decompilerLib;

val _ = new_theory "decompiler_list";


(* we define a separation logic-style linked-list assertion *)

val aLIST_def = Define `
  (aLIST a [] = cond (a = 0w)) /\
  (aLIST a (x::xs) = SEP_EXISTS b. cond (ALIGNED a) *
     cond ~(a = 0w) * aM a b * aM (a + 4w) x * aLIST b xs)`;


(* a few lemmas about list *)

val aLIST_NIL = prove(
  ``!s. (aLIST a xs) s ==> ((a = 0w) = (xs = []))``,
  Cases_on `xs` THEN SIMP_TAC std_ss [aLIST_def,SEP_EXISTS_THM,
    cond_STAR,GSYM STAR_ASSOC,NOT_CONS_NIL]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [cond_def])

val SPEC_SPLIT_LIST = prove(
  ``SPEC m (p * cond (~GUARD n (xs = []))) c (q xs) =
    SPEC m (p * cond (~GUARD n (xs = []))) c (q (HD xs :: TL xs))``,
  Cases_on `xs` THEN SIMP_TAC std_ss [SPEC_MOVE_COND,GUARD_def,HD,TL]);

val aLIST_NIL_INTRO = prove(
  ``!x. (x = []) ==> (aR a 0w = SEP_EXISTS b. aR a b * aLIST b x)``,
  SIMP_TAC std_ss [aLIST_def,FUN_EQ_THM,SEP_EXISTS_THM,cond_STAR]);


(* auxilliary functions *)

fun list_mk_sep_exists (vs,tm) = foldr mk_sep_exists tm vs
fun list_dest_sep_exists tm = let
  val vs = list_dest dest_sep_exists tm
  in (butlast vs, last vs) end;

fun standardise_var_names th = let
  val (_,p,_,q) = dest_spec (concl th)
  val (ps,p) = list_dest_sep_exists p
  val (qs,q) = list_dest_sep_exists q
  val pts = map dest_comb (find_terms (can (match_term ``aR x y``)) p)
  val qts = map dest_comb (find_terms (can (match_term ``aR x y``)) q)
  val s = map (fn (x,y) => snd (hd (filter (fn (z,_) => z = x) qts)) |-> y) pts
  fun foo [] = ALL_CONV
    | foo (x::xs) = RAND_CONV (ALPHA_CONV x THENC ABS_CONV (foo xs))
  val th = CONV_RULE (POST_CONV (foo (map (subst s) qs))) th
  val th = CONV_RULE (PRE_CONV SEP_EXISTS_AC_CONV THENC POST_CONV SEP_EXISTS_AC_CONV) th
  in th end;

fun ABBREV_aLIST th = let
  val _ = if hyp th = [] then () else fail()
  val (_,p,_,q) = dest_spec (concl th)
  val (_,p) = list_dest_sep_exists p
  val (_,q) = list_dest_sep_exists q
  val pts = map dest_comb (find_terms (can (match_term ``aLIST x y``)) p)
  val qts = map dest_comb (find_terms (can (match_term ``aLIST x y``)) q)
  val xs = map (fn (x,y) => (y,snd (hd (filter (fn (z,_) => z = x) qts)))) pts
  val xs = filter (fn (x,y) => not (x = y)) xs
  val ys = map (fn (x,y) => mk_eq(mk_var("s15@" ^ fst (dest_var x),type_of x),y)) xs
  val th = SIMP_RULE bool_ss (map (GSYM o ASSUME) ys) th
  in th end handle HOL_ERR _ => th;

fun INTRO_M th = let
  val g = find_term (can (match_term ``aMEMORY df f``))
  val f = cdr (g (car (concl th)))
  val th = RW [ALIGNED_INTRO] (DISCH_ALL (UNABBREV_ALL th))
  val (a,df) = pred_setSyntax.dest_in (find_term (pred_setSyntax.is_in) (concl th))
  val lm = SPEC_ALL (SPECL [a,f] aM_THM)
  val f2 = cdr (g (concl lm))
  val th = (SIMP_RULE std_ss [lm,IN_INSERT])
        (INST [f|->f2,df|->pred_setSyntax.mk_set[a]] th)
  val th = RW [GSYM SPEC_MOVE_COND,combinTheory.APPLY_UPDATE_THM] th
  val th = RW1 [SPEC_MOVE_COND_POST] th
  in th end handle HOL_ERR _ => th;


(* list specific help for decompiler *)

fun FINALISE_FUNC def = let
  val def = SIMP_RULE std_ss [LET_DEF] def
  val pat = ``p = if (xs:'b list) = [] then d else (k:'a)``
  val def = if not (can (match_term pat) (concl def)) then def else let
              val (b,_,_) = (dest_cond o snd o dest_eq o concl) def
              val v = (fst o dest_eq) b
              val ty = (hd o snd o dest_type o snd o dest_var) v
              val x = (implode o butlast o explode o fst o dest_var) v
              val xs = listSyntax.mk_cons(mk_var(x,ty),v)
              val th1 = INST [v |-> listSyntax.mk_nil ty] def
              val th2 = INST [v |-> xs] def
              in CONJ th1 th2 end
  val def = SIMP_RULE std_ss [LET_DEF,NOT_NIL_CONS,HD,TL] def
  val def = CONV_RULE (DEPTH_CONV FORCE_PBETA_CONV) def
  val def = SIMP_RULE std_ss [LET_DEF,NOT_NIL_CONS,HD,TL] def
  in def end;

fun SPEC_COMPOSE_PREPROCESS th = let
  val th = INTRO_M th
  val th = RW [cond_CONJ,STAR_ASSOC] th
  val th = if not (can (match_term ``x = 0w:word32``) (hd (hyp th)))
              handle Empty => true then th
           else let
             val th2 = UNABBREV_ALL th
             val lemma = SPEC (mk_var("s0@ys",``:word32 list``)) aLIST_NIL_INTRO
             val th2 = SIMP_RULE std_ss [UNDISCH lemma,SEP_CLAUSES] th2
             in th2 end
  in th end;

fun SPEC_COMPOSE_POSTPROCESS th = let
  val th = SEP_REWRITE_RULE [aLIST_NIL] th
  val th = SIMP_RULE std_ss [SEP_EXISTS_COND] th
  val th = SIMP_RULE std_ss [Once SPEC_SPLIT_LIST] th
  val th = SIMP_RULE std_ss [aLIST_def,SEP_CLAUSES,NOT_CONS_NIL,STAR_ASSOC] th
  in th end;

fun SPEC_COMPOSE_FINALISE th = let
  val rw = el 2 (CONJUNCTS (GSYM aLIST_def))
  val th = EXISTS_SEP_REWRITE_RULE rw th
  val th = HIDE_POST_RULE ``aR 0w`` th handle HOL_ERR _ => th
  val th = HIDE_PRE_RULE ``aR 0w`` th handle HOL_ERR _ => th
  val th = standardise_var_names th
  val th = ABBREV_aLIST th
  in th end;

fun shape_of_loop (th:thm) =
  RW [SEP_CLAUSES] (SPEC_FRAME_RULE (Q.SPECL [`emp`,`{}`] (ISPEC ``ARM_MODEL`` SPEC_REFL))
    ``SEP_EXISTS a b. aR 1w a * aLIST a xs * aR 2w b * aLIST b ys``)


(* we use add_modifier to make the decompiler 'smart' *)

val _ = add_modifier "pre" SPEC_COMPOSE_PREPROCESS;
val _ = add_modifier "post" SPEC_COMPOSE_POSTPROCESS;
val _ = add_modifier "spec" SPEC_COMPOSE_FINALISE;
val _ = add_modifier "func" FINALISE_FUNC;
val _ = add_modifier "shape 24" shape_of_loop;


(* now we can decompile the list reverse example in a smart way *)

val name = "rev"
val qcode = `
  E3A02000    (*   0      mov r2,#0          *)
  EA000003    (*   4      b L2               *)
  E5910000    (*   8  L1: ldr r0,[r1]        *)
  E5812000    (*  12      str r2,[r1]        *)
  E1A02001    (*  16      mov r2,r1          *)
  E1A01000    (*  20      mov r1,r0          *)
  E3510000    (*  24  L2: cmp r1,#0          *)
  1AFFFFF9    (*  28      bne L1             *)`
val (th,def) = decompile_arm "rev" qcode

val _ = save_thm("rev_def",def);
val _ = save_thm("rev_thm",th);

(*

val tools = arm_tools
open codegenLib;

assemble "arm" `
    mov r2,#0
    b L2
L1: ldr r0,[r1,#4]
    str r2,[r1,#4]
    mov r2,r1
    mov r1,r0
L2: cmp r1,#0
    bne L1
`

*)

val _ = export_theory();

