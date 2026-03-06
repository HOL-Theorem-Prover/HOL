
Theory decoder
Ancestors
  opmon list string bit_list

(* -- define tokenise - a function which splits a string at white space and comma -- *)

Definition STR_SPLIT_AUX_def:
  (STR_SPLIT_AUX c [] curr = [IMPLODE (REVERSE curr)]) /\
  (STR_SPLIT_AUX c (x::xs) curr =
    if MEM x c then IMPLODE (REVERSE curr) :: STR_SPLIT_AUX c xs []
               else STR_SPLIT_AUX c xs (x::curr))
End

Definition STR_SPLIT_def:
  STR_SPLIT c s = STR_SPLIT_AUX c (EXPLODE s) []
End

Definition tokenise_def:
  tokenise s = FILTER (\x. ~(x = "")) (STR_SPLIT [#" ";#","] s)
End

(* EVAL ``tokenise "testing: A, B, C"`` gives ``["testing:"; "A"; "B"; "C"]`` *)


(* -- syntax matcher -- *)

Definition match_init_def:
  match_init = (\w:bool list. SOME ((\x:string.[]:bool list),w))
End

Definition match_def:
  match step s = option_do (MAP step s)
End

Definition match_list_def:
  match_list step pre res list =
    match_init >>
    option_try (MAP (\(x,y). match step (pre x) >> (res y)) list)
End

Definition match_list_raw_def:
  match_list_raw g step pre res list =
    (\w:bool list. SOME (g,w)) >>
    option_try (MAP (\(x,y). match step (pre x) >> (res y)) list)
End


(* -- operations over bit lists -- *)

Definition hex2bits_def:
  hex2bits = FOLDR $++ [] o MAP (\x. n2bits (4 * STRLEN x) (hex2num x)) o tokenise
End

Definition assign_def:
  assign name x (g:string->bool list, bits:bool list) = SOME ((name =+ x) g,bits)
End

Definition assign_drop_def:
  assign_drop name i (g:string->bool list, bits:bool list) =
    if LENGTH bits < i then NONE else SOME ((name =+ TAKE i bits) g, DROP i bits)
End

Definition drop_eq_def:
  drop_eq v (g:string->bool list, bits:bool list) =
    let i = LENGTH v in
      if LENGTH bits < i \/ ~(v = TAKE i bits) then NONE else SOME (g, DROP i bits)
End

Definition assert_def:
  assert p (g:string->bool list, bits:bool list) =
    if p g then SOME (g,bits) else NONE
End

Definition DT_def:
  (DT (g,[]) = NONE) /\
  (DT (g,F::b) = NONE) /\
  (DT (g,T::b) = SOME (g,b))
End

Definition DF_def:
  (DF (g,[]) = NONE) /\
  (DF (g,F::b) = SOME (g,b)) /\
  (DF (g,T::b) = NONE)
End


(* -- simplifying rules -- *)

Theorem drop_eq_thm:
    !xs. (drop_eq (T::xs) = DT >> drop_eq xs) /\
         (drop_eq (F::xs) = DF >> drop_eq xs) /\
         (drop_eq [] = SOME)
Proof
  REPEAT STRIP_TAC
  THEN SIMP_TAC bool_ss [FUN_EQ_THM] THEN Cases_on `x` THEN Cases_on `r`
  THEN SIMP_TAC std_ss [drop_eq_def,DT_def,DF_def,LET_DEF,LENGTH,option_then_def,DROP_0,TAKE_0]
  THEN Cases_on `h` THEN SIMP_TAC std_ss [drop_eq_def,DT_def,DF_def,
    LET_DEF,LENGTH,option_then_def,rich_listTheory.BUTFIRSTN,rich_listTheory.FIRSTN,CONS_11]
QED

val assert_option_then_lemma = prove(
  ``!p b. (assert (\g. T) >> p = p) /\
          (assert b >> DF = DF >> assert b) /\
          (assert b >> DT = DT >> assert b)``,
  REPEAT STRIP_TAC
  THEN SRW_TAC [] [option_then_def,assert_def,FUN_EQ_THM,LET_DEF,pairTheory.FORALL_PROD]
  THEN Cases_on `p_2` THEN SRW_TAC [] [DF_def,DT_def]
  THEN Cases_on `h` THEN FULL_SIMP_TAC std_ss [DF_def,DT_def,assert_def]);

Theorem assert_option_then_thm:
    !p q b. (assert (\g. T) >> p = p) /\
            (q >> assert (\g. T) >> p = q >> p) /\
            (assert b >> DF = DF >> assert b) /\
            (assert b >> DT = DT >> assert b) /\
            (p >> assert b >> DF = p >> DF >> assert b) /\
            (p >> assert b >> DT = p >> DT >> assert b)
Proof
  METIS_TAC [assert_option_then_lemma,option_then_assoc]
QED


(* -- for fast evaluation -- *)

Theorem DT_DF_then_orelse[compute]:
  ((DT >> p) (g,[]) = NONE) /\ ((DF >> p) (g,[]) = NONE) /\
  ((DT >> p) (g,F::b) = NONE) /\ ((DF >> p) (g,T::b) = NONE) /\
  ((DF >> p) (g,F::b) = p (g,b)) /\ ((DT >> p) (g,T::b) = p (g,b)) /\
  (((DT >> f) ++ p) (g,[]) = p (g,[])) /\ (((DF >> f) ++ p) (g,[]) = p (g,[])) /\
  (((DT >> f1) ++ (DF >> f2)) (g,F::b) = f2 (g,b)) /\
  (((DF >> f2) ++ (DT >> f1)) (g,F::b) = f2 (g,b)) /\
  (((DT >> f1) ++ (DF >> f2)) (g,T::b) = f1 (g,b)) /\
  (((DF >> f2) ++ (DT >> f1)) (g,T::b) = f1 (g,b)) /\
  (((DT >> f) ++ p) (g,F::b) = p (g,F::b)) /\
  (((DF >> f) ++ p) (g,T::b) = p (g,T::b))
Proof
  SIMP_TAC std_ss [DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF] >>
  METIS_TAC []
QED

val DT_over_DF_lemma = prove(
  ``((DT >> x) ++ ((DF >> y) ++ (DT >> z)) = (DT >> (x ++ z)) ++ (DF >> y)) /\
    ((DF >> x) ++ ((DT >> y) ++ (DF >> z)) = (DF >> (x ++ z)) ++ (DT >> y))``,
  REPEAT STRIP_TAC THEN (REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN Cases_on `r`
  THEN1 SIMP_TAC std_ss [DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF]
  THEN Cases_on `h`
  THEN SIMP_TAC std_ss [DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF]
  THEN METIS_TAC []));

Theorem DT_over_DF:
    ((DT >> x) ++ ((DF >> y) ++ ((DT >> z) ++ g)) = (DT >> (x ++ z)) ++ ((DF >> y) ++ g)) /\
    ((DF >> x) ++ ((DT >> y) ++ ((DF >> z) ++ g)) = (DF >> (x ++ z)) ++ ((DT >> y) ++ g)) /\
    ((DT >> x) ++ ((DF >> y) ++ (DT >> z)) = (DT >> (x ++ z)) ++ (DF >> y)) /\
    ((DF >> x) ++ ((DT >> y) ++ (DF >> z)) = (DF >> (x ++ z)) ++ (DT >> y))
Proof
  REWRITE_TAC [GSYM option_orelse_assoc,
    REWRITE_RULE [GSYM option_orelse_assoc] DT_over_DF_lemma]
QED

Definition DTF_def:
  (DTF p q (g,[])= NONE) /\
  (DTF p q (g,F::b) = q (g,b)) /\
  (DTF p q (g,T::b) = p (g,b))
End

Theorem DTF_THM:
    !x y. ((DF >> p) ++ (DT >> q) = DTF q p) /\ ((DT >> q) ++ (DF >> p) = DTF q p)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN Cases_on `r`
  THEN SIMP_TAC bool_ss [DTF_def,DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF]
  THEN Cases_on `h`
  THEN SIMP_TAC std_ss [DTF_def,DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF]
  THEN METIS_TAC []
QED

