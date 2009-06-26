
open HolKernel boolLib bossLib Parse;
open optionTheory wordsTheory listTheory;

val _ = new_theory "opmon";


(* operations over options *)

val option_orelse_def = Define `
  option_orelse f g x = 
    let m = f x in (if m = NONE then g x else m)`;

val option_then_def = Define `
  option_then f g x =  
    let m = f x in (if m = NONE then NONE else g (THE m))`;

val _ = overload_on ("++",Term`$option_orelse`); 
val _ = overload_on (">>",Term`$option_then`);

val option_fail_def = Define `option_fail = \x. NONE`;

val option_do_def = Define `
  (option_do [] = option_fail) /\
  (option_do [t] = t) /\
  (option_do (t1::t2::ts) = t1 >> option_do (t2::ts))`;

val option_try_def = Define `
  (option_try [] = option_fail) /\
  (option_try [t] = t) /\
  (option_try (t1::t2::ts) = option_orelse t1 (option_try (t2::ts)))`;

val option_apply_def = Define `
  option_apply x f = if x = NONE then NONE else f (THE x)`;

(* theorems *)

val option_apply_SOME = store_thm("option_apply_SOME",
  ``!x f. option_apply (SOME x) f = f x``,SRW_TAC [] [option_apply_def]);

val option_then_assoc = store_thm("option_then_assoc",
  ``!x y z. (x >> y) >> z = x >> (y >> z)``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_then_def,LET_DEF]  
  THEN REPEAT STRIP_TAC THEN Cases_on `x x'` THEN SRW_TAC [] []);

val option_orelse_assoc = store_thm("option_orelse_assoc",
  ``!x y z. option_orelse (option_orelse x y) z = 
            option_orelse x (option_orelse y z)``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_orelse_def,LET_DEF]  
  THEN REPEAT STRIP_TAC THEN Cases_on `x x'` THEN SRW_TAC [] []);

val option_orelse_SOME = store_thm("option_orelse_SOME",
  ``!f g h. 
      (option_orelse f g) >> SOME o k = option_orelse (f >> SOME o k) (g >> SOME o k)``,
  SIMP_TAC std_ss [FUN_EQ_THM,option_orelse_def,option_then_def,LET_DEF]  
  THEN REPEAT STRIP_TAC THEN Cases_on `f x`
  THEN ASM_SIMP_TAC std_ss []);

val option_then_OVER_orelse = store_thm("option_then_OVER_orelse",
  ``!x:'a -> 'b option y:'b -> 'c option g. 
      (option_orelse (x >> y) (x >> z) = x >> (option_orelse y z)) /\ 
      (option_orelse (option_orelse g (x >> y)) (x >> z) = option_orelse g (x >> (option_orelse y z))) /\ 
      (option_orelse (x >> y) (option_orelse (x >> z) g) = option_orelse (x >> (option_orelse y z)) g) /\ 
      (option_orelse h (option_orelse (x >> y) (option_orelse (x >> z) g)) = 
       option_orelse h (option_orelse (x >> (option_orelse y z)) g))``,
  REPEAT STRIP_TAC THEN `option_orelse (x >> y) (x >> z) = x >> (option_orelse y z)` by 
    (SIMP_TAC std_ss [FUN_EQ_THM,option_orelse_def,option_then_def,LET_DEF]  
     THEN REPEAT STRIP_TAC THEN Cases_on `x x'` THEN SRW_TAC [] [])
  THEN METIS_TAC [option_orelse_assoc]);

val pull_if_lemma = store_thm("pull_if_lemma",
  ``!b x y (f:'a->'b). (f (if b then x else y) = if b then f x else f y) /\
                       ((if b then h else k) z = if b then h z else (k:'c->'d) z)``,
  Cases THEN SIMP_TAC std_ss []);

val if_some_lemma = store_thm("if_some_lemma",
  ``!b x (y:'a) (z:'b). (if b then SOME (z,x) else SOME (z,y)) = SOME (z,if b then x else y)``,
  Cases THEN SIMP_TAC std_ss []);


val _ = export_theory ();
