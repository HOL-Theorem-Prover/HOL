(* Interactive: 
  load "wordsLib";
  quietdec := true;
  open wordsLib arithmeticTheory;
  quietdec := false;
*)

open HolKernel Parse boolLib bossLib wordsLib 
     arithmeticTheory;

val _ = new_theory "Normal";

val C_def = Define `
    C e = \k. k e`;

val atom_def = Define `
    atom = \x.x`;

val C_ATOM_INTRO = Q.store_thm (
  "C_ATOM_INTRO",
  `!v. C v = C (atom v)`,
  SIMP_TAC std_ss [atom_def, C_def]
 );

val ATOM_ID = Q.store_thm (
   "ATOM_ID",
   `atom x = x`,
   SIMP_TAC std_ss [atom_def]
  );

val C_ATOM = Q.store_thm (
  "C_ATOM",
  `C (atom v) =
      \k. k v`,
  SIMP_TAC std_ss [C_def, atom_def]
 );

val C_INTRO = Q.store_thm (
  "C_INTRO",
  `!f. f = C f (\x.x)`,
  SIMP_TAC std_ss [C_def, LET_THM]
 );

val C_2_LET = Q.store_thm (
  "C_2_LET",
  `(C e k = let x = e in k x)`,
  SIMP_TAC std_ss [C_def, atom_def, LET_THM]
 );

(*---------------------------------------------------------------------------*)
(* Convert an expression to it continuation format                           *)
(* Theorems used for rewriting                                               *)	
(*---------------------------------------------------------------------------*)

val ABS_C_BINOP = Q.store_thm
("ABS_C_BINOP",
 `!f e1 e2. C (f e1 e2) = \k. C e1 (\x. C e2 (\y. C (f x y) k))`,
   SIMP_TAC std_ss [C_def, LET_THM]);

val C_BINOP = Q.store_thm (
  "C_BINOP",
   `(C (e1 + e2) =  \k. C e1 (\x. C e2 (\y. C (x + y) k))) /\
    (C (e1 - e2) =  \k. C e1 (\x. C e2 (\y. C (x - y) k))) /\
    (C (e1 * e2) =  \k. C e1 (\x. C e2 (\y. C (x * y) k))) /\
    (C (e1 ** e2) = \k. C e1 (\x. C e2 (\y. C (x ** y) k)))`,
   METIS_TAC [ABS_C_BINOP]
  );

val C_PAIR = Q.store_thm (
  "C_PAIR",
  `C (e1, e2) = \k. C e1 (\x. C e2 (\y. k (x,y)))`,
   RW_TAC std_ss [C_def]
  );

val C_WORDS = Q.store_thm (
  "C_WORDS",
  `!w1 w2 : 'a word.
    (C (w1 + w2)  = \k. C w1 (\x. C w2 (\y. C (x + y) k))) /\
    (C (w1 - w2)  = \k. C w1 (\x. C w2 (\y. C (x - y) k))) /\
    (C (w1 * w2)  = \k. C w1 (\x. C w2 (\y. C (x * y) k))) /\
    (C (w1 && w2) = \k. C w1 (\x. C w2 (\y. C (x && y) k))) /\
    (C (w1 ?? w2) = \k. C w1 (\x. C w2 (\y. C (x ?? y) k))) /\
    (C (w1 !! w2) = \k. C w1 (\x. C w2 (\y. C (x !! y) k))) /\
    (C (w1 < w2)  = \k. C w1 (\x. C w2 (\y. C (x < y) k))) /\
    (C (w1 <= w2) = \k. C w1 (\x. C w2 (\y. C (x <= y) k))) /\
    (C (w1 > w2)  = \k. C w1 (\x. C w2 (\y. C (x > y) k))) /\
    (C (w1 > w2)  = \k. C w1 (\x. C w2 (\y. C (x > y) k))) /\
    (C (w1 >> n)  = \k. C w1 (\x. C n (\y. C (x >> y) k))) /\
    (C (w1 >>> n) = \k. C w1 (\x. C n (\y. C (x >>> y) k))) /\
    (C (w1 << n)  = \k. C w1 (\x. C n (\y. C (x << y) k))) /\
    (C (w1 #>> n) = \k. C w1 (\x. C n (\y. C (x #>> y) k))) /\
    (C (w1 #<< n) = \k. C w1 (\x. C n (\y. C (x #<< y) k)))
`,
   METIS_TAC [ABS_C_BINOP]
  );

(*---------------------------------------------------------------------------*)
(* LET expressions are processed in a way that generates A-normal forms      *)
(*---------------------------------------------------------------------------*)

val C_LET = Q.store_thm (
  "C_LET",
  `C (let v = e in f v) = \k. C e (\x. C (f x) (\y. k y))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

(*---------------------------------------------------------------------------*)
(* For K-normal forms, use the following for LET expressions                 *)
(*---------------------------------------------------------------------------*)

val C_LET_K = Q.store_thm (
  "C_LET_K",
   `C (let v = e in f v) = \k. C e (\x. C x (\y. C (f y) (\z.k z)))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

val C_ABS = Q.store_thm (
  "C_ABS",
   `C (\v. f v) = C (\v. (C (f v) (\x. x)))`,
   RW_TAC std_ss [C_def, LET_THM]
  );

val C_APP = Q.store_thm (
  "C_APP",
   `C (f e) = \k. C f (\g. C e (\x. C (g x) (\y. k y)))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

val C_ATOM_COND = Q.store_thm (
  "C_ATOM_COND",
   `C (if cmpop c1 c2 then e1 else e2) = 
       \k. C c1 (\p. C c2 (\q.
         C (if cmpop p q then C e1 (\x.x) 
            else C e2 (\y.y)) (\z. k z)))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

(*
val C_COMPOUND_COND = Q.store_thm (
  "C_COMPOUND_COND",
   `C (if c1 /\ c2 then e1 else e2) = 
       \k. C c1 (\p. C c2 (\q. C e1 (\x. C e2 
           (\y. k (if p then 
                   if q then x else y
                   else y)))))`,
   RW_TAC std_ss [C_def, LET_THM] THEN
   METIS_TAC []
  );
*)


val BETA_REDUCTION = Q.store_thm (
   "BETA_REDUCTION",
   `(let x = atom y in f x) = f y`,
   SIMP_TAC std_ss [atom_def, LET_THM]
  );

val ELIM_USELESS_LET = Q.store_thm (
  "ELIM_USELESS_LET",
   `(let x = e1 in e2) = e2`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );

val FLATTEN_LET = Q.store_thm (
  "FLATTEN_LET",
   `(let x = (let y = e1 in e2 y) in e3 x) = 
    (let y = e1 in let x = e2 y in e3 x)`,
   SIMP_TAC std_ss [LET_THM]
  );


(* Conjunction in condtions *)
val AND_COND = Q.store_thm (
  "AND_COND",
  `(if c1 /\ c2 then e1 else e2) = 
     let x = e2 in
      (if c1 then 
         if c2 then e1 else x
       else x)`,
   RW_TAC std_ss [LET_THM] THEN
   METIS_TAC []
  );

(* Disjunction in condtions *)
val OR_COND = Q.store_thm (
  "OR_COND",
  `(if c1 \/ c2 then e1 else e2) = 
    let x = e1 in
      (if c1 then x else
       if c2 then x else e2)`,
   RW_TAC std_ss [LET_THM] THEN
   METIS_TAC []
  );

(* Normalize the conditions in branches *)
val BRANCH_NORM = Q.store_thm (
  "BRANCH_NORM",
  `((if (a:num) > b then x else y) = (if a <= b then y else x)) /\ 
    ((if a >= b then x else y) = (if b <= a then x else y)) /\
    ((if a < b then x else y) = (if b <= a then y else x))
  `,
   RW_TAC arith_ss [] THEN
   FULL_SIMP_TAC std_ss [GREATER_DEF, GREATER_EQ,NOT_LESS, NOT_LESS_EQUAL] THEN
   METIS_TAC [LESS_EQ_ANTISYM]
  );


(*---------------------------------------------------------------------------*)
(* Definitions used in inline.sml                                            *)
(*---------------------------------------------------------------------------*)

val fun_def = Define `
  fun = \x.x`;

val fun_ID = store_thm (
  "fun_ID",
  ``fun f = f``,
   SIMP_TAC std_ss [fun_def]
  );

val INLINE_EXPAND = store_thm (
  "INLINE_EXPAND",
  ``(let f = fun e1 in e2 f) = e2 e1``,
   SIMP_TAC std_ss [LET_THM, fun_def]
  );


(* Definitions and theorems used in closure.sml *)
(*---------------------------------------------------------------------------*)
(* Closure conversion                                                        *)
(* Eliminate nested function definitions                                     *)
(*---------------------------------------------------------------------------*)

val CLOSE_ONE = store_thm (
  "CLOSE_ONE",
  ``(let v = atom v in let f = fun (e1 v) in e2 f) = 
    let f = fun (\v. e1 v) in e2 (f v)``,
   SIMP_TAC std_ss [LET_THM, fun_def, atom_def]
  );

(*---------------------------------------------------------------------------*)
(* Eliminate administrative terms                                            *)
(*---------------------------------------------------------------------------*)

val LET_ATOM = store_thm (
  "LET_ATOM",
  ``(let x = atom x in f x) = f x``,
   SIMP_TAC std_ss [LET_THM, atom_def]
  );

val LET_FUN = store_thm (
  "LET_FUN",
  ``(let f = fun e1 in e2 f) = e2 e1``,
   SIMP_TAC std_ss [LET_THM, fun_def]
  );


val TOP_LEVEL_ABS = store_thm (
  "TOP_LEVEL",
  ``(\x. let f = fun e1 in e2 f) = (let f = fun e1 in (\x. e2 f))``,
   SIMP_TAC std_ss [LET_THM]
  );

val TOP_LEVEL_LET = store_thm (
  "TOP_LEVEL_LET",
  ``(let v = e1 in let f = fun e2 in e3 v f) = 
    (let f = fun e2 in let v = e1 in e3 v f)``,
   SIMP_TAC std_ss [LET_THM]
  );

val TOP_LEVEL_COND_1 = store_thm (
  "TOP_LEVEL_COND_1",
  ``(if e1 then let f = fun k1 in e2 f else e3) = 
        (let f = fun k1 in if e1 then e2 f else e3)``,
   SIMP_TAC std_ss [LET_THM]
  );

val TOP_LEVEL_COND_2 = store_thm (
  "TOP_LEVEL_COND_2",
  ``(if e1 then e2 else let f = fun k1 in e3 f) =
        (let f = fun k1 in if e1 then e2 else e3 f)``,
   SIMP_TAC std_ss [LET_THM]
  );


(* --------------------------------------------------------------------*)
(* Used in regAlloc.sml                                                *)
(* Administrative terms: save and loc                                  *)
(* --------------------------------------------------------------------*)

val save_def = Define `
  save = \x.x`;

val LET_SAVE = store_thm (
  "LET_SAVE",
  ``(let x = save y in f x) = f y``,
   SIMP_TAC std_ss [LET_THM, save_def]
  );

val loc_def = Define `
  loc = \x.x`;

val LET_LOC = store_thm (
  "LET_LOC",
  ``(let x = loc y in f x) = f y``,
   SIMP_TAC std_ss [LET_THM, loc_def]
  );


val _ = export_theory();
