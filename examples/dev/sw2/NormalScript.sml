(* Interactive:
  load "wordsLib";
  quietdec := true;
  open wordsLib arithmeticTheory;
  quietdec := false;
*)
Theory Normal  (* This name is misleading *)
Ancestors
  arithmetic
Libs
  wordsLib


(*---------------------------------------------------------------------------------*)
(* Theorems used for pre-processing, normalization, normal format optimization,    *)
(* inlining, closure conversion and register allocation.                           *)
(* To do: break them into several theories.                                        *)
(*---------------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------------*)
(* Preprocessing                                                                   *)
(*---------------------------------------------------------------------------------*)

(* Conjunction in condtions *)
Theorem AND_COND:
   (if c1 /\ c2 then e1 else e2) =
     let x = e2 in
      (if c1 then
         if c2 then e1 else x
       else x)
Proof
   RW_TAC std_ss [LET_THM] THEN
   METIS_TAC []
QED

(* Disjunction in condtions *)
Theorem OR_COND:
   (if c1 \/ c2 then e1 else e2) =
    let x = e1 in
      (if c1 then x else
       if c2 then x else e2)
Proof
   RW_TAC std_ss [LET_THM] THEN
   METIS_TAC []
QED

(* Normalize the conditions in branches *)
Theorem BRANCH_NORM:
   ((if (a:num) > b then x else y) = (if a <= b then y else x)) /\
    ((if a >= b then x else y) = (if a < b then y else x)) /\
    ((if aw > bw then xw else yw) = (if aw <= bw then yw else xw)) /\
    ((if aw >= bw then xw else yw) = (if aw < bw then yw else xw)) /\
    ((if aw >+ bw then xw else yw) = (if aw <=+ bw then yw else xw)) /\
    ((if aw >=+ bw then xw else yw) = (if aw <+ bw then yw else xw))
Proof
   RW_TAC arith_ss [wordsTheory.WORD_LO, wordsTheory.WORD_LS, wordsTheory.WORD_HI, wordsTheory.WORD_HS] THEN
   FULL_SIMP_TAC std_ss [GREATER_DEF, GREATER_EQ, NOT_LESS, NOT_LESS_EQUAL, wordsTheory.WORD_GREATER,
              wordsTheory.WORD_GREATER_EQ, wordsTheory.WORD_NOT_LESS_EQUAL] THEN
   METIS_TAC [LESS_EQ_ANTISYM, wordsTheory.WORD_LESS_EQ_ANTISYM]
QED

(*---------------------------------------------------------------------------------*)
(* Normalization: turn program into normal forms.                                  *)
(*---------------------------------------------------------------------------------*)

Definition C_def:
    C e = \k. k e
End

Definition atom_def:
    atom = \x.x
End

Theorem C_ATOM_INTRO:
   !v. C v = C (atom v)
Proof
  SIMP_TAC std_ss [atom_def, C_def]
QED

Theorem ATOM_ID:
    atom x = x
Proof
   SIMP_TAC std_ss [atom_def]
QED

Theorem C_ATOM:
   C (atom v) =
      \k. k v
Proof
  SIMP_TAC std_ss [C_def, atom_def]
QED

Theorem C_INTRO:
   !f. f = C f (\x.x)
Proof
  SIMP_TAC std_ss [C_def, LET_THM]
QED

Theorem C_2_LET:
   (C e k = let x = e in k x)
Proof
  SIMP_TAC std_ss [C_def, atom_def, LET_THM]
QED

(*---------------------------------------------------------------------------*)
(* Convert an expression to it continuation format                           *)
(* Theorems used for rewriting                                               *)
(*---------------------------------------------------------------------------*)

Theorem ABS_C_BINOP:
  !f e1 e2. C (f e1 e2) = \k. C e1 (\x. C e2 (\y. C (f x y) k))
Proof
   SIMP_TAC std_ss [C_def, LET_THM]
QED

Theorem C_BINOP:
    (C (e1 + e2) =  \k. C e1 (\x. C e2 (\y. C (x + y) k))) /\
    (C (e1 - e2) =  \k. C e1 (\x. C e2 (\y. C (x - y) k))) /\
    (C (e1 * e2) =  \k. C e1 (\x. C e2 (\y. C (x * y) k))) /\
    (C (e1 ** e2) = \k. C e1 (\x. C e2 (\y. C (x ** y) k)))
Proof
   METIS_TAC [ABS_C_BINOP]
QED

Theorem C_BINOP_SYM:
    (C (e1 + e2) =  \k. C e1 (\x. C e2 (\y. C (y + x) k))) /\
    (C (e1 - e2) =  \k. C e2 (\x. C e1 (\y. C (y - x) k))) /\
    (C (e1 * e2) =  \k. C e1 (\x. C e2 (\y. C (y * x) k))) /\
    (C (e1 ** e2) = \k. C e1 (\x. C e2 (\y. C (x ** y) k)))
Proof
   SIMP_TAC arith_ss [C_def, LET_THM]
QED

Theorem C_PAIR:
   C (e1, e2) = \k. C e1 (\x. C e2 (\y. k (x,y)))
Proof
   RW_TAC std_ss [C_def]
QED

Theorem C_WORDS_BINOP:
   !w1 w2 : 'a word.
    (C (w1 + w2)  = \k. C w1 (\x. C w2 (\y. C (x + y) k))) /\
    (C (w1 - w2)  = \k. C w1 (\x. C w2 (\y. C (x - y) k))) /\
    (C (w1 * w2)  = \k. C w1 (\x. C w2 (\y. C (x * y) k))) /\
    (C (w1 && w2) = \k. C w1 (\x. C w2 (\y. C (x && y) k))) /\
    (C (w1 ?? w2) = \k. C w1 (\x. C w2 (\y. C (x ?? y) k))) /\
    (C (w1 !! w2) = \k. C w1 (\x. C w2 (\y. C (x !! y) k))) /\

    (C (w1 < w2)  = \k. C w1 (\x. C w2 (\y. C (x < y) k))) /\
    (C (w1 <= w2) = \k. C w1 (\x. C w2 (\y. C (x <= y) k))) /\
    (C (w1 > w2)  = \k. C w2 (\x. C w1 (\y. C (x < y) k))) /\
    (C (w1 >= w2) = \k. C w2 (\x. C w1 (\y. C (x <= y) k))) /\
    (C (w1 <+ w2)  = \k. C w1 (\x. C w2 (\y. C (x <+ y) k))) /\
    (C (w1 <=+ w2) = \k. C w1 (\x. C w2 (\y. C (x <=+ y) k))) /\
    (C (w1 >+ w2)  = \k. C w2 (\x. C w1 (\y. C (x <+ y) k))) /\
    (C (w1 >=+ w2) = \k. C w2 (\x. C w1 (\y. C (x <=+ y) k))) /\

    (C (w1 >> n)  = \k. C w1 (\x. C n (\y. C (x >> y) k))) /\
    (C (w1 >>> n) = \k. C w1 (\x. C n (\y. C (x >>> y) k))) /\
    (C (w1 << n)  = \k. C w1 (\x. C n (\y. C (x << y) k))) /\
    (C (w1 #>> n) = \k. C w1 (\x. C n (\y. C (x #>> y) k))) /\
    (C (w1 #<< n) = \k. C w1 (\x. C n (\y. C (x #<< y) k)))
Proof
    SIMP_TAC arith_ss [C_def, LET_THM] THEN
    SIMP_TAC bool_ss [wordsTheory.WORD_GREATER, wordsTheory.WORD_GREATER_EQ,
      wordsTheory.WORD_HIGHER, wordsTheory.WORD_HIGHER_EQ]
QED

Definition rsb_def:   rsb x y = y - x
End

Theorem C_WORDS_BINOP_SYM:
   !w1 w2 : 'a word.
    (C (w1 + w2)  = \k. C w1 (\x. C w2 (\y. C (y + x) k))) /\
    (C (w1 - w2)  = \k. C w1 (\x. C w2 (\y. C (rsb y x) k))) /\
    (C (w1 * w2)  = \k. C w1 (\x. C w2 (\y. C (y * x) k))) /\
    (C (w1 && w2) = \k. C w1 (\x. C w2 (\y. C (y && x) k))) /\
    (C (w1 ?? w2) = \k. C w1 (\x. C w2 (\y. C (y ?? x) k))) /\
    (C (w1 !! w2) = \k. C w1 (\x. C w2 (\y. C (y !! x) k))) /\

    (C (w1 >> n)  = \k. C w1 (\x. C n (\y. C (x >> y) k))) /\
    (C (w1 >>> n) = \k. C w1 (\x. C n (\y. C (x >>> y) k))) /\
    (C (w1 << n)  = \k. C w1 (\x. C n (\y. C (x << y) k))) /\
    (C (w1 #>> n) = \k. C w1 (\x. C n (\y. C (x #>> y) k))) /\
    (C (w1 #<< n) = \k. C w1 (\x. C n (\y. C (x #<< y) k)))
Proof
   SIMP_TAC std_ss [C_def, LET_THM, rsb_def] THEN
   SIMP_TAC bool_ss [wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_MULT_COMM, wordsTheory.WORD_AND_COMM,
     wordsTheory.WORD_XOR_COMM, wordsTheory.WORD_OR_COMM, wordsTheory.WORD_GREATER, wordsTheory.WORD_GREATER_EQ,
     wordsTheory.WORD_HIGHER, wordsTheory.WORD_HIGHER_EQ]
QED

Theorem COND_SWAP:
    ((x : 'a word < y)  = (y > x)) /\
    ((x <= y)  = (y >= x)) /\
    ((x > y)  = (y < x)) /\
    ((x >= y)  = (y <= x)) /\
    ((x <+ y)  = (y >+ x)) /\
    ((x <=+ y) = (y >=+ x)) /\
    ((x >+ y)  = (y <+ x)) /\
    ((x >=+ y) = (y <=+ x))
Proof
    SIMP_TAC bool_ss [wordsTheory.WORD_GREATER, wordsTheory.WORD_GREATER_EQ,
      wordsTheory.WORD_HIGHER, wordsTheory.WORD_HIGHER_EQ]
QED

(*---------------------------------------------------------------------------*)
(* LET expressions are processed in a way that generates A-normal forms      *)
(*---------------------------------------------------------------------------*)

Theorem C_LET:
   C (let v = e in f v) = \k. C e (\x. C (f x) (\y. k y))
Proof
   SIMP_TAC std_ss [C_def, LET_THM]
QED

(*---------------------------------------------------------------------------*)
(* For K-normal forms, use the following for LET expressions                 *)
(*---------------------------------------------------------------------------*)

Theorem C_LET_K:
    C (let v = e in f v) = \k. C e (\x. C x (\y. C (f y) (\z.k z)))
Proof
   SIMP_TAC std_ss [C_def, LET_THM]
QED

Theorem C_ABS:
    C (\v. f v) = C (\v. (C (f v) (\x. x)))
Proof
   RW_TAC std_ss [C_def, LET_THM]
QED

(*
val C_APP = Q.store_thm (
  "C_APP",
   `C (f e) = \k. C f (\g. C e (\x. k (g x)))`,
   SIMP_TAC std_ss [C_def, LET_THM]
  );
*)

Theorem C_APP:
    C (f e) = \k. C f (\g. C e (\x. C (g x) (\y. k y)))
Proof
   SIMP_TAC std_ss [C_def, LET_THM]
QED

Theorem C_ATOM_COND:
    C (if cmpop c1 c2 then e1 else e2) =
       \k. C c1 (\p. C c2 (\q.
         C (if cmpop p q then C e1 (\x.x)
            else C e2 (\y.y)) (\z. k z)))
Proof
   SIMP_TAC std_ss [C_def, LET_THM]
QED

Theorem C_ATOM_COND_EX:
    C (if cmpop c1 c2 then e1 else e2) =
       \k. C c1 (\p. C c2 (\q.
         k (if cmpop p q then C e1 (\x.x)
            else C e2 (\y.y)
           )))
Proof
   SIMP_TAC std_ss [C_def, LET_THM]
QED

(*---------------------------------------------------------------------------------*)
(* Optimization of normal forms.                                                   *)
(*---------------------------------------------------------------------------------*)

Theorem BETA_REDUCTION:
    (let x = atom y in f x) = f y
Proof
   SIMP_TAC std_ss [atom_def, LET_THM]
QED

Theorem ELIM_USELESS_LET:
    (let x = e1 in e2) = e2
Proof
   SIMP_TAC std_ss [C_def, LET_THM]
QED

Theorem FLATTEN_LET:
    (let x = (let y = e1 in e2 y) in e3 x) =
    (let y = e1 in let x = e2 y in e3 x)
Proof
   SIMP_TAC std_ss [LET_THM]
QED

(*---------------------------------------------------------------------------*)
(* Definitions used in inline.sml                                            *)
(*---------------------------------------------------------------------------*)

Definition fun_def:
  fun = \x.x
End

Theorem fun_ID:
    fun f = f
Proof
   SIMP_TAC std_ss [fun_def]
QED

Theorem INLINE_EXPAND:
    (let f = fun e1 in e2 f) = e2 e1
Proof
   SIMP_TAC std_ss [LET_THM, fun_def]
QED


(* Definitions and theorems used in closure.sml *)
(*---------------------------------------------------------------------------*)
(* Closure conversion                                                        *)
(* Eliminate nested function definitions                                     *)
(*---------------------------------------------------------------------------*)

Theorem CLOSE_ONE:
    (let v = atom v in let f = fun (e1 v) in e2 f) =
    let f = fun (\v. e1 v) in e2 (f v)
Proof
   SIMP_TAC std_ss [LET_THM, fun_def, atom_def]
QED

(*---------------------------------------------------------------------------*)
(* Eliminate administrative terms                                            *)
(*---------------------------------------------------------------------------*)

Theorem LET_ATOM:
    (let x = atom y in f x) = f y
Proof
   SIMP_TAC std_ss [LET_THM, atom_def]
QED

Theorem LET_FUN:
    (let f = fun e1 in e2 f) = e2 e1
Proof
   SIMP_TAC std_ss [LET_THM, fun_def]
QED


Theorem TOP_LEVEL_ABS:
    (\x. let f = fun e1 in e2 f) = (let f = fun e1 in (\x. e2 f))
Proof
   SIMP_TAC std_ss [LET_THM]
QED

Theorem TOP_LEVEL_LET:
    (let v = e1 in let f = fun e2 in e3 v f) =
    (let f = fun e2 in let v = e1 in e3 v f)
Proof
   SIMP_TAC std_ss [LET_THM]
QED

Theorem TOP_LEVEL_COND_1:
    (if e1 then let f = fun k1 in e2 f else e3) =
        (let f = fun k1 in if e1 then e2 f else e3)
Proof
   SIMP_TAC std_ss [LET_THM]
QED

Theorem TOP_LEVEL_COND_2:
    (if e1 then e2 else let f = fun k1 in e3 f) =
        (let f = fun k1 in if e1 then e2 else e3 f)
Proof
   SIMP_TAC std_ss [LET_THM]
QED


(* --------------------------------------------------------------------*)
(* Used in regAlloc.sml                                                *)
(* Administrative terms: save and loc                                  *)
(* --------------------------------------------------------------------*)

Definition save_def:
  save = \x.x
End

Theorem LET_SAVE:
    (let x = save y in f x) = f y
Proof
   SIMP_TAC std_ss [LET_THM, save_def]
QED

Definition loc_def:
  loc = \x.x
End

Theorem LET_LOC:
    (let x = loc y in f x) = f y
Proof
   SIMP_TAC std_ss [LET_THM, loc_def]
QED

(* --------------------------------------------------------------------*)
