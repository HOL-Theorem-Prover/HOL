(* This is demo / test file for new features of the pattern matcher.
   It's just a collection of tests and demos, nothing substantial.
   It is not even decently documented and not intended to make it
   back into the main branch. *)

val _ = new_theory "pattern_match_demo";

open Pmatch

fun Define_heu heu = with_heuristic heu Define

val Define_classic = Define_heu pheu_classic
val Define_f = Define_heu pheu_first_row
val Define_q = Define_heu pheu_constr_prefix
val Define_qba = Define_heu pheu_qba
val Define_cqba = Define_heu pheu_cqba

(* Turn of case-pretty printing in order to see the results properly *)
val _ = set_trace "pp_cases" 0


(* simple example from decideable_separation_logic *)

val DELETE_ELEMENT_def = Define
  `(DELETE_ELEMENT n [] = []) /\
   (DELETE_ELEMENT 0 (x::l) = l) /\
   (DELETE_ELEMENT (SUC n) (x::l) = x::DELETE_ELEMENT n l)`

(* old (classic result)

 |- (DELETE_ELEMENT 0 [] = []) /\
    (!v2. DELETE_ELEMENT (SUC v2) [] = []) /\
    (!x l. DELETE_ELEMENT 0 (x::l) = l) /\
    (!x n l. DELETE_ELEMENT (SUC n) (x::l) = x::DELETE_ELEMENT n l)

with Define, Define_q, Define_f

 |- (DELETE_ELEMENT n [] = []) /\
    (!x l. DELETE_ELEMENT 0 (x::l) = l) /\
    (!x n l. DELETE_ELEMENT (SUC n) (x::l) = x::DELETE_ELEMENT n l)

*)


(* Slightly more complex example form decidebale separation logic *)
val SWAP_ELEMENTS_def = Define `
   (SWAP_ELEMENTS _ 0 l = l) /\
   (SWAP_ELEMENTS _ _ [] = []) /\
   (SWAP_ELEMENTS _ _ [e] = [e]) /\
   (SWAP_ELEMENTS 0 (SUC n) (e1::e2::l) = ARB (* Something clever *) ) /\
   (SWAP_ELEMENTS (SUC m) (SUC n) (e::l) = e:: (SWAP_ELEMENTS m n l))`

term_size (concl SWAP_ELEMENTS_def)
(* old (classic result)

 |- (                SWAP_ELEMENTS 0        0         []              = []) /\
    (!v10.           SWAP_ELEMENTS 0        0         [v10]           = [v10]) /\
    (!v15 v14 v10.   SWAP_ELEMENTS 0        0         (v10::v14::v15) = v10::v14::v15) /\
    (!n.             SWAP_ELEMENTS (SUC n)  0         []              = []) /\
    (!v27 n.         SWAP_ELEMENTS (SUC n)  0         [v27]           = [v27]) /\
    (!v32 v31 v27 n. SWAP_ELEMENTS (SUC n)  0         (v27::v31::v32) = v27::v31::v32) /\
    (!v7.            SWAP_ELEMENTS 0        (SUC v7)  []              = []) /\
    (!v24 v2.        SWAP_ELEMENTS (SUC v2) (SUC v24) []              = []) /\
    (!v8 e.          SWAP_ELEMENTS 0        (SUC v8)  [e]             = [e]) /\
    (!v3 v25 e.      SWAP_ELEMENTS (SUC v3) (SUC v25) [e]             = [e]) /\
    (!n l e2 e1.     SWAP_ELEMENTS 0        (SUC n)   (e1::e2::l)     = ARB) /\
    (!v38 v37 n m e. SWAP_ELEMENTS (SUC m)  (SUC n)   (e::v37::v38)   = e::SWAP_ELEMENTS m n (v37::v38):
   thm

with Define_f

 |- (!l.             SWAP_ELEMENTS 0        0         l               = l) /\
    (!n l.           SWAP_ELEMENTS (SUC n)  0         l               = l) /\
    (!v7.            SWAP_ELEMENTS 0        (SUC v7)  []              = []) /\
    (!v2 v16.        SWAP_ELEMENTS (SUC v2) (SUC v16) []              = []) /\
    (!v8 e.          SWAP_ELEMENTS 0        (SUC v8)  [e]             = [e]) /\
    (!v3 v17 e.      SWAP_ELEMENTS (SUC v3) (SUC v17) [e]             = [e]) /\
    (!n l e2 e1.     SWAP_ELEMENTS 0        (SUC n)   (e1::e2::l)     = ARB) /\
    (!v22 v21 n m e. SWAP_ELEMENTS (SUC m)  (SUC n)   (e::v21::v22)   = e::SWAP_ELEMENTS m n (v21::v22):
   thm

with Define_q

 |- (!l.             SWAP_ELEMENTS 0        0         l               = l) /\
    (!n l.           SWAP_ELEMENTS (SUC n)  0         l               = l) /\
    (!x v4.          SWAP_ELEMENTS x        (SUC v4)  []              = []) /\
    (!x v5 e.        SWAP_ELEMENTS x        (SUC v5)  [e]             = [e]) /\
    (!n l e2 e1.     SWAP_ELEMENTS 0        (SUC n)   (e1::e2::l)     = ARB) /\
    (!v13 v12 n m e. SWAP_ELEMENTS (SUC m)  (SUC n)   (e::v12::v13)   = e::SWAP_ELEMENTS m n (v12::v13):
   thm


 |- (DELETE_ELEMENT n [] = []) /\
    (!x l. DELETE_ELEMENT 0 (x::l) = l) /\
    (!x n l. DELETE_ELEMENT (SUC n) (x::l) = x::DELETE_ELEMENT n l)

*)


val test_list_def = Define `
 test_list l = (case l of
       [_;     _; T; _;  _;    _] => 1
     | [_;     _; _;    _; F; _] => 2
     | [F; _; _;    _;     _; _] => 3
   )`;

val test_list_org_def = Define_classic `
 test_list_org l = (case l of
       [_;     _; T; _;  _;    _] => 1
     | [_;     _; _;    _; F; _] => 2
     | [F; _; _;    _;     _; _] => 3
   )`;

val test_pair_def = Define `
 (test_pair p = (case p of
       (_, _,      T, _,  _,   _) => 1
     | (_, _:bool, _, _:bool, F, _) => 2
     | (F, _, _,   _, _, _:bool) => 3
   ))`;


val test_pair_org_def = Define_classic `
 (test_pair_org p = (case p of
       (_, _,      T, _,  _,   _) => 1
     | (_, _:bool, _, _:bool, F, _) => 2
     | (F, _, _,   _, _, _:bool) => 3
   ))`;


val test_pair_qba_def = Define_qba `
 (test_pair_qba p = (case p of
       (_, _,      T, _,  _,   _) => 1
     | (_, _:bool, _, _:bool, F, _) => 2
     | (F, _, _,   _, _, _:bool) => 3
   ))`;


fun get_def thm = (rhs (snd (dest_forall (concl thm))))
fun def_size thm = term_size (get_def thm)


val x = def_size test_pair_qba_def   (* 37 *)
val x = def_size test_pair_def     (* 37 *)
val x = def_size test_pair_org_def (* 89 *)

(* Test runtime performance *)

(* generate input *)
local

fun all_bool_lists 0 = [``[]:bool list``]
  | all_bool_lists n =
    let
       val l = all_bool_lists (n - 1)
       fun my_cons n L = map (fn l => listSyntax.mk_cons (n,l)) L
    in
       (my_cons T l) @ (my_cons F l)
    end

fun all_bool_pairs 1 = [T, F]
  | all_bool_pairs n =
    let
       val l = all_bool_pairs (n - 1)
       fun my_cons n L = map (fn l => pairSyntax.mk_pair (n,l)) L
    in
       (my_cons T l) @ (my_cons F l)
    end

val input6 = all_bool_lists 6
val input5 = all_bool_lists 5
val input12 = all_bool_lists 12
val input2 = all_bool_lists 2

fun replicate 0 l = []
  | replicate n l = l @ (replicate (n-1) l)

val inputp6 = all_bool_pairs 6

in

val input_m = input5 @ input12 @ input6 @ input12 @ input6 @ input5 @ input2 @ input6

val input_6  = replicate 128 input6
val input_2  = replicate 1024 input2
val input_12 = replicate 1 input12

val inputp_6  = replicate 500 inputp6

end

(* run it *)

fun run_it input t = (time (map (fn l => EVAL (mk_comb (t, l)))) input; ())

val _ = run_it inputp_6 ``test_pair``;      (*  3.8 s *)
val _ = run_it inputp_6 ``test_pair_org``;  (*  4.6 s *)
val _ = run_it inputp_6 ``test_pair_qba``;  (*  4.3 s *)


val _ = export_theory();
