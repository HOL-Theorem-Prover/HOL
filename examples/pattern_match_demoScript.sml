(* This is demo / test file for new features of the pattern matcher.
   It's just a collection of tests and demos, nothing substantial. 
   It is not even decently documented and not intended to make it
   back into the main branch. *)

val _ = new_theory "pattern_match_demo";


fun Define_org q =
let
  val _ = Pmatch.choose_pat_col_fun := Pmatch.choose_pat_col___first_col 
  val _ = Pmatch.skip_irrelevant_pat_rows := false
in Define q
end

fun Define_new q =
let
  val _ = Pmatch.choose_pat_col_fun := Pmatch.choose_pat_col___first_non_var 
  val _ = Pmatch.skip_irrelevant_pat_rows := true
in Define q
end

fun Define_new_skip q =
let
  val _ = Pmatch.choose_pat_col_fun := Pmatch.choose_pat_col___first_col
  val _ = Pmatch.skip_irrelevant_pat_rows := true
in Define q
end


val test_org_def = Define_org `
 test_org l = (case l of
       [_;     _; T; _;  _;    _] => 1
     | [_;     _; _;    _; F; _] => 2
     | [F; _; _;    _;     _; _] => 3
   )`;

val test_org2_def = Define_new `
 test_org2 l = (case l of
       [_;     _; T; _;  _;    _] => 1
     | [_;     _; _;    _; F; _] => 2
     | [F; _; _;    _;     _; _] => 3
   )`;

val test_lem_def = Define_org `
 (test_lem l = (case l of [] => ARB | b::l0 => (case l0 of [] => ARB | _::l1 => (case l1 of [] => ARB | b1::l2 => (case b1 of  T => (case l2 of [] => ARB | _::l3 => (case l3 of [] => ARB | _::l4 => (case l4 of [] => ARB | _::l5 => (case l5 of [] => 1 | _::_ => ARB ) ) ) ) |  F => (case l2 of [] => ARB | _::l7 => (case l7 of [] => ARB | b7::l8 => (case b7 of  T => (case l8 of [] => ARB | _::l9 => (case l9 of [] => (case b of  T => ARB |  F => 3 ) | _::_ => ARB ) ) |  F => (case l8 of [] => ARB | _::l11 => (case l11 of [] => 2 | _::_ => ARB ) ) ) ) ) ) ) ) ))`;


(* A manual version *)
val test_man_def = Define_org `
 test_man l = case l of
    [] => ARB
  | [_] => ARB
  | [_;_] => ARB
  | [_;_;_] => ARB
  | [_;_;_;_] => ARB
  | [_;_;_;_;_] => ARB
  | [b1;_;b3;_;b5;_] => (if b3 then 1 else (if b5 then (if b1 then ARB else 3) else 2))
  | _ => ARB`

(* A second manual version *)
val test_man2_def = Define_org `
 test_man2 l = 
  if (LENGTH l = 6) then
    (if EL 2 l then 1 else (if EL 4 l then (if EL 0 l then ARB else 3) else 2))
  else ARB`


(* your original definition *)
val testp_org_def = Define_org `
 (testp_org p = (case p of
       (_, _,      T, _,  _,   _) => 1
     | (_, _:bool, _, _:bool, F, _) => 2
     | (F, _, _,   _, _, _:bool) => 3
   ))`;
(* result

val testp_org_def =
   |- !p.
     testp_org p =
     case p of
       (T,v2,T,v6,T,v9) => 1
     | (T,v2,T,v6,F,v9) => 1
     | (T,v2,F,v10,T,v13) => ARB
     | (T,v2,F,v10,F,v13) => 2
     | (F,v15,T,v19,T,v22) => 1
     | (F,v15,T,v19,F,v22) => 1
     | (F,v15,F,v23,T,v26) => 3
     | (F,v15,F,v23,F,v26) => 2:
   thm
*)

val testp_org2_def = Define_new `
 (testp_org2 p = (case p of
       (_, _,      T, _,  _,   _) => 1
     | (_, _:bool, _, _:bool, F, _) => 2
     | (F, _, _,   _, _, _:bool) => 3
   ))`;

(* Result

val testp_org2_def =
   |- !p.
     testp_org2 p =
     case p of
       (v,v2,T,v6,v8,v9) => 1
     | (T,v2,F,v10,T,v13) => ARB
     | (F,v2,F,v10,T,v13) => 3
     | (v,v2,F,v10,F,v13) => 2:
   thm
*)


val testp_lem_def = Define_org `
 (testp_lem p = (case p of (b:bool,_:bool,b0,_:bool,b1,_:bool) => (case b0 of  T => 1 |  F => (case b1 of  T => (case b of  T => ARB(*Incomplete Pattern at File "hol.lem", line 7, character 15 to line 11, character 6:*) |  F => 3 ) |  F => 2 ) ) ))`;

val testp_man_def = Define_org `
 (testp_man p = (case p of
       (b1:bool, _:bool, b3, bs) => if b3 then 1 else
     (case bs of (_:bool, F, _:bool) => 2
                 | _ => (if b1 then ARB else 3))))`


val testp_org3_def = Define_org `
 (testp_org3 p = (case p of
       (_, _,      T, _) => 1
     | (_, _:bool, _, _:bool, F, _:bool) => 2
     | (F, _) => 3
   ))`;

val testp_org4_def = Define_new `
 (testp_org4 p = (case p of
       (_, _,      T, _) => 1
     | (_, _:bool, _, _:bool, F, _:bool) => 2
     | (F, _) => 3
   ))`;


local 
  fun get_def thm = (rhs (snd (dest_forall (concl thm))))
in
 val test_org_t = get_def test_org_def
 val test_org2_t = get_def test_org2_def
 val test_lem_t = get_def test_lem_def
 val test_man_t = get_def test_man_def
 val test_man2_t = get_def test_man2_def

 val testp_org_t = get_def testp_org_def
 val testp_org2_t = get_def testp_org2_def
 val testp_org3_t = get_def testp_org3_def
 val testp_org4_t = get_def testp_org4_def
 val testp_lem_t = get_def testp_lem_def
 val testp_man_t = get_def testp_man_def
end

(* show that they are indeed all do the same thing *)
local

val bool_case_simp = prove (``(case b:bool of T => t | F => f) = (if b then t else f)``,
Cases_on `b` THEN SIMP_TAC std_ss [])

fun split_nil_tac v = Cases_on v THEN SIMP_TAC list_ss [test_lem_def, test_org_def, test_man_def, test_man2_def, bool_case_simp, test_org2_def]

in

val thmp_OK = prove (
``(testp_lem p = testp_org p) /\
  (testp_man p = testp_org p) /\
  (testp_org2 p = testp_org p) /\
  (testp_org3 p = testp_org p) /\
  (testp_org4 p = testp_org p)``,
Cases_on `p` THEN
Cases_on `r` THEN
Cases_on `r'` THEN
Cases_on `r` THEN
Cases_on `r'` THEN
Cases_on `r` THEN
Cases_on `q` THEN
Cases_on `q'` THEN
Cases_on `q''` THEN
Cases_on `q'''` THEN
Cases_on `q''''` THEN
SIMP_TAC list_ss [testp_lem_def, testp_org_def, pairTheory.pair_CASE_def, testp_org2_def, testp_man_def,
  testp_org3_def, testp_org4_def])

val thm_OK = prove (
``(test_lem l = test_org l) /\ 
  (test_man l = test_org l) /\
  (test_man2 l = test_org l) /\
  (test_org2 l = test_org l)``,

split_nil_tac `l` THEN
split_nil_tac `t` THEN
split_nil_tac `t'` THEN
split_nil_tac `t` THEN
split_nil_tac `t'` THEN
split_nil_tac `t` THEN
split_nil_tac `t'` THEN
PROVE_TAC[])

end


val size_test_org  = term_size test_org_t    (* 172 *)
val size_test2_org  = term_size test_org2_t  (* 82 *)
val size_test_lem  = term_size test_lem_t    (* 82 *)
val size_test_man  = term_size test_man_t    (* 52 *)
val size_test_man2 = term_size test_man2_t   (* 37 *)
val size_testp_org = term_size testp_org_t   (* 89 *)
val size_testp_org2 = term_size testp_org2_t (* 45 *)
val size_testp_org3 = term_size testp_org3_t (* 89 *)
val size_testp_org4 = term_size testp_org4_t (* 37 *)
val size_testp_lem = term_size testp_lem_t   (* 37 *)
val size_testp_man = term_size testp_man_t   (* 37 *)


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

val _ = run_it input_m ``test_org``;  (*  5.1 s *)
val _ = run_it input_m ``test_org2``; (*  4.9 s *)
val _ = run_it input_m ``test_lem``;  (*  4.9 s *)
val _ = run_it input_m ``test_man``;  (*  4.4 s *)
val _ = run_it input_m ``test_man2``; (*  3.9 s *)

val _ = run_it inputp_6 ``testp_org``;  (*  5.8 s *)
val _ = run_it inputp_6 ``testp_org2``; (*  5.4 s *)
val _ = run_it inputp_6 ``testp_org3``; (*  5.8 s *)
val _ = run_it inputp_6 ``testp_org4``; (*  4.7 s *)
val _ = run_it inputp_6 ``testp_lem``;  (*  5.4 s *)
val _ = run_it inputp_6 ``testp_man``;  (*  4.8 s *)


val _ = export_theory();
