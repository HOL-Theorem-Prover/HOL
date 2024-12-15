
open HolKernel Parse boolLib bossLib cvTheory cv_repTheory cv_primTheory;
open cv_typeTheory cv_typeLib cv_repLib cv_transLib;
open arithmeticTheory integerTheory wordsTheory sptreeTheory wordsLib;

(*---------------------------------------------------------------------------*
  Testing only cv_type
 *---------------------------------------------------------------------------*)

val _ = Datatype ‘
  a = A1 (num list) (((a # b) list) list)
    | A2 ((a + b) list) ;
  b = B1
    | B2
    | B3 (c option) ;
  c = C1
    | C2 a 'aa 'bb
’

val ty = “:('d, 'c) b”
val res = define_from_to ty

val _ = Datatype ‘
  tree = Leaf
       | Branch ((tree list + bool) option list)
’

val res = define_from_to “:tree”

val _ = Datatype ‘
  t1 = T1 num (t1 list)
’

val res = define_from_to “:t1”

val _ = Datatype ‘
  word_tree =
    | Fork word_tree word_tree
    | Word1 ('a word)
    | Other 'b
    | Word2 ('c word)
’

val ty = “:('a,'b,'c) word_tree”
val res = define_from_to ty
val _ = (type_of “from_scratch_word_tree f0 t” = “:cv$cv”) orelse fail()

val res = define_from_to “:'a sptree$spt”

val _ = Datatype‘
  op = Add | Sub
’

val _ = Datatype ‘
  exp = Var string | Const int | Op op (exp list)
’

val _ = Datatype ‘
  prog = Skip | Seq prog prog | Assign string exp
’

(*---------------------------------------------------------------------------*
  Testing full cv_trans automation
 *---------------------------------------------------------------------------*)

fun test_for_failure f x =
  case total f x of
    NONE => ()
  | SOME _ => failwith "unexpected success";

val _ = Datatype `
  xx_yy = XX xx_yy | YY (xx_yy list)
`

val xx_yy_depth_def = Define `
  xx_yy_depth (XX x) = xx_yy_depth x /\
  xx_yy_depth (YY xs) = xx_yy_depth_list xs /\
  xx_yy_depth_list [] = 0:num /\
  xx_yy_depth_list (y::ys) = xx_yy_depth y + xx_yy_depth_list ys
`

val _ = cv_trans xx_yy_depth_def

val add1_def = Define `
  add1 a xs = MAP (\x . x + a:num) xs
`

val _ = cv_auto_trans add1_def;

val genlist_def = Define `
  genlist i f 0 = [] /\
  genlist i f (SUC n) = f i :: genlist (i+1:num) f n
`

val genlist_eq_GENLIST = store_thm("genlist_eq_GENLIST[cv_inline]",
  ``GENLIST = genlist 0``,
  qsuff_tac ‘!i f n. genlist i f n = GENLIST (f o (\k. k + i)) n’
  >- (gvs [FUN_EQ_THM] \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [FUN_EQ_THM])
  \\ Induct_on ‘n’ \\ gvs [genlist_def]
  \\ rewrite_tac [listTheory.GENLIST_CONS] \\ gvs []
  \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [FUN_EQ_THM,arithmeticTheory.ADD1]
);

val mult_table_def = Define `
  mult_table n = GENLIST (\i . GENLIST (\j . i * j) n) n
`

val _ = cv_auto_trans mult_table_def;

val _ = Datatype `
  rec = <| abc : num ; def : num; rest : rec list |>
`

val rec_test1_def = Define `
  rec_test1 r = r.abc + 1
`

val _ = cv_auto_trans rec_test1_def;

val rec_test2_def = Define `
  rec_test2 r = r with <| rest := r :: r.rest |>
`

val _ = cv_auto_trans rec_test2_def;

val rec_test3_def = Define `
  rec_test3 r = <| abc := 4; def := 45; rest := r.rest |>
`

val _ = cv_auto_trans rec_test3_def;

val fac_def = Define `
  fac (n:num) = if n = 0:num then 1 else n * fac (n-1)
`

val inc_def = Define `
  inc n = n + 1:num
`

val risky_def = Define `
  risky n = if n = 0 then ARB else n+1:num
`

val foo_def = Define `
  foo (n:num) k i = if n = 0:num then k + i + 1:num else
                    if 500 < n then ARB else n * foo (n-1) i k
`

val use_foo_def = Define `
  use_foo n = foo 1 (n + 2) 3
`

val cond_def_lemma = Q.prove (
  `?(f:num -> num) . !n . n <> 0 ==> f n = n - 1`,
  qexists_tac ‘\n. n - 1’ \\ fs []
)

val cond_def = new_specification("cond_sub_def",["cond_sub"],cond_def_lemma);

val res = cv_trans fac_def;
val res = cv_trans_pre foo_def;
val res = cv_trans_pre use_foo_def;
val res = cv_trans_pre risky_def;
val res = cv_trans inc_def;
val res = cv_trans_pre cond_def;

val _ = Datatype `
  a_type = A_cons | B_cons | C_cons num num | D_cons (a_type list)
`

val a_fun_def = Define `
  a_fun n = D_cons [A_cons; C_cons n 5]
`

val res = cv_trans a_fun_def;

open sptreeTheory

val _ = Datatype `
  b_type = B1 | B2 | B3 | B4 | B5 | B6 | B7
`

val _ = Datatype `
  c_type = C1 num | C2 c_type | C3 c_type
`

val num_sum_def = Define `
  num_sum ns =
    case ns of [] => 0:num | (n::ns) => n + num_sum ns
`

val res = cv_trans num_sum_def;
val res = cv_trans listTheory.LENGTH;
(* val res = cv_trans_pre lookup_def; *)

val f1_def = Define `
  f1 (n:num) = 1:num
`

val f2_def = Define `
  f2 n = f1 n
`

val f3_def = Define `
  f3 n = f2 n
`

val res = cv_auto_trans f3_def;

val fw1_def = Define `
  fw1 w = w + 1w
`

val fw2_def = Define `
  fw2 w = fw1 (w:word8)
`

val res = cv_auto_trans fw2_def;

val hello_def = Define `
  hello xs = "HELLO!" ++ xs
`

val res = cv_auto_trans hello_def;

val res = time cv_eval “f3 (1+2)”;

val even_def = Define `
  even 0 = T /\
  even (SUC n) = odd n /\
  odd 0 = F /\
  odd (SUC n) = even n
`

val res = cv_trans_pre even_def

val _ = store_thm("even_pre[local,cv_pre]",
  ``(!a0. even_pre a0) /\ (!a1. odd_pre a1)``,
  ho_match_mp_tac (fetch "-" "even_ind") \\ rpt strip_tac
  \\ once_rewrite_tac [res] \\ fs []
);

val th = cv_eval “even 10”
val th = cv_eval “even 999999”

val test_u2_def = Define `
  test_u2 n = (n+1:num,())
`

val _ = cv_trans test_u2_def;

val _ = Datatype `
  foo = RoseTree (num -> num) (foo list)
`

val _ = test_for_failure (cv_rep_for []) “RoseTree (\i. i) []”;

val missing_arg_def = Define `
  missing_arg = K
`

val _ = cv_trans combinTheory.K_THM
val _ = cv_trans missing_arg_def

val apply_list_def = Define `
  apply_list [] x = x /\
  apply_list (f::fs) x = apply_list fs (f x)
`

val _ = test_for_failure cv_trans apply_list_def;

val thms = rec_define_from_to “:prog”;

val _ = Datatype `
  trafficLight = Red | Yellow | Green
`

val nothing_def = Define `
  (nothing t [] = ()) /\
  (nothing t [x] = ()) /\
  (nothing t (x::xs) =
   nothing Red xs)
`

val _ = cv_trans nothing_def;

val _ = Datatype `
  clos_op = Add           (* + over the integers *)
          | Sub           (* - over the integers *)
`

val _ = Datatype `
  c_exp = Var num num
        | If num c_exp c_exp c_exp
        | Let num (c_exp list) c_exp
        | Raise num c_exp
        | Handle num c_exp c_exp
        | Tick num c_exp
        | Call num num (* ticks *) num (* loc *) (c_exp list) (* args *)
        | App num (num option) c_exp (c_exp list)
        | Fn string (num option) (num list option) num c_exp
        | Letrec (string list) (num option) (num list option) ((num # c_exp) list) c_exp
        | Op num clos_op (c_exp list)
`

val exp_size_alt_def = tDefine "exp_size_alt" `
  exp_size_alt ((Var x y) : c_exp) = 1:num /\
  exp_size_alt (If a b c d) = 1 + exp_size_alt b + exp_size_alt c + exp_size_alt d /\
  exp_size_alt (Let a es e) = 1 + exp_size_alt e + exp_sizes_alt es /\
  exp_size_alt (Handle a0 a1 a2) = 1 + exp_size_alt a1 + exp_size_alt a2 /\
  exp_size_alt (Tick a0 a1) = 1 + exp_size_alt a1 /\
  exp_size_alt (Call a0 a1 a2 a3) = 1 + exp_sizes_alt a3 /\
  exp_size_alt (App a0 a1 a2 a3) = 1 + exp_size_alt a2 + exp_sizes_alt a3 /\
  exp_size_alt (Fn a0 a1 a2 a3 a4) = 1 + exp_size_alt a4 /\
  exp_size_alt (Letrec a0 a1 a2 a3 a4) = 6 + exp_size_alt a4 /\
  exp_size_alt (Op a0 a1 a2) = 1 + exp_sizes_alt a2 /\
  exp_sizes_alt [] = 0 /\
  exp_sizes_alt (x::xs) = exp_size_alt x + exp_sizes_alt xs`
  cheat;

val pre = cv_auto_trans_pre_rec exp_size_alt_def cheat;

val can_raise_def = Define ` can_raise x = T `

val _ = Datatype `
  x_exp = x_If x_exp x_exp x_exp | x_Other `

val dest_handle_If_def = Define `
  dest_handle_If (x_If x1 x2 x3) =
     (if can_raise x1 then NONE
      else if can_raise x2 then
        if can_raise x3 then NONE else SOME (INL (x1,x2,x3))
      else if can_raise x3 then
        if can_raise x2 then NONE else SOME (INR (x1,x2,x3))
      else NONE) /\
  dest_handle_If _ = NONE `

val _ = cv_trans can_raise_def;
val _ = cv_trans dest_handle_If_def;

(*
val mem_test_def = Define `mem_test n = MEM n ["test1"; "test2"]`
val _ = cv_trans mem_test_def;
val _ = cv_eval ``mem_test "hi"``
*)
