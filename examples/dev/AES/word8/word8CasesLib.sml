(*===========================================================================*)
(* Simple theory of bytes.                                                   *)
(*===========================================================================*)

(* Interactive mode:
  load "word8Lib";
  load "word8CasesTheory";
*)
structure word8CasesLib = struct
open HolKernel Parse boolLib bossLib word8Lib word8Theory word8CasesTheory

datatype clause = Var of term * term
                | Num of int * term

fun cvt_param (arg, res) =
  if is_var arg then
    Var (arg, res)
  else if is_comb arg then
    let val (n2w, nums) = strip_comb arg in
      if term_eq ``n2w`` n2w andalso
         length nums = 1 andalso
         numSyntax.is_numeral (hd nums) then
        Num (numSyntax.int_of_term (hd nums) mod 256, res)
      else
        raise (mk_HOL_ERR "word8Cases" "word8Define" 
                          "bad syntax in word constant")
    end
  else
    raise (mk_HOL_ERR "word8Cases" "word8Define"
                      "argument must be a syntactic variable or word constant")

fun to_first_var [] acc = (acc, NONE)
  | to_first_var [Var x] acc = (acc, SOME x)
  | to_first_var [Num x] acc = (x :: acc, NONE)
  | to_first_var (Var x :: t) acc = 
      (HOL_WARNING "word8Cases" "word8Define"
                   "ignoring cases after variable parameter case";
       (rev acc, SOME x))
  | to_first_var (Num x :: t) acc = 
      to_first_var t (x :: acc)

fun fill_results_helper next i j r default warn = 
  let val first_pad_amt  = i - next 
      val second_pad_amt = j - i - 1
  in
    if first_pad_amt > 0 orelse second_pad_amt > 0 then
      warn ()
    else ();
    (List.tabulate (first_pad_amt, default) @ [r] @
      List.tabulate (second_pad_amt, default),
     next + 1 + first_pad_amt + second_pad_amt)
  end

fun fill_results [] default warn next =
      if next = 256 then
        []
      else
       (warn ();
        List.tabulate (256 - next, default))
  | fill_results [(i, r)] default warn next =
      #1 (fill_results_helper next i 256 r default warn)
  | fill_results ((i, r1) :: (j, r2) :: t) default warn next = 
      if i = j then
        raise (mk_HOL_ERR "word8Cases" "word8Define"
                        ("duplicate definitions for " ^ int_to_string i ^ "w"))
      else 
        let val (rs, next_next) = 
                fill_results_helper next i j r1 default warn
        in 
          rs @ fill_results ((j, r2) :: t) default warn next_next
        end

fun word8Define def_term = 
  let val clauses = strip_conj def_term
      val name = #1 (strip_comb (#1 (dest_eq (hd clauses))))
      val params = map (hd o #2 o strip_comb o #1 o dest_eq) clauses
      val results = map (#2 o dest_eq) clauses
      val (num_params, var_param) =
        to_first_var (map cvt_param (zip params results)) []
      val s_num_params = sort (fn (x, _) => fn (y, _) => x < y) num_params
      val result_type = type_of (hd results)
      val results_no_gaps = 
        fill_results s_num_params
                     (case var_param of
                        SOME (var, res) => (fn _ => res)
                      | NONE => 
                         (fn _ => mk_arb result_type))
                     (case var_param of
                        SOME (var, res) => (fn _ => ())
                      | NONE => (fn _ =>
                                  HOL_WARNING "word8Cases" "word8Definition"
                                              "cases not exhaustive"))
                     0
      val def = Define 
      `^name = ^(list_mk_comb (inst [alpha |-> result_type] ``word8_cases``, 
                               results_no_gaps))`
      val simp_def = WORD_RULE (PURE_ONCE_REWRITE_RULE [word8_cases_def] def)
      val eqns =
        (map (fn (num, res) =>
                ``^(#1 (dest_eq (concl def)))
                  (n2w ^(numSyntax.term_of_int num)) =
                  ^res``)
              s_num_params) @
        (case var_param of
           SOME (var, res) => [``!^var. ^name ^var = ^res``]
         | NONE => [])
      val thms =
        map (fn e => prove (e, PURE_ONCE_REWRITE_TAC [simp_def] THEN WORD_TAC))
            eqns
  in
    (def, simp_def, LIST_CONJ thms)
  end


end
(*
word8Define ``f (x:word8) = 1``;
word8Define ``f (x:word8) = x``;
word8Define ``f 1w = 1``;
word8Define ``(f 1w = 1) /\ (f x = 2)``;
word8Define ``(f 0w = 1) /\ (f x = 2) /\ (f 0w = 3)``;
word8Define ``(f 0w = 1) /\ (f 2w = 2) /\ (f 4w = 3)``;
word8Define ``(f 1w = 1) /\ (f 3w = 2) /\ (f 5w = 3)``;
word8Define ``(f 0w = 1) /\ (f 256w = 1)`` handle e => Raise e;
word8Define ``(f 0 = 1)`` handle e => Raise e;
word8Define ``(f (a b) = 1)`` handle e => Raise e;
*)
