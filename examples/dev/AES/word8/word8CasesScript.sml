(*===========================================================================*)
(* Simple theory of bytes.                                                   *)
(*===========================================================================*)
load "word8Lib";
open HolKernel Parse boolLib bossLib word8Lib word8Theory;

val _ = new_theory "word8Cases";

val word8Type = mk_type ("word8", []);
val alphaType = mk_vartype "'a";

fun iota n acc =
  if n < 0 then []
  else if n = 0 then 0 :: acc
  else iota (n - 1) (n :: acc)

fun buildVar name t n = mk_var ((name ^ int_to_string n), t)

val prim_rec = prove (
let val nums = iota 255 []
    val vars = map (buildVar "w" alphaType) nums
    val body_eqns = 
      Lib.map2
       (fn n => fn v =>
         ``fn (n2w ^(numSyntax.term_of_int n)) = ^v``)
       nums vars
in
  foldr mk_forall ``?fn. ^(foldr mk_conj (hd body_eqns) (tl body_eqns))`` vars
end,

                        
);

val case_analysis = prove (
let val nums = iota 255 []
    val vars = map (buildVar "w" alphaType) nums
    val inner_clauses =
         Lib.map2 (fn n => fn v => 
                    ``n2w ^(numSyntax.term_of_int n) -> ^v``)
                  nums vars
    val inner_clauses2 = 
        foldr (fn (x, y) => ``^x || ^y``) (hd inner_clauses) (tl inner_clauses)
    val clauses = 
        (Lib.map2 (fn n => fn v =>
                     foldr mk_forall
                           ``(case n2w ^(numSyntax.term_of_int n) of
                                ^inner_clauses2) =
                             ^v``
                           vars)
                   nums vars)
in
  foldr mk_conj (hd clauses) (tl clauses)
end,

);

val induction = prove (
let val clauses =
       List.map 
        (fn n => ``(P :word8 -> bool) (n2w ^(numSyntax.term_of_int n))``)
        (iota 255 [])
in
  ``!(P :word8 -> bool). ^(foldr mk_conj (hd clauses) (tl clauses)) ==> 
                         !b. P b``
end,


);


val distinctness = prove (
let val clauses = flatten
      (List.map (fn i =>
                  List.map (fn j =>
                              ``~(n2w ^(numSyntax.term_of_int i) =
                                  n2w ^(numSyntax.term_of_int j))``)
                           (iota (i - 1) []))
                (iota 255 []))
in
  foldr mk_conj (hd clauses) (tl clauses)
end,

);


val _ = export_theory();

