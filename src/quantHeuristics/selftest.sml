open HolKernel Parse boolTheory boolLib pairTheory
open quantHeuristicsLib simpLib boolSimps

local open quantHeuristicsLibAbbrev in end (* check it compiles *)

(* For manual

val hard_fail = false;
val quiet = false;
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;

*)

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

fun test_conv s conv (t, r_opt) =
    let
      fun msg t = s ^ " " ^ UnicodeChars.ldquo ^ term_to_string t ^
                  UnicodeChars.rdquo
    in
      case r_opt of
          SOME result => testutils.convtest (msg t, conv, t, result)
        | NONE => testutils.shouldfail {
                   checkexn = fn Interrupt => false | _ => true,
                   printarg = msg, printresult = thm_to_string, testfn = conv
                 } t
    end

val hard_fail = false;
val hard_fail = true;
val quiet = false;

(******************************************************************************)
(* General tests                                                              *)
(******************************************************************************)


local
   val x = mk_var ("x", numLib.num);
   fun mk_eq_n n =
      mk_eq (x, numSyntax.term_of_int n)

   fun mk_eq_disj n =
   if (n = 1) then mk_eq_n 1 else
   mk_disj (mk_eq_n n, mk_eq_disj (n-1))

in
   fun mk_eq_disj_ex n = mk_exists (x, mk_eq_disj n)
end

local
   val x = mk_var ("x", numLib.num);
   fun mk_eq_n n =
      mk_eq (x, numSyntax.term_of_int n)

   fun mk_eq_disj m n =
   if (n = 1) then mk_eq_n m else
   let
      val n2 = n div 2
      val n3 = n - n2;
   in
       mk_disj (mk_eq_disj m n2, mk_eq_disj (m+n2) n3)
   end;

in
   fun mk_eq_disj_ex2 n = mk_exists (x, mk_eq_disj 0 n)
end


val qh_testCases =
  [(``?x. x = 2``, SOME ``T``),
   (``?x. f x = f 2``, SOME ``T``),
   (``?x. f x = 2``, NONE),
   (``?x. P x /\ (x = 2)``, SOME ``(P 2):bool``),
   (``?x. ~~(P x /\ (x = 2))``, SOME ``(P 2):bool``),
   (``?x. P1 x /\ (x = 2) /\ P2 x /\ P3 x /\ P4 x``, SOME ``P1 2 /\ P2 2 /\ P3 2 /\ P4 2``),
   (``?x. P /\ (x = 2)``, SOME ``P:bool``),
   (``?x1 x2. P1 x2 ==> ((x1 = 2) /\ P2(x1, x2))``, SOME ``?x2. P1 x2 ==> (P2(2, x2))``),
   (``?x. P x \/ (x = 2)``, SOME T),
   (``?x. (x = 2) \/ Q x``, SOME T),
   (``?x. (f x = f 2) /\ Q``, SOME ``Q:bool``),
   (``!x. x = 2``, NONE),
   (``!x. (x = 2) ==> P x``, SOME ``(P 2):bool``),
   (``!x. (Q x /\ (x = 2)) ==> P x``, SOME ``Q 2 ==> P 2``),
   (``?x:'a. (?y:'b. (x = f y)) /\ P x``, SOME ``?y:'b. P ((f y):'a)``),
   (``?x. ~(Q3 x \/ Q x \/ Q2 x \/ ~(x = 2))``, SOME ``~(Q3 2 \/ Q 2 \/ Q2 2)``),
   (``?x:'a. (!y:'b. (x = f y)) /\ P x``, SOME ``?y:'b. (!y'. f y = f y') /\ P ((f y):'a)``),
   (``?x:'a. (!y2:'b y:'b y3:'b. (x = f y y2 y3)) /\ P x``, SOME ``?y2:'b y:'b y3:'b. (!y2' y' y3'. f y y2 y3 = f y' y2' y3') /\ P ((f y y2 y3):'a)``),
   (``?x:'a. Q x /\ (?y:'b. (x = f y)) /\ P x``, SOME ``?y:'b. Q (f y) /\ P ((f y):'a)``),
   (``?x. if b x then ((x = 2) /\ Q x) else (Q2 x /\ (x = 2))``,
    SOME ``if b 2 then (Q 2):bool else Q2 2``),
   (``?!x. (x = 2) /\ P x``, SOME ``(P 2):bool``),
   (mk_eq_disj_ex 40, SOME T)];

val qh_test = test_conv "QUANT_INSTANTIATE_CONV []" (QUANT_INSTANTIATE_CONV [])
val _ = map qh_test qh_testCases;


(******************************************************************************)
(* QUANT_CONV tests                                                           *)
(******************************************************************************)

val _ = test_conv "INST_QUANT_CONV [(\"x\", `2:num`, [])]" (INST_QUANT_CONV [("x", `2:num`, [])])
   (``!z. !x. (x = 2:num) ==> P(x, z)``, SOME ``!z. P(2, z)``)

val _ = test_conv "INST_QUANT_CONV [(\"x\", `2:num`, [])]" (INST_QUANT_CONV [("x", `2:num`, [])])
   (``!z. ?x. (x = 2:num) /\ P(x, z)``, SOME ``!z. P(2, z)``)

val _ = test_conv "INST_QUANT_CONV [(\"x\", `3:num`, [])]" (INST_QUANT_CONV [("x", `3:num`, [])])
   (``!z. ?x. (x = 2:num) /\ P(x, z)``, NONE)

(*
QUANT_INSTANTIATE_CONV [] ``?x. if b x then ((x = 2) /\ Q x) else (Q2 x /\ (x = 2))``

exceptionLocation UNCHANGED
 (fn () =>
(QUANT_INSTANTIATE_CONV [] ``?x. if b x then ((x = 2) /\ Q x) else (Q2 x /\ (x = 2))``; NONE)
handle exn => exceptionLocation exn

open PolyML
PolyML.stackTrace()
PolyML.Compiler.debug := true


free_in ``y:num`` (mk_eq_disj_ex 4000)
val conv = (QUANT_INSTANTIATE_CONV [])

val (v,t) = dest_forall ``!x. ~~(x = 2) ==> P x``
val t = mk_neg t

QUANT_INSTANTIATE_CONV [] ``?x. ~~(x = 2)``
QUANT_INSTANTIATE_CONV [] ``?x. if b x then ((x = 2) /\ Q x) else (Q2 x /\ (x = 2))``

open PolyML
stackTrace ()
PolyML.debug = 1
time conv t
PolyML.profiling 2
val t = (mk_eq_disj_ex 40)
val t = (mk_eq_disj_ex2 40)
val (v,t) = dest_exists ``?x. if b x then ((x = 2) /\ Q x) else (Q2 x /\ (x = 2))``


QUANT_INSTANTIATE_HEURISTIC___debug := 3;

conv ``?y:num. (z = 40)``
t

time (QUANT_INSTANTIATE_CONV []) ``?x.
quantHeuristicsArgsLib
QUANT_INSTANTIATE_HEURISTIC___debug := 0

((x = 8) \/ (x = 7) \/ (x = 6) \/ (x = 1) \/ (x = 2) \/ (x = 3)  \/ (x = 4) \/ (x = 5))``
*)

(******************************************************************************)
(* Pair tests                                                                 *)
(******************************************************************************)

val qh_test_pair = test_conv "QUANT_INSTANTIATE_CONV [pair_default_qp]" (QUANT_INSTANTIATE_CONV [pair_default_qp])

val qh_testCases_pair =
  [(``?p:('a # 'b). (x = FST p) /\ Q p``, SOME ``?p_2:'b. Q(x:'a,p_2)``),
   (``?p:('a # 'b). (x = SND p) /\ Q p``, SOME ``?p_1:'a. Q(p_1,x:'b)``),
   (``?v:'a. (v,X:'b) = Z``, SOME ``X = SND (Z:('a # 'b))``),
   (``!x. a /\ (\ (a1:'a, t3:'b, a2:'c). P a1 a2 t3) x /\ b x``,
    SOME ``!a1:'a t3:'b a2:'c. a /\ (\ (a1:'a, t3:'b, a2:'c). P a1 a2 t3) (a1,t3,a2) /\ b (a1,t3,a2)``),
   (``?v:'a. (v,X:'b) = (a,b)``, SOME ``X:'b = b``)];

val _ = map qh_test_pair qh_testCases_pair;



(******************************************************************************)
(* Option tests                                                               *)
(******************************************************************************)

val qh_test_option = test_conv "QUANT_INSTANTIATE_CONV [option_qp]" (QUANT_INSTANTIATE_CONV [option_qp])

val qh_testCases_option =
  [(``!x:'a option. IS_SOME x ==> P x``, SOME ``!x_x':'a. P (SOME x_x')``),
   (``?x:'a option. IS_SOME x ==> P x``, SOME T),
   (``!x:'a option. ~(IS_SOME x) ==> P x``, SOME ``(P (NONE:'a option)):bool``),
   (``?x. IS_SOME x``, SOME T),
   (``!x. IS_SOME x``, SOME F),
   (``?x. IS_NONE x``, SOME T),
   (``!x. IS_NONE x``, SOME F)];

val _ = map qh_test_option qh_testCases_option;


(******************************************************************************)
(* Num tests                                                               *)
(******************************************************************************)

val qh_test_num = test_conv "QUANT_INSTANTIATE_CONV [num_qp]" (QUANT_INSTANTIATE_CONV [num_qp])

val qh_testCases_num =
  [(``!x:num. (x + 7 = 2 + 7)``, SOME F),
   (``!x:num. ~(x = 0) ==> P x``, SOME ``!x_n. P (SUC x_n)``),
   (``!x:num. x = y``, SOME F),
   (``!x:num. y = x``, SOME F)];

val _ = map qh_test_num qh_testCases_num;


(******************************************************************************)
(* LIST tests                                                                 *)
(******************************************************************************)

val qh_test_list =
    test_conv "QUANT_INSTANTIATE_CONV [list_qp]"
              (QUANT_INSTANTIATE_CONV [list_qp])

val qh_testCases_list =
  [(``!l:'a list. ~(NULL l) ==> P l``, SOME ``!l_h l_t. P (l_h::l_t)``),
   (``!x. x = y::ys``, SOME F),
   (``!x. x = []``, SOME F),
   (``?l. ~(NULL l)``, SOME T),
   (``?x:'a xs. QQ /\ (x::xs = y::ys) /\ P /\ Q xs``,
    SOME ``QQ /\ P /\ Q (ys:'a list)``),
   (``?x. PP ==> ~(x = []) /\ P x``,
    SOME ``?x_h x_t:'a list. PP ==> P (x_h::x_t)``)];
val _ = map qh_test_list qh_testCases_list;


(******************************************************************************)
(* Option tests                                                               *)
(******************************************************************************)

val qh_test_option = test_conv "QUANT_INSTANTIATE_CONV [option_qp]"
                               (QUANT_INSTANTIATE_CONV [option_qp])

val qh_testCases_option =
  [(``!x:'a option. IS_SOME x ==> P x``, SOME ``!x_x':'a. P (SOME x_x')``),
   (``?x:'a option. IS_SOME x ==> P x``, SOME T),
   (``!x:'a option. ~(IS_SOME x) ==> P x``, SOME ``(P (NONE:'a option)):bool``),
   (``?x. IS_SOME x``, SOME T),
   (``!x. IS_SOME x``, SOME F),
   (``?x. IS_NONE x``, SOME T),
   (``!x. IS_NONE x``, SOME F)];

val _ = map qh_test_option qh_testCases_option;

(******************************************************************************)
(* SUM tests                                                                  *)
(******************************************************************************)

val qh_test_sum = test_conv "QUANT_INSTANTIATE_CONV [sum_qp]"
                            (QUANT_INSTANTIATE_CONV [sum_qp])

val qh_testCases_sum =
  [(``!x:'a + 'b. ISL x ==> P x``, SOME ``!l. P ((INL l):('a + 'b))``),
   (``!x:'a + 'b. ISR x ==> P x``, SOME ``!r. P ((INR r):('a + 'b))``),
   (``?x:'a + 'b. ISL x ==> P x``, SOME T),
   (``?x:'a + 'b. ISR x ==> P x``, SOME T),
   (``!x:'a + 'b. ~(ISR x) ==> P x``, SOME ``!l. (P ((INL l):('a + 'b)))``),
   (``!x:'a + 'b. ~(ISL x) ==> P x``, SOME ``!r. (P ((INR r):('a + 'b)))``),
   (``!p_1 p_2. x <> OUTR p_2 \/ ISL p_2 \/ P p_1 p_2``, SOME ``!p_1. P p_1 (INR x)``),
   (``?x. ISL x``, SOME T),
   (``!x. ISL x``, SOME F),
   (``?x. ISR x``, SOME T),
   (``!x. ISR x``, SOME F)];

val _ = map qh_test_sum qh_testCases_sum;

(******************************************************************************)
(* Context tests                                                              *)
(******************************************************************************)

val qh_test_direct_context =
    test_conv "SIMP_CONV (bool_ss++QUANT_INST_ss[direct_context_qp]) []"
              (SIMP_CONV (bool_ss++QUANT_INST_ss[direct_context_qp]) [])

val qh_testCases_direct_context =
  [(``(P x) ==> !x. ~(P x) /\ Q x``, SOME ``~(P x)``),
   (``~(P x) ==> !x. P x /\ Q x``, SOME ``(P (x:'a)):bool``),
   (``P x ==> ?x. Q x \/ P x``, SOME ``T``)
] (* Untested!? *)


val qh_test_context =
    test_conv "SIMP_CONV (bool_ss++QUANT_INST_ss[context_qp]) []"
              (SIMP_CONV (bool_ss++QUANT_INST_ss[context_qp]) [])
val qh_testCases_context =
  [(``(!x. P x ==> (x = 2)) ==> (!x. P x ==> Q x)``,
    SOME ``(!x. P x ==> (x = 2)) ==> P 2 ==> Q 2``),
   (``(!x. Q x ==> P x) /\ Q 2 ==> (?x. P x)``, SOME T)
]

val _ = map qh_test_context qh_testCases_context;


val qh_test_context2 =
    test_conv "SIMP_CONV (bool_ss++QUANT_INST_ss[std_qp]) []"
              (SIMP_CONV (bool_ss++QUANT_INST_ss[std_qp]) [])

val qh_testCases_context2 =
  [(``(~(P [])) ==> (!x. P x ==> Q x)``,
    SOME ``¬P [] ⇒ ∀x_h x_t. P (x_h::x_t) ⇒ Q (x_h::x_t)``),
   (``(!x. P x ==> ~(x = [])) ==> (!x. P x ==> Q x)``,
    SOME ``¬P [] ⇒ ∀x_h x_t. P (x_h::x_t) ⇒ Q (x_h::x_t)``),
   (``(!x. P x ==> ISR x) ==> (!x. P x ==> Q x)``,
    SOME ``(!l. ~((P:('a + 'b)-> bool) (INL l))) ==>
           (!r. P (INR r) ==> (Q:('a + 'b)-> bool) (INR r))``),
   (``(!x. P x ==> ISL x) ==> (!x. P x ==> Q x)``,
    SOME ``(!r. ~((P:('a + 'b)-> bool) (INR r))) ==>
           (!l. P (INL l) ==> (Q:('a + 'b)-> bool) (INL l))``)]

val _ = map qh_test_context2 qh_testCases_context2;


(******************************************************************************)
(* simple tests                                                               *)
(******************************************************************************)

val qh_test_simple =
    test_conv "SIMPLE_QUANT_INSTANTIATE_CONV" SIMPLE_QUANT_INSTANTIATE_CONV

val qh_testCases_simple =
  [(``!x. (P x /\ (x = 5) /\ Q x) ==> Z x``,
    SOME ``(P 5 /\ (5 = 5) /\ Q 5) ==> Z 5``),

   (``?x. (P x /\ (x = 5) /\ Q x)``, SOME ``(P 5 /\ (5 = 5) /\ Q 5)``),

   (``!x. (P x \/ ~(x = 5) \/ Q x)``, SOME ``(P 5 \/ ~(5 = 5) \/ Q 5)``),

   (``?x. (P x /\ x)``, SOME ``P T /\ T``),
   (``!x. (P x \/ ~x)``, SOME ``P T \/ ~T``),

   (``?x. (x = 5)``, SOME ``5 = 5``),
   (``!x. ~(5 = x)``, SOME ``~(5 = 5)``),

   (``?!x. (P x /\ (x = 5) /\ Q x)``, SOME ``(P 5 /\ (5 = 5) /\ Q 5)``),

   (``some x. (P x /\ (x = 5) /\ Q x)``,
    SOME ``if (P 5 /\ (5 = 5) /\ Q 5) then SOME 5 else NONE``),

   (``@x. (P x /\ (x = 5) /\ Q x)``,
    SOME ``if (P 5 /\ (5 = 5) /\ Q 5) then 5 else @x. F``),


   (``!x y z. (P x \/ ~(x = f y z) \/ Q x)``,
    SOME ``!y:'b z:'c. (P (f y z) \/ ~(f y z = f y z) \/ Q (f y z))``),


   (``?x. (P x /\ (5 = x) /\ Q x)``, SOME ``(P 5 /\ (5 = 5) /\ Q 5)``),
   (``?x. (P x /\ (!z:'a. (5 = x) /\ Q x z))``,
    SOME ``(P 5 /\ (!z:'a. (5 = 5) /\ Q 5 z))``),
   (``?x. (P x /\ (?z:'a. (5 = x) /\ Q x z))``,
    SOME ``(P 5 /\ (?z:'a. (5 = 5) /\ Q 5 z))``),

   (``!x. ~(P x /\ (5 = x) /\ Q x)``, SOME ``~(P 5 /\ (5 = 5) /\ Q 5)``),
   (``!x. ~(P x /\ (!z:'a. (5 = x) /\ Q x z))``,
    SOME ``~(P 5 /\ (!z:'a. (5 = 5) /\ Q 5 z))``),
   (``!x. ~(P x /\ (?z:'a. (5 = x) /\ Q x z))``,
    SOME ``~(P 5 /\ (?z:'a. (5 = 5) /\ Q 5 z))``),

   (``?x. (x, y) = (X:('a # 'b))``, SOME ``(FST X, y) = (X:('a # 'b))``),
   (``?x. ((y, x) = (X:('a # 'b)))``, SOME ``(y, SND X) = (X:('a # 'b))``),
   (``?x. ((3, (y:'a, x:'b), z:'c)) = X``,
    SOME ``((3,(y:'a,SND (FST (SND X))),z:'c) = X)``),
   (``?x. (3::4::l = y::x::l')``, SOME ``(3::4::l = y::4::l')``),
   (``?l'. (3::4::l = y::x::l')``, SOME ``(3::4::l = y::x::l)``),
   (``?y. (3::4::l = y::x::l')``, SOME ``(3::4::l = 3::x::l')``),
   (``?x. (SOME x = f)``, SOME ``(SOME (THE f) = f)``)
]


val _ = map qh_test_simple qh_testCases_simple;


val _ = Process.exit Process.success;
