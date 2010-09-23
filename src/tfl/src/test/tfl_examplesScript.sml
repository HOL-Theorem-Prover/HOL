open HolKernel boolLib bossLib Parse

fun function s q = Count.apply (bossLib.xDefine s) q; (* tries termination *)

val nested_function = LIST_CONJ o map #1 o #extracta o
                      Defn.wfrec_eqns (TypeBase.theTypeBase())
                      o Parse.Term;

val _ = new_theory "tfl_examples"

val fact_cond_def = function "fact_cond" `fact x = if x = 0 then 1 else x * fact(x-1)`;

val fact_pattern_def = function "fact_pattern"
   `(Fact 0 = 1) /\
    (Fact (SUC x) = Fact x * SUC x)`;

val Ffact_def = function "Ffact" `(Ffact (SUC x) = Ffact x * SUC x)`;

val Fib_def = function "Fib"
   `(Fib 0 = 1) /\
    (Fib (SUC 0) = 1) /\
    (Fib (SUC(SUC x)) = Fib x + Fib (SUC x))`;

val Ffib_def = function "Ffib" `(Ffib (SUC(SUC x)) = Ffib x + Fib (SUC x))`;

val _ = nested_function
   `(Ack (0,n) =  n+1) /\
    (Ack (SUC m,0) = Ack (m, 1)) /\
    (Ack (SUC m, SUC n) = Ack (m, Ack (SUC m, n)))`;

val map2_def = function "map2"
  `(map2(f, ([]:'a list),(L:'b list)) = ([]:'c list)) /\
   (map2(f, CONS h t,   []) = [])                         /\
   (map2(f, CONS h1 t1, CONS h2 t2) = CONS (f h1 h2) (map2 (f, t1, t2)))`;

val Map2_def = function  "Map2"
  `(Map2((([]:'a list),(L:'b list)), f) = ([]:'c list)) /\
   (Map2((CONS h t, []),             f) = [])           /\
   (Map2((CONS h1 t1, CONS h2 t2),   f) = CONS (f h1 h2) (Map2((t1,t2),f)))`;

val Mmap2_def = function "Mmap2"
  `(Mmap2((fn:'a->'b->'c), [],      []) = []) /\
   (Mmap2(fn,  CONS h1 t1, CONS h2 t2) = CONS (fn h1 h2) (Mmap2 (fn, t1,t2)))`;

val order = ty_antiq(==`:'a -> 'a -> bool`==);
val sorted_def = function "sorted"
   `(sorted (R:^order, []) = T) /\
    (sorted (R,       [x]) = T) /\
    (sorted (R, CONS x (CONS y rst)) = R x y /\ sorted(R, CONS y rst))`;

val fin_def = function "fin" `(fin(R:^order,[x:'a]) = T)`;
val _ = overload_on("filter", ``FILTER``)
val _ = overload_on ("mem", ``MEM``)

val qsort_defn = Hol_defn "qsort"
   `(qsort(ord:^order,[]) = []) /\
    (qsort(ord, CONS (x:'a) rst) =
      qsort(ord,filter($~ o ord x) rst)++[x]++qsort(ord,filter(ord x) rst))`;

val variant_def = Hol_defn "variant" `
  variant(x, L) = if mem x L then variant(SUC x,L) else x
`;

val gcd_def = function "gcd"
   `(gcd (0,y) = y) /\
    (gcd (SUC x, 0) = SUC x) /\
    (gcd (SUC x, SUC y) =
        (if y <= x then gcd(x-y, SUC y)
         else gcd(SUC x, y-x)))`;

val AND_def = function "AND"
   `(AND(x,[]) = x) /\
    (AND(y, CONS h t) = AND(y /\ h, t))`;

val _ = nested_function
  `ninety_one x = if x>100 then x-10 else ninety_one (ninety_one (x+11))`;

val div_def = function "div"
   `(div(0,x) = (0,0)) /\
    (div(SUC x, y) = let (q,r) = div(x,y) in
                       if y <= SUC r then (SUC q,0)
                       else  (q, SUC r))`;

(* Nested paired lets *)
(* uglification ensues *)
val div_def = function "div"
   `(Div(0,x) = (0,0)) /\
    (Div(SUC x, y) = let (q,r) = Div(x,y) in
                     let (s,t) = (x,y)
                     in if y <= SUC r then (SUC q,0)
                        else (q, SUC r))`;

(* as before, but with lets *)
val Qsort_def = Hol_defn "Qsort"
   `(Qsort(ord:^order,[]) = []) /\
    (Qsort(ord, CONS (x:'a) rst) =
      let ((L1,L2),P) = ((filter($~ o ord x) rst,
                          filter (ord x) rst),
                       (x,rst)) in
      let (lower,upper) = ((ord,L1),(ord,L2))
      in
      Qsort lower ++[x]++ Qsort upper)`;


(* From Tobias Nipkow; "acc1" forms part of a lexer.
   .... currently fails to prove induction theorem. *)
val acc1_def = Hol_defn "acc1"
   `(acc1 ((f,p),([]:'a list),(s:'b),xss,zs,xs) =
      if xs=[] then (xss, zs)
      else   acc1((f,p), zs, s, (xss++[xs]),[],[])) /\
    (acc1((f,(p:'c)), CONS y ys, s, xss, zs, xs) =
       let s' = s in
       let zs' = if f s' then [] else zs++[y] in
       let xs' = if f s' then xs++zs++[y] else xs
       in
          acc1((f,p), ys, s', xss, zs', xs'))`;

val nested_if_def = function "nested_if"
  `(f(0,x) = (0,0)) /\
   (f(SUC x, y) = if y = x then
                    if 0<y then (0,0) else f(x,y)
                  else (x,y))`;

val vary_defn = Hol_defn "vary"
    `vary(x, L) = if mem x L then let x = SUC x in vary(x,L) else x`;

val vary_lemma = prove(
  ``LENGTH (filter (\y. SUC x <= y) L) <= LENGTH (filter (\y. x <= y) L)``,
  Induct_on `L` THEN SRW_TAC [ARITH_ss][] THEN DECIDE_TAC);

val (vary_def, vary_ind) = Defn.tprove(
  vary_defn,
  WF_REL_TAC `measure \(x,L). LENGTH(filter (\y. x <= y) L)` THEN
  SRW_TAC [][] THEN
  Induct_on `L` THEN SRW_TAC [ARITH_ss][] THEN
  `x = h` by DECIDE_TAC THEN
  MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS THEN
  Q.EXISTS_TAC `LENGTH (filter (\y. x <= y) L)` THEN
  SRW_TAC [][vary_lemma]);

val vary1_def = Hol_defn "vary1"
    `vary1(x, L) = if mem x L then
                     let x = SUC x in
                     let x = x
                     in
                       vary1(x,L)
                   else x`;

val vary2_def = Hol_defn "vary2"
    `vary2(x, L) = if mem x L then let (x,y) = (SUC x,x) in
                               let (x,y) = (x,y) in vary2(x,L) else x`;



(* Test nested lets - ugly variable renaming happens *)
val Divide_def = function "Divide"
   `(Divide(0,x) = (0,0)) /\
    (Divide(SUC x, y) = let q = FST(Divide(x,y)) in
                     let r = SND(Divide(x,y))
                     in if y <= SUC r then (SUC q, 0)
                        else (q, SUC r))`;


(* Ramana Kumar's beta-redex definition bug 14/09/2010 *)
val _ = tDefine "foo"
`foo x = if (\x. x) x then foo F else ()`
(WF_REL_TAC `measure (\x. if x then 1 else 0)`);

val _ = export_theory()
