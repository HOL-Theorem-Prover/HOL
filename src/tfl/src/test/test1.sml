fun function s q = Count.apply (tflLib.function s) q;

val nested_function = LIST_CONJ o map #1 o #extracta o
                      Tfl.wfrec_eqns (Datatype.theFactBase())
                      o Parse.Term;

function "fact_cond_def" `fact x = ((x = 0) => 1 | x * fact(x-1))`;

function "fact_pattern_def"
   `(Fact 0 = 1) /\
    (Fact (SUC x) = Fact x * SUC x)`;

function "Ffact_def" `(Ffact (SUC x) = Ffact x * SUC x)`;

function "Fib_def"
   `(Fib 0 = 1) /\
    (Fib (SUC 0) = 1) /\
    (Fib (SUC(SUC x)) = Fib x + Fib (SUC x))`;

function "Ffib_def" `(Ffib (SUC(SUC x)) = Ffib x + Fib (SUC x))`;

nested_function
   `(Ack (0,n) =  n+1) /\
    (Ack (SUC m,0) = Ack (m, 1)) /\
    (Ack (SUC m, SUC n) = Ack (m, Ack (SUC m, n)))`;

function "map2"
  `(map2(f, ([]:'a list),(L:'b list)) = ([]:'c list)) /\
   (map2(f, CONS h t,   []) = [])                         /\
   (map2(f, CONS h1 t1, CONS h2 t2) = CONS (f h1 h2) (map2 (f, t1, t2)))`;

function  "Map2"
  `(Map2((([]:'a list),(L:'b list)), f) = ([]:'c list)) /\
   (Map2((CONS h t, []),             f) = [])           /\
   (Map2((CONS h1 t1, CONS h2 t2),   f) = CONS (f h1 h2) (Map2((t1,t2),f)))`;

function "Mmap2"
  `(Mmap2((fn:'a->'b->'c), [],      []) = []) /\
   (Mmap2(fn,  CONS h1 t1, CONS h2 t2) = CONS (fn h1 h2) (Mmap2 (fn, t1,t2)))`;

val order = ty_antiq(==`:'a -> 'a -> bool`==);
function "sorted_def"
   `(sorted (R:^order, []) = T) /\
    (sorted (R,       [x]) = T) /\
    (sorted (R, CONS x (CONS y rst)) = R x y /\ sorted(R, CONS y rst))`;

function "fin" `(fin(R:^order,[x:'a]) = T)`;
new_infix {Name="++", Ty = Type`:'a list -> 'a list -> 'a list`, Prec = 650}
new_constant {Name="filter", Ty = Type`:('a -> bool) -> 'a list -> 'a list`};
new_constant {Name="mem", Ty = Type`:'a -> 'a list -> bool`};

function "qsort_def"
   `(qsort(ord:^order,[]) = []) /\
    (qsort(ord, CONS (x:'a) rst) =
      qsort(ord,filter($~ o ord x) rst)++[x]++qsort(ord,filter(ord x) rst))`;

function "variant_def" `variant(x, L) = (mem x L => variant(SUC x,L) | x)`;

function "gcd"
   `(gcd (0,y) = y) /\
    (gcd (SUC x, 0) = SUC x) /\
    (gcd (SUC x, SUC y) =
        ((y <= x)     => gcd(x-y, SUC y)
         | (*otherwise*) gcd(SUC x, y-x)))`;

function "AND_def"
   `(AND(x,[]) = x) /\
    (AND(y, CONS h t) = AND(y /\ h, t))`;

nested_function
  `ninety_one x = (x>100 => (x-10) | ninety_one (ninety_one (x+11)))`;

function "div_def"
   `(div(0,x) = (0,0)) /\
    (div(SUC x, y) = let (q,r) = div(x,y)
                     in y <= SUC r => (SUC q,0)
                                   |  (q, SUC r))`;

(* Nested paired lets *)
function "div_def"
   `(Div(0,x) = (0,0)) /\
    (Div(SUC x, y) = let (q,r) = Div(x,y) in
                     let (s,t) = (x,y)
                     in y <= SUC r => (SUC q,0)
                                   |  (q, SUC r))`;

function "Qsort_def"
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
function "acc1"
   `(acc1 ((f,p),([]:'a list),(s:'b),xss,zs,xs) =
      ((xs=[]) => (xss, zs) |  acc1((f,p), zs, s, (xss++[xs]),[],[]))) /\
    (acc1((f,(p:'c)), CONS y ys, s, xss, zs, xs) =
       let s' = s in let
          zs' = (f s' => [] | zs++[y]) in let
          xs' = (f s' => xs++zs++[y] | xs)
       in
          acc1((f,p), ys, s', xss, zs', xs'))`;

function "nested_if"
  `(f(0,x) = (0,0)) /\
   (f(SUC x, y) = (y = x => (0<y => (0,0) | f(x,y)) | (x,y)))`;

function "vary"
    `vary(x, L) = (mem x L => let x = SUC x in vary(x,L) | x)`;

function "tricky1"
    `vary1(x, L) = (mem x L => let x = SUC x in
                              let x = x in vary1(x,L) | x)`;

function "tricky2"
    `vary2(x, L) = (mem x L => let (x,y) = (SUC x,x) in
                               let (x,y) = (x,y) in vary2(x,L) | x)`;



(* Test nested lets -- auto-def will fail, since the binding to r is nested! *)
nested_function
   `(Divide(0,x) = (0,0)) /\
    (Divide(SUC x, y) = let q = FST(Divide(x,y)) in
                     let r = SND(Divide(x,y))
                     in y <= SUC r => (SUC q, 0)
                                   |  (q, SUC r))`;

