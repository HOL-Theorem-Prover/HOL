(*---------------------------------------------------------------------------
 * Some basic tests.
 *---------------------------------------------------------------------------*)
app load ["tflLib"];
open tflLib;

fun Rfunction s q1 q2 = Count.apply (tflLib.Rfunction s q1) q2;

Rfunction "fact_cond_def" 
          `^(tflLib.pred)`
     `fact x = ((x = 0) => 1 | x * fact(x-1))`;

Rfunction "fact_pattern_def"
          `^pred`
   `(Fact 0 = 1) /\
    (Fact (SUC x) = Fact x * SUC x)`;

Rfunction "fib_def" `$<`
   `(Fib 0 = 1) /\
    (Fib (SUC 0) = 1) /\
    (Fib (SUC(SUC x)) = Fib x + Fib (SUC x))`;

Rfunction "Ack_def" `$< ** $<`
   `(Ack (0,n) =  n+1) /\
    (Ack (SUC m,0) = Ack (m, 1)) /\
    (Ack (SUC m, SUC n) = Ack (m, Ack (SUC m, n)))`;

Rfunction "ack_def" 
          `^pred ** ^pred`
   `(ack (0,n) =  n+1) /\
    (ack (SUC m,0) = ack (m, 1)) /\
    (ack (SUC m, SUC n) = ack (m, ack (SUC m, n)))`;

val smaller_def = Rfunction "smaller_def" 
                     `inv_image ^pred (FST o FST)`
  `(smaller((0,i), z) = (i:num))    /\
   (smaller((SUC x, i), (0,j)) = j) /\
   (smaller((SUC x, i), (SUC y,j)) = 
      ((SUC y = i) => i
     | (SUC x = j) => j
     | smaller((x,i), (y,j))))`;

(* Finds the smaller of two Peano numbers efficiently: count down
 * both until you bump into one or the other original values (or 0). *)
Rfunction "min_def"
          `Empty` 
   `min (x,y) = smaller((x,x), (y,y))`;

Rfunction "map2_def"
          `inv_image ^list_pred (FST o SND)`
  `(map2(f, ([]:'a list),(L:'b list)) = ([]:'c list)) /\
   (map2(f, CONS h t,   []) = [])                     /\
   (map2(f, CONS h1 t1, CONS h2 t2) = CONS (f h1 h2) (map2 (f, t1, t2)))`;

Rfunction "sorted"
          `inv_image ^list_pred SND`
   `(sorted (R, []) = T) /\
    (sorted (R,       [x]) = T) /\   
    (sorted (R, CONS x (CONS y rst)) = R x y /\ sorted(R, CONS y rst))`;

(* Supporting constant declarations.  *)
val _ = new_infix{Name="++", Prec=300, Ty=Type`:'a list->'a list->'a list`};
val _ = map new_constant 
            [{Name="filter", Ty=Type`:('a->bool)->'a list->'a list`},
             {Name="mem",    Ty=Type`:'a->'a list -> bool`}];

Rfunction "qsort_def"
          `measure (LENGTH o SND)` 
   `(qsort(ord,[]) = []) /\
    (qsort(ord, CONS x rst) = 
      qsort(ord,filter($~ o ord x) rst)
      ++[x]++
      qsort(ord,filter(ord x) rst))`;

Rfunction "variant_def"
          `measure \(x,L). LENGTH(filter (\y. x <= y) L)`
   `variant(x, L) = (mem x L => variant(SUC x, L) | x)`;

Rfunction "gcd_def"
          `measure \(x,y). x+y`
   `(gcd (0,y) = y) /\
    (gcd (SUC x, 0) = SUC x) /\
    (gcd (SUC x, SUC y) = 
        ((y <= x)     => gcd(x-y, SUC y) 
         | (*otherwise*) gcd(SUC x, y-x)))`;

Rfunction "G_def"
          `$<` 
   `(G 0 = 0) /\
    (G (SUC x) = G (G x))`;

Rfunction "ninety1_def"
          `measure \x. 101 - x`
`ninety_one x = (x>100 => (x-10) | ninety_one (ninety_one (x+11)))`;

Rfunction "div_def"
          `inv_image ^pred FST`
   `(div(0,x) = (0,0)) /\
    (div(SUC x, y) = let (q,r) = div(x,y)
                     in (y <= SUC r) => (SUC q,0) 
                        | (*otherwise*) (q, SUC r))`;

(* Test nested lets *)
Rfunction "Div_def"
          `inv_image ^pred FST`
   `(Div(0,x) = (0,0)) /\
    (Div(SUC x, y) = let q = FST(Div(x,y)) in
                     let r = SND(Div(x,y))
                     in (y <= SUC r) => (SUC q,0) 
                        | (*otherwise*) (q, SUC r))`;

Rfunction "part_def"
          `inv_image ^list_pred (FST o SND)`
   `(part(P:'a->bool, [], l1,l2) = (l1,l2)) /\
    (part(P, CONS h rst, l1,l2) =
        (P h => part(P,rst, CONS h l1, l2)
             |  part(P,rst,  l1,  CONS h l2)))`;
  

(* Have to note that our tuples may not be the tuples of SML! *)
val partition_def = 
  new_definition
    ("partition", Term`!(P:'a->bool). partition(P,L) = part(P,L,[],[])`);


(* The quicksort algorithm  *)
Rfunction "fqsort_def"
          `measure (LENGTH o SND)`
   `(fqsort(ord,[]) = []) /\
    (fqsort(ord, CONS x rst) = 
        let (l1,l2) = partition((\y. ord y x), rst)
        in
          fqsort(ord,l1)++[x]++fqsort(ord,l2))`;


Rfunction "Qsort_def"
          `measure (LENGTH o SND)`
   `(Qsort(ord,[]) = []) /\
    (Qsort(ord, CONS x rst) = 
      let ((L1,L2),P) = (partition((\y. ord y x), rst), (x,rst)) in
      let (lower,upper) = ((ord,L1),(ord,L2))
      in
      Qsort lower ++[x]++ Qsort upper)`;


(* Limitations of antiquotes seen: polymorphic constants have type
   variables that are constrainable, but list_pred was being antiquoted in, 
   and had ordinary type variables, which are deemed to be constant for
   type inference.
*)

val list_pred_def = 
   new_definition("list_pred", Term`list_pred l1 l2 = ?h:'a. l2 = CONS h l1`);


Rfunction "AND_def"
          `inv_image list_pred SND`
   `(AND(x,[]) = x) /\
    (AND(y, CONS h t) = AND(y /\ h, t))`;

(* Patterns in "non-standard" order *)
Rfunction "rev_def"
          `^list_pred` 
  `(rev (CONS h t) = CONS h (rev t)) /\ 
   (rev ([]:'a list) = [])`;

val fdef = (hd o map #1 o #extracta)
  (Tfl.wfrec_eqns (Datatype.theFactBase())
       (Term`f x = num_case 1 (\m. SUC m * f m) x`));

load"QLib";
val fdef0 = RW.RW_RULE[] (Q.INST[`x:num` |-> `0`] fdef);
val fdef1 = BETA_RULE (RW.RW_RULE[] (Q.INST[`x:num` |-> `SUC m`] fdef));
val fdef_all = CONJ fdef0 fdef1;

(* Nesting and scope. There should be 2 termination conditions extracted. *)
Rfunction "k" `Empty`
  `(k 0 = 0) /\
   (k (SUC n) = let x = k 1 
                in (0=1) => k 2 | n)`;

(* Overlapping patterns *)
Rfunction "Foo" 
          `Empty`
   `(Foo(0,x) = x) /\ 
    (Foo(x,0) = Foo(0,0))`;

(* Should fail on repeated variables. *)
Lib.try (Rfunction "And_def"
              `inv_image list_pred SND`)
  `(And(x:bool,[]) = x) /\
   (And(y, CONS y t) = And(y, t))`;
