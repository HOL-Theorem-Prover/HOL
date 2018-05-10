% Recursive Quicksort %

letrec quicksort l =
 (let x.l' = l in
  let l1,l2 = partition (curry $> x) l' in
  quicksort l1 @ [x] @ quicksort l2
 ) ? l;;

% The combinator list_fun_def below can be used to generate quicksort.

  If  f = list_fun_def(x,fun,[f1;...;fn])  then:

   f [] = x
   f l  = fun  [f(f1 l);...;f(fn l)]    (if l is not [])
%

letrec list_fun_def (x,fn,fnl) l =
 if null l 
 then x
 else fn
       l
       (map
         (\f. list_fun_def (x,fn,fnl) (f l))
         fnl)
;;

let quicksort =
 list_fun_def
 ([],
  (\l [l1;l2]. l1 @ [hd l] @ l2),
  [(\(x.l'). filter(curry $> x) l');
   (\(x.l'). filter($not o (curry $> x)) l')]);;

% The function list_fun_def_functional should satisfy:

  |- !x fn fnl. ALL_MONO fnl ==> ?F. F = list_fun_def_functional(x,fn,fnl) F

  (where ALL_MONO is a predicate on lists of functions that is true if every
   function f in the list satisfies |- !x. length(f x) < length x ).

 The F so produced is list_fun_def(x,fn,fnl), so in HOL we could define:

  |-  list_fun_def(x,fn,fnl) = FIX(list_fun_def_functional(x,fn,fnl))

 where:

  |- FIX F = @f. f = F f
%

let list_fun_def_functional (x,fn,fnl) F l =
 if null l 
 then x
 else fn l (map (\f. F (f l)) fnl) ;;

letrec quicksort l =
 list_fun_def_functional
 ([],
  (\l [l1;l2]. l1 @ [hd l] @ l2),
  [(\(x.l'). filter(curry $> x) l');
   (\(x.l'). filter($not o (curry $> x)) l')])
 quicksort
 l
;;
