signature parse_bnf =
sig

  val parse2ftor : ParseDatatype.AST list -> (string * bnfBase_dtype.bnftor) list

end

(* Example behaviour:

given:

  foo = fnil | fc ('a -> foo) (bar list) ;  (* one forward ref, one recursive *)
  bar = bc1 num | bc2 (foo + num) | bc3 qux 'd raz;  (* two forward refs *)
  qux = qc1 | qc2 foo
  raz = rc1 bar | rc2 qux

we want to generate the following functor equations to satisfy:

  foo0 = 1 + ('a -> foo0) * 'bar list

After this point, foo0 is a binary tyop because the bar position is taken by
a type variable.  References to foo in subsequent equations need to be replaced
by
  ('a, ??) foo0
where ?? is the "current encoding" for bar, which at this point could be taken
to be 'bar.

Moving onto the equation for bar, we update bar so that it points at bar0,
giving

  bar0 = num + (('a,bar0)foo0 + num) + 'qux * 'd * 'raz

making bar0 a 4-nary tyop, with genuine type variables 'a and 'd, and the
rest to be taken by "current encodings" for qux and raz.  At this point,
the "current encodings" are:

   foo |->  ('a, ('a,'d,'qux,'raz) bar0) foo0
   bar |->  ('a,'d,'qux,'raz) bar0

Next, we have to do

  qux0 = 1 + ('a, ('a,'d,qux0,'raz) bar0) foo0

This makes qux0 a ternary operator, and we get

   foo |->  ('a, ('a, 'd, ('a,'d,'raz) qux0, 'raz) bar0) foo0
   bar |->  ('a,'d,('a,'d,'raz)qux0,'raz) bar0
   qux |->  ('a,'d,'raz) qux0

So the last equation to solve is

   raz0 = ('a,'d,('a,'d,raz0)qux0,raz0) bar0 + ('a,'d,raz0)qux0

making raz a binary operator, and giving final instantiations:

  foo |-> ('a, ('a,'d,('a,'d,('a,'d)raz0) qux0, ('a,'d) raz0) bar) foo0
  bar |-> ('a, 'd, ('a,'d,('a,'d)raz0)qux0, ('a,'d)raz0) bar0
  qux |-> ('a,'d,('a,'d)raz0) qux0
  raz |-> ('a,'d)raz0


*)
