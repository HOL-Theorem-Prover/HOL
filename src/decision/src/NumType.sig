signature NumType =
sig
   type num = arbint.int
   val num0 : num
   val num1 : num
   val + : num * num -> num
   val - : num * num -> num
   val * : num * num -> num
   val div : num * num -> num
   val lcm : num * num -> num
   val < : num * num -> bool
end;

