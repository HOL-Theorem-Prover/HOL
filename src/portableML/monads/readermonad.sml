structure readermonad :> readermonad =
struct

  infix >- >>
  type ('s,'b) t = 's -> 'b
  fun return x s = x

  fun (m1 >- f) s = f (m1 s) s
  fun (m1 >> m2) = m1 >- (fn _ => m2)

end
