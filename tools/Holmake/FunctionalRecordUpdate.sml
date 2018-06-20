(* From http://www.mlton.org/FunctionalRecordUpdate *)
structure FunctionalRecordUpdate =
struct
local
  fun next g (f, z) x = g (f x, z)
  fun  f1 (f, z) x = f (z x)
  fun  f2 z = next  f1 z
  fun  f3 z = next  f2 z
  fun  f4 z = next  f3 z
  fun  f5 z = next  f4 z
  fun  f6 z = next  f5 z
  fun  f7 z = next  f6 z
  fun  f8 z = next  f7 z
  fun  f9 z = next  f8 z
  fun f10 z = next  f9 z
  fun f11 z = next f10 z
  fun f12 z = next f11 z
  fun f13 z = next f12 z
  fun f14 z = next f13 z
  fun f15 z = next f14 z
  fun f16 z = next f15 z
  fun f17 z = next f16 z
  fun f18 z = next f17 z
  fun f19 z = next f18 z
  fun f20 z = next f19 z
  fun f21 z = next f20 z
  fun f22 z = next f21 z
  fun f23 z = next f22 z
  fun f24 z = next f23 z

  fun  c0 from =  from
  fun  c1 from =  c0 (from  f1)
  fun  c2 from =  c1 (from  f2)
  fun  c3 from =  c2 (from  f3)
  fun  c4 from =  c3 (from  f4)
  fun  c5 from =  c4 (from  f5)
  fun  c6 from =  c5 (from  f6)
  fun  c7 from =  c6 (from  f7)
  fun  c8 from =  c7 (from  f8)
  fun  c9 from =  c8 (from  f9)
  fun c10 from =  c9 (from f10)
  fun c11 from = c10 (from f11)
  fun c12 from = c11 (from f12)
  fun c13 from = c12 (from f13)
  fun c14 from = c13 (from f14)
  fun c15 from = c14 (from f15)
  fun c16 from = c15 (from f16)
  fun c17 from = c16 (from f17)
  fun c18 from = c17 (from f18)
  fun c19 from = c18 (from f19)
  fun c20 from = c19 (from f20)
  fun c21 from = c20 (from f21)
  fun c22 from = c21 (from f22)
  fun c23 from = c22 (from f23)
  fun c24 from = c23 (from f24)
in

structure Fold =
struct
  fun fold (a,f) g = g (a,f)
  fun step0 h (a,f) =  fold (h a, f)
  fun step1 h (a,f) b = fold (h (b,a), f)
  fun step2 h (a,f) b c = fold (h (b,c,a), f)
end

fun makeUpdate cX (from, from', to) record =
    let
      fun ops () = cX from'
      fun vars f = to f record
    in
      Fold.fold ((vars, ops), fn (vars, _) => vars from)
    end

fun  makeUpdate0 z = makeUpdate  c0 z
fun  makeUpdate1 z = makeUpdate  c1 z
fun  makeUpdate2 z = makeUpdate  c2 z
fun  makeUpdate3 z = makeUpdate  c3 z
fun  makeUpdate4 z = makeUpdate  c4 z
fun  makeUpdate5 z = makeUpdate  c5 z
fun  makeUpdate6 z = makeUpdate  c6 z
fun  makeUpdate7 z = makeUpdate  c7 z
fun  makeUpdate8 z = makeUpdate  c8 z
fun  makeUpdate9 z = makeUpdate  c9 z
fun makeUpdate10 z = makeUpdate c10 z
fun makeUpdate11 z = makeUpdate c11 z
fun makeUpdate12 z = makeUpdate c12 z
fun makeUpdate13 z = makeUpdate c13 z
fun makeUpdate14 z = makeUpdate c14 z
fun makeUpdate15 z = makeUpdate c15 z
fun makeUpdate16 z = makeUpdate c16 z
fun makeUpdate17 z = makeUpdate c17 z
fun makeUpdate18 z = makeUpdate c18 z
fun makeUpdate19 z = makeUpdate c19 z
fun makeUpdate20 z = makeUpdate c20 z
fun makeUpdate21 z = makeUpdate c21 z
fun makeUpdate22 z = makeUpdate c22 z
fun makeUpdate23 z = makeUpdate c23 z
fun makeUpdate24 z = makeUpdate c24 z

fun $$ (a,f) = f a
fun U s v z =
    Fold.step0 (fn (vars,ops) =>
                   (fn out => vars (s (ops()) (out,fn _ => v)),ops))
               z
end (* local *)

end (* struct *)
