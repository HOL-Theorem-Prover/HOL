(* taken from http://mlton.org/FunctionalRecordUpdate *)
structure FunctionalRecordUpdate =
struct

  fun $$ (a, f) = f a
  fun id x = x

  datatype ('a, 'b) product = & of 'a * 'b
  infix &

  structure Fold =
  struct
    fun fold (a, f) g = g (a, f)
    fun step0 h (a, f) = fold (h a, f)
  end

  datatype ('x, 'y) u = X of 'x | Y of 'y

  val makeUpdate =
         fn z =>
         Fold.fold
         (((), (),
           fn f => f o X,
           fn (a, u) => case u of X x => x | _ => a),
          fn (p, up, _, _) => fn (p2r, p2r', r2p) => fn r =>
          Fold.fold ((p2r' (p id), up, r2p r),
                     fn (_, _, p) => p2r p))
         z

  val A =
         fn z =>
         Fold.step0
         (fn (_, _, p, up) =>
          (p, up, fn f => p (f o X) & (f o Y),
           fn (a & b, u) =>
           (case u of X x => up (a, x) | _ => a)
           & (case u of Y y => y | _ => b)))
         z

  fun makeUpdate2 z = makeUpdate A A $$ z
  fun makeUpdate3 z = makeUpdate A A A $$ z
  fun makeUpdate4 z = makeUpdate A A A A $$ z

  fun U s v = Fold.step0 (fn (r, up, p) => (r, up, up (p, s r v)))
end
