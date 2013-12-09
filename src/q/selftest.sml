open Parse boolLib HolKernel

fun tprint s = print (StringCvt.padRight #" " 65 s)
fun die() = (print "FAILED!\n"; Process.exit Process.failure)
val _ = tprint "Testing Q.EXISTS ... "

val th = Q.EXISTS (`?f. f T T = T`, `$/\`) (REWRITE_CONV [] ``T /\ T``)
         handle HOL_ERR _ => die()

val _ = print "OK\n"

val _ = tprint "Testing Q.REFINE_EXISTS_TAC"

val asm = ``!x1:'a x2:'a y1:'b y2:'b. (f x1 y1:'c = f x2 y2) <=> (x1 = x2) /\ (y1 = y2)``
val goal = ``?a:'c b:'d. Q a b``
val (sgs, vfn) = Q.REFINE_EXISTS_TAC `f x y` ([asm], goal) handle _ => die()
val expected_sg = ``?x:'a y:'b b:'d. Q (f x y:'c) b``
val result =
    case sgs of
      [g as ([a],g')] => if aconv a asm andalso aconv g' expected_sg
                         then vfn [mk_thm g]
                         else die()
     | _ => die()
val _ = if aconv (concl result) goal then
          case hyp result of
            [a] => if aconv a asm then print "OK\n" else die()
           | _ => die()
        else die()

val _ = Process.exit Process.success;
