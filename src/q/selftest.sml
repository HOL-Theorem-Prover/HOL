open Parse boolLib HolKernel testutils

val _ = tprint "Testing Q.EXISTS ... "

val th = Q.EXISTS (`?f. f T T = T`, `$/\`) (REWRITE_CONV [] ``T /\ T``)
         handle HOL_ERR _ => die "FAILED!"

val _ = print "OK\n"

val _ = tprint "Testing Q.REFINE_EXISTS_TAC"

val asm = ``!x1:'a x2:'a y1:'b y2:'b. (f x1 y1:'c = f x2 y2) <=> (x1 = x2) /\ (y1 = y2)``
val goal = ``?a:'c b:'d. Q a b``
val (sgs, vfn) = Q.REFINE_EXISTS_TAC `f x y` ([asm], goal)
                 handle _ => die "FAILED!"
val expected_sg = ``?x:'a y:'b b:'d. Q (f x y:'c) b``
val result =
    case sgs of
      [g as ([a],g')] => if aconv a asm andalso aconv g' expected_sg
                         then vfn [mk_thm g]
                         else die "FAILED!"
     | _ => die "FAILED!"
val _ = if aconv (concl result) goal then
          case hyp result of
            [a] => if aconv a asm then print "OK\n" else die "FAILED!"
           | _ => die "FAILED!"
        else die "FAILED!"

(* fake arithmetic *)
val _ = new_type ("num", 0)
val _ = new_constant ("*", ``:num -> num -> num``)
val _ = new_constant ("+", ``:num -> num -> num``)
val _ = new_constant ("<", ``:num -> num -> bool``)
val _ = new_constant ("SUC", ``:num -> num``)
val _ = new_constant ("zero", ``:num``)
val _ = set_fixity "+" (Infixl 500)
val _ = set_fixity "*" (Infixl 600)
val _ = set_fixity "<" (Infix(NONASSOC, 450))

val _ = tprint "Q.MATCH_GOALSUB_RENAME_TAC 1"
val gl1 = ([] : term list,
          ``!x. x * SUC (SUC zero) < y * (z + SUC zero) * (y + a)``)
val expected_result1 =
    ``!x. x * SUC (SUC zero) < y * (z + SUC zero) * (y + c)``
val (sgs, _) = Q.MATCH_GOALSUB_RENAME_TAC `y + c` [] gl1
val _ = case sgs of
            [([], t)] => if aconv t expected_result1 then print "OK\n"
                         else die "FAILED!"
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_GOALSUB_RENAME_TAC 2"
val gl2 = ([] : term list,
           ``!x. x * SUC zero < y * (z + SUC zero) * (z + SUC (SUC zero))``)
val expected_result2 = ``!x. x * c < y * (a + c) * (a + SUC c)``
val (sgs, _) = Q.MATCH_GOALSUB_RENAME_TAC `a + c` [] gl2
val _ = case sgs of
            [([], t)] => if aconv t expected_result2 then print "OK\n"
                         else die "FAILED!"
          | _ => die "FAILED!"

val _ = Process.exit Process.success;
