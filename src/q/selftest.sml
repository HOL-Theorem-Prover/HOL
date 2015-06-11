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

(* combinator *)
val _ = new_definition("I_DEF", ``I = \x:'a. x``);

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

fun aconvdie m t1 t2 = aconv t1 t2 orelse die ("FAILED! (" ^ m ^ " wrong)")

val _ = tprint "Q.MATCH_RENAME_TAC 1"
val gl0 = ([``x < y``], ``x = z:num``)
val expected_a0 = ``a < y``
val expected_c0 = ``a = b:num``
val (sgs, _) = Q.MATCH_RENAME_TAC `a = b` gl0
val _ = case sgs of
            [([a], c)] => (aconvdie "assumption" a expected_a0;
                           aconvdie "goal" c expected_c0;
                           print "OK\n")
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_RENAME_TAC 2"
val glmrt2 = ([] : term list, ``f ((h : 'a -> 'b) s) = s``)
val expected_mrt2 = ``(f : 'b -> 'a) z = v``
val (sgs, _) = Q.MATCH_RENAME_TAC `f z = v` glmrt2
val _ = case sgs of
            [([], c)] => (aconvdie "conclusion" c expected_mrt2; print "OK\n")
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_RENAME_TAC 3"
val glmrt3 = ([] : term list, ``f zero zero = (z:'a)``)
val expected_mrt3 = ``f (a:num) a = (u:'a)``
val (sgs, _) = Q.MATCH_RENAME_TAC `f b a = u` glmrt3
val _ = case sgs of
            [([], c)] => (aconvdie "conclusion" c expected_mrt3; print "OK\n")
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_ABBREV_TAC 1"
val expected_mat1c = ``f (a:num) a = (u:'a)``
val expected_mat1a1 = ``Abbrev (b = zero)``
val expected_mat1a2 = ``Abbrev (a:num = b)``
val expected_mat1a3 = ``Abbrev (u:'a = z)``
val (sgs, _) = Q.MATCH_ABBREV_TAC `f b a = u` glmrt3
val _ = case sgs of
            [([a1,a2,a3], c)] =>
            let
              val _ = aconvdie "assumption #1" a1 expected_mat1a1
              val _ = aconvdie "assumption #2" a2 expected_mat1a2
              val _ = aconvdie "assumption #3" a3 expected_mat1a3
              val _ = aconvdie "goal conclusion" c expected_mat1c
            in
              print "OK\n"
            end
          | _ => die "FAILED! (new goal of wrong shape)"

val _ = tprint "Q.MATCH_ABBREV_TAC 2"
val expected_mat2c = ``(f : 'b -> 'a) z = v``
(* first assumption is most recently created *)
val expected_mat2a1 = ``Abbrev(v : 'a = s)``
val expected_mat2a2 = ``Abbrev(z :'b = h (v:'a))``
val (sgs, _) = Q.MATCH_ABBREV_TAC `f z = v` glmrt2
val _ = case sgs of
            [([a1, a2], c)] =>
            let
              val _ = aconvdie "goal conclusion" c expected_mat2c
              val _ = aconvdie "assumption #1" a1 expected_mat2a1
              val _ = aconvdie "assumption #2" a2 expected_mat2a2
            in
              print "OK\n"
            end
          | _ => die "FAILED! (new goal of wrong shape)"

val _ = tprint "Q.MATCH_GOALSUB_RENAME_TAC 1"
val gl1 = ([] : term list,
          ``!x. x * SUC (SUC zero) < y * (z + SUC zero) * (y + a)``)
val expected_result1 =
    ``!x. x * SUC (SUC zero) < y * (z + SUC zero) * (y + c)``
val (sgs, _) = Q.MATCH_GOALSUB_RENAME_TAC `y + c` gl1
val _ = case sgs of
            [([], t)] => (aconvdie "goal" t expected_result1; print "OK\n")
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_GOALSUB_RENAME_TAC 2"
val gl2 = ([] : term list,
           ``!x. x * SUC zero < y * (z + SUC zero) * (z + SUC (SUC zero))``)
val expected_result2 = ``!x. x * c < y * (a + c) * (a + SUC c)``
val (sgs, _) = Q.MATCH_GOALSUB_RENAME_TAC `a + c` gl2
val _ = case sgs of
            [([], t)] =>
              (aconvdie "goal conclusion" t expected_result2; print "OK\n")
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_GOALSUB_RENAME_TAC 3"
val gl2a = ([] : term list, ``!x. x * SUC zero < z``)
val expected_result2a = #2 gl2a
val (sgs, _) = Q.MATCH_GOALSUB_RENAME_TAC `SUC` gl2a
val _ = case sgs of
            [([], t)] =>
              (aconvdie "goal conclusion" t expected_result2a; print "OK\n")
          | _ => die "FAILED!"


val _ = tprint "Q.MATCH_ASMSUB_RENAME_TAC 1"
val gl3 = ([``P (x:num): bool``, ``Q (x < SUC (SUC (SUC zero))) : bool``],
           ``x + y < SUC (SUC zero)``);
val expected_a1 = ``P (x:num) : bool``
val expected_a2 = ``Q (x < n) : bool``
val expected_c = ``x + y < SUC (SUC zero)``
val (sgs, _) = Q.MATCH_ASMSUB_RENAME_TAC `x < n` gl3
val _ = case sgs of
            [([a1, a2], c)] => (aconvdie "assumption #1" a1 expected_a1;
                                aconvdie "assumption #2" a2 expected_a2;
                                aconvdie "goal conclusion" c expected_c;
                                print "OK\n")
          | _ => die "FAILED!"


val _ = tprint "Q.PAT_ABBREV_TAC (gh252)"
val (sgs, _) = Q.PAT_ABBREV_TAC `v = I x` ([], ``I p /\ v``)
val _ = print "OK\n"

fun shouldfail f x =
  (f x ; die "FAILED!") handle HOL_ERR _ => print "OK\n"

val _ = tprint "Q.PAT_ABBREV_TAC (gh262) 1"
val (sgs, _) =
    Q.PAT_ABBREV_TAC `v = (x < SUC w)` ([], ``y < SUC zero ==> y < z``)
val _ = case sgs of
            [([abb], sg)] =>
            if Term.aconv abb ``Abbrev(v = y < SUC zero)`` andalso
               Term.aconv sg ``v ==> y < z``
            then print "OK\n"
            else die "FAILED!"
          | _ => die "FAILED!"

val _ = tprint "Q.PAT_ABBREV_TAC (gh262) 2"
val _ = shouldfail (Q.PAT_ABBREV_TAC `v = (x < SUC z)`)
                   ([], ``!x. x < SUC zero``)

val _ = tprint "Q.PAT_ABBREV_TAC (gh262) 3"
val _ = shouldfail (Q.PAT_ABBREV_TAC `v = (x < SUC z)`)
                   ([], ``!y. y < SUC zero``)

val _ = tprint "Q.PAT_ABBREV_TAC (gh262) 4"
val _ = shouldfail (Q.PAT_ABBREV_TAC `v = (x < SUC z)`)
                   ([], ``(!y. y < SUC zero) /\ y < zero``)

val _ = tprint "Q.PAT_ABBREV_TAC (gh262) 5"
val (sgs,_) = Q.PAT_ABBREV_TAC `v = (x < SUC z)`
                  ([], ``(!y. y < SUC zero) /\ u < SUC (SUC zero)``)
val _ = case sgs of
            [([abb], sg)] =>
            if Term.aconv abb ``Abbrev (v = u < SUC (SUC zero))`` andalso
               Term.aconv sg ``(!y. y < SUC zero) /\ v``
            then print "OK\n"
            else die "FAILED!"
          | _ => die "FAILED!"

val _ = tprint "Q.PAT_ABBREV_TAC (gh262) 6"
val (sgs,_) = Q.PAT_ABBREV_TAC `v = (x < SUC z)`
                  ([], ``(!x. x < SUC zero) /\ u < SUC (SUC zero)``)
val _ = case sgs of
            [([abb], sg)] =>
            if Term.aconv abb ``Abbrev (v = u < SUC (SUC zero))`` andalso
               Term.aconv sg ``(!y. y < SUC zero) /\ v``
            then print "OK\n"
            else die "FAILED!"
          | _ => die "FAILED!"

val _ = Process.exit Process.success;
