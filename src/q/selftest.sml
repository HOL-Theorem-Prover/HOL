open Parse boolLib HolKernel testutils

val _ = tprint "Testing Q.EXISTS ... "

val th = Q.EXISTS (`?f. f T T = T`, `$/\`) (REWRITE_CONV [] ``T /\ T``)
         handle HOL_ERR _ => die "FAILED!"

val _ = OK()

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
            [a] => if aconv a asm then OK() else die "FAILED!"
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
                           OK())
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_RENAME_TAC 2"
val glmrt2 = ([] : term list, ``f ((h : 'a -> 'b) s) = s``)
val expected_mrt2 = ``(f : 'b -> 'a) z = v``
val (sgs, _) = Q.MATCH_RENAME_TAC `f z = v` glmrt2
val _ = case sgs of
            [([], c)] => (aconvdie "conclusion" c expected_mrt2; OK())
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_RENAME_TAC 3"
val glmrt3 = ([] : term list, ``f zero zero = (z:'a)``)
val expected_mrt3 = ``f (a:num) a = (u:'a)``
val (sgs, _) = Q.MATCH_RENAME_TAC `f b a = u` glmrt3
val _ = case sgs of
            [([], c)] => (aconvdie "conclusion" c expected_mrt3; OK())
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
              OK()
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
              OK()
            end
          | _ => die "FAILED! (new goal of wrong shape)"

val _ = tprint "Q.MATCH_GOALSUB_RENAME_TAC 1"
val gl1 = ([] : term list,
          ``!x. x * SUC (SUC zero) < y * (z + SUC zero) * (y + a)``)
val expected_result1 =
    ``!x. x * SUC (SUC zero) < y * (z + SUC zero) * (y + c)``
val (sgs, _) = Q.MATCH_GOALSUB_RENAME_TAC `y + c` gl1
val _ = case sgs of
            [([], t)] => (aconvdie "goal" t expected_result1; OK())
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_GOALSUB_ABBREV_TAC 1"
val gl1 = ([] : term list,
          ``!x. x * SUC (SUC zero) < y * (z + SUC zero) * (y + a)``)
val expected_result1 =
    ``!x. x * SUC (SUC zero) < y * s * (y + a)``
val expected_abbrev =
    ``Abbrev(s = z + SUC zero)``
val (sgs, _) = Q.MATCH_GOALSUB_ABBREV_TAC `y * s` gl1
val _ = case sgs of
            [([a], t)] => (aconvdie "assumption" a expected_abbrev;
                           aconvdie "goal" t expected_result1;
                           OK())
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_GOALSUB_RENAME_TAC 2"
val gl2 = ([] : term list,
           ``!x. x * SUC zero < y * (z + SUC zero) * (z + SUC (SUC zero))``)
val expected_result2 = ``!x. x * c < y * (a + c) * (a + SUC c)``
val (sgs, _) = Q.MATCH_GOALSUB_RENAME_TAC `a + c` gl2
val _ = case sgs of
            [([], t)] =>
              (aconvdie "goal conclusion" t expected_result2; OK())
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_GOALSUB_RENAME_TAC 3"
val gl2a = ([] : term list, ``!x. x * SUC zero < z``)
val expected_result2a = #2 gl2a
val (sgs, _) = Q.MATCH_GOALSUB_RENAME_TAC `SUC` gl2a
val _ = case sgs of
            [([], t)] =>
              (aconvdie "goal conclusion" t expected_result2a; OK())
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
                                OK())
          | _ => die "FAILED!"

val _ = tprint "Q.MATCH_ASMSUB_ABBREV_TAC 1"
val gl3 = ([``P (x:num): bool``, ``Q (x < SUC (SUC (SUC zero))) : bool``],
           ``x + y < SUC (SUC zero)``);
val expected_a1 = ``Abbrev(two = SUC (SUC zero))``
val expected_a2 = ``P (x:num) : bool``
val expected_a3 = ``Q (x < SUC two) : bool``
val expected_c = ``x + y < two``
val (sgs, _) = Q.MATCH_ASMSUB_ABBREV_TAC `x < _ two` gl3
val _ = case sgs of
            [([a1, a2, a3], c)] =>
              (aconvdie "assumption #1" a1 expected_a1;
               aconvdie "assumption #2" a2 expected_a2;
               aconvdie "assumption #3" a3 expected_a3;
               aconvdie "goal conclusion" c expected_c;
               OK())
          | _ => die "FAILED!"

val _ = tprint "Q.PAT_ABBREV_TAC (gh252)"
val (sgs, _) = Q.PAT_ABBREV_TAC `v = I x` ([], ``I p /\ v``)
val _ = OK()

fun shouldfail f x =
  (f x ; die "FAILED!") handle HOL_ERR _ => OK()

val _ = tprint "Q.PAT_ABBREV_TAC (gh262) 1"
val (sgs, _) =
    Q.PAT_ABBREV_TAC `v = (x < SUC w)` ([], ``y < SUC zero ==> y < z``)
val _ = case sgs of
            [([abb], sg)] =>
            if Term.aconv abb ``Abbrev(v = y < SUC zero)`` andalso
               Term.aconv sg ``v ==> y < z``
            then OK()
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
            then OK()
            else die "FAILED!"
          | _ => die "FAILED!"

val _ = tprint "Q.PAT_ABBREV_TAC (gh262) 6"
val (sgs,_) = Q.PAT_ABBREV_TAC `v = (x < SUC z)`
                  ([], ``(!x. x < SUC zero) /\ u < SUC (SUC zero)``)
val _ = case sgs of
            [([abb], sg)] =>
            if Term.aconv abb ``Abbrev (v = u < SUC (SUC zero))`` andalso
               Term.aconv sg ``(!y. y < SUC zero) /\ v``
            then OK()
            else die "FAILED!"
          | _ => die "FAILED!"

fun tactest (nm, tac, g, expected) =
  let
    val _ = tprint nm
    val (sgs, _) = tac g
  in
    if list_compare (pair_compare(list_compare Term.compare, Term.compare))
                    (sgs, expected) = EQUAL
    then
      OK()
    else die "FAILED!"
  end

val fa_y = ``!y:'a. P y``
val fa_n = ``!n:num. SUC n < zero``
val _ = new_type ("int", 0)
val _ = new_constant ("int_plus1", ``:int -> int``)
val fa_i = ``!i:int. Q i``
val _ = overload_on("SUC", ``int_plus1``)
val _ = List.app tactest [
         ("Q.SPEC_THEN 1", FIRST_X_ASSUM (Q.SPEC_THEN `x` MP_TAC),
          ([fa_y, fa_n], ``x < x``),
          [([fa_y], ``SUC x < zero ==> x < x``)]),

         ("Q.SPEC_THEN 2", FIRST_X_ASSUM (Q.SPEC_THEN `SUC x` MP_TAC),
          ([fa_y, fa_n], ``x < f (y:int)``),
          [([fa_y], ``SUC (SUC x) < zero ==> x < f (y:int)``)]),

         ("Q.SPEC_THEN 3", FIRST_X_ASSUM (Q.SPEC_THEN `SUC j` MP_TAC),
          ([fa_y, fa_i, fa_n], ``x < f (y:int)``),
          [([fa_y, fa_n], ``Q (int_plus1 j) ==> x < f (y:int)``)]),

         ("Q.SPECL_THEN 1", FIRST_X_ASSUM (Q.SPECL_THEN [`SUC x`, `x`] MP_TAC),
          ([fa_y, fa_n, ``!j k. j < k``], ``x < x``),
          [([fa_y, fa_n], ``SUC x < x ==> x < x``)]),

         ("Q.SPECL_THEN 2", FIRST_X_ASSUM (Q.SPECL_THEN [`SUC x`, `x`] MP_TAC),
          ([fa_y, fa_n, fa_i, ``!j k. j < k``], ``x < x``),
          [([fa_y, fa_n, fa_i], ``SUC x < x ==> x < x``)]),

         ("Q.SPECL_THEN 3", FIRST_X_ASSUM (Q.SPECL_THEN [`SUC x`, `x`] MP_TAC),
          ([fa_y, fa_n, fa_i, ``!j (k:int). j < f k``, ``!a b. a < b``],
           ``x < x``),
          [([fa_y, fa_n, fa_i, ``!j (k:int). j < f k``],
           ``SUC x < x ==> x < x``)]),

         ("Q.SPECL_THEN 4", FIRST_X_ASSUM (Q.SPECL_THEN [`SUC x`, `j`] MP_TAC),
          ([fa_y, fa_n, fa_i, ``!j (k:int). j < f k``, ``!a b. a < b``],
           ``x < x``),
          [([fa_y, fa_n, fa_i, ``!a b. a < b``],
           ``SUC x < f (j:int) ==> x < x``)])
    ]

val _ = tprint "Q.GENL variable order"
val vnms = ASSUME ``!x:'a y:'a z:'a. P x y z``
              |> SPEC_ALL
              |> Q.GENL [`x`, `y`, `z`]
              |> concl |> strip_forall |> #1 |> map (#1 o dest_var)
val _ = if vnms = ["x", "y", "z"] then OK() else die "FAILED!"

val _ = tprint "Q.MATCH_RENAME_TAC on overloads"
val foo1_def = new_definition("foo1_def", ``foo1 x y z = (x ==> y /\ z)``);
val foo2_def = new_definition("foo2_def", ``foo2 x y z = (x ==> y \/ z)``);
val _ = overload_on("foo", ``foo1``);
val _ = overload_on("foo", ``foo2``);

val th = TAC_PROOF(([], ``foo1 F x y``),
               Q.MATCH_RENAME_TAC `foo F a b` >>
               REWRITE_TAC [foo1_def]) handle HOL_ERR _ => die "FAILED!"
val _ = OK()

val _ = tprint "Q.RENAME1 on overloads"
val th = TAC_PROOF(([], ``?v. foo1 v x y``),
                   Q.RENAME1_TAC `foo _ a b` >>
                   Q.EXISTS_TAC `F` >>
                   REWRITE_TAC [foo1_def]) handle HOL_ERR _ => die "FAILED!"
val _ = OK()

val _ = tprint "Q.kRENAME_TAC(1)"
val th = TAC_PROOF (([``foo1 a b c``, ``foo2 d e f``], ``?x y z. foo1 x y z``),
                    Q.kRENAME_TAC [`foo u v w`]
                                  (MAP_EVERY Q.EXISTS_TAC [`u`, `v`, `w`] THEN
                                   FIRST_ASSUM ACCEPT_TAC))
                   handle HOL_ERR _ => die "FAILED!"
val _ = OK()

val _ = tprint "Q.kRENAME_TAC(2)"
val th = TAC_PROOF (([``foo2 a b c``, ``foo1 d e f``], ``?x y z. foo1 x y z``),
                    Q.kRENAME_TAC [`foo u v w`]
                                  (MAP_EVERY Q.EXISTS_TAC [`u`, `v`, `w`] THEN
                                   FIRST_ASSUM ACCEPT_TAC))
                   handle HOL_ERR _ => die "FAILED!"
val _ = OK()

val _ = tprint "PAT_ABBREV_TAC respects Parse.hide"
val _ = new_definition ("gh431_def", ``gh431 x = ~x``);
val _ = hide "gh431"
val th = (Q.PAT_ABBREV_TAC `gh431 = T` THEN Q.UNABBREV_TAC `gh431` THEN
          REWRITE_TAC [])
         ([], ``p /\ T = p``) handle HOL_ERR _ => die "FAILED\n"
val _ = OK()

val _ = new_definition ("gh425a_def", ``gh425a a = a``);
val _ = new_definition ("gh425b_def", ``gh425b p = (p ==> T)``);
val _ = overload_on ("gh425", ``gh425a``);
val _ = overload_on ("gh425", ``gh425b``);
val buf = ref ([] : string list)
fun app s = buf := s :: !buf
fun testquiet f x =
  (buf := [];
   let val result =
           (Lib.with_flag (Feedback.MESG_outstream, app) o
            Lib.with_flag (Feedback.ERR_outstream, app) o
            Lib.with_flag (Feedback.WARNING_outstream, app) o
            Lib.with_flag (Globals.interactive, true)) (Lib.total f) x
       val _ =
           null (!buf) orelse
           die ("\n  FAILED : buf contains " ^ String.concatWith "\n" (!buf))
   in
     result
   end);

val _ = tprint "(Interactive) PAT_ASSUM quiet about tyvar guesses(1)"
val result = testquiet
                 (Q.PAT_X_ASSUM `gh425a (g x)` mp_tac)
                 ([``gh425a (f T) : bool``], ``p /\ q``)
val _ = case result of
            SOME ([([], t)],_) =>
              if aconv t ``gh425a (f T) ==> p /\ q`` then OK()
              else die "\nFAILED - Incorrect result"
          | _ => die "\nFAILED - Incorrect result"

val _ = tprint "(Interactive) PAT_ASSUM quiet about tyvar guesses(2)"
val _ = testquiet
                 (Q.PAT_X_ASSUM `gh245 (g x)` mp_tac)
                 ([``gh425a (f T) : bool``], ``p /\ q``)
val _ = OK()

val _ = tprint "(Interactive) PAT_ASSUM quiet about tyvar guesses(3)"
val _ = testquiet
                 (Q.PAT_X_ASSUM `gh245 x` mp_tac)
                 ([``gh425b (f T) : bool``], ``p /\ q``)
val _ = OK()

val _ = tprint "(Interactive) RENAME_TAC quiet about tyvar guesses(1)"
val _ = testquiet (Q.RENAME_TAC [‘f x /\ _’])
                  ([], “(gg : num -> bool) n /\ p”)
val _ = OK()

val _ = tprint "(Interactive) RENAME_TAC quiet about tyvar guesses(2)"
val _ = testquiet (Q.RENAME_TAC [‘SUC n’]) ([], “p /\ q”)
val _ = OK()

val _ = tprint "(Interactive) RENAME_TAC quiet about tyvar guesses(3)"
val _ = testquiet (Q.RENAME_TAC [‘SUC n’]) ([“P (SUC x) ==> Q”], “p /\ q”)
val _ = OK()

val _ = tprint "(Interactive) RENAME_TAC quiet about tyvar guesses(4)"
val _ = testquiet (Q.RENAME_TAC [‘SUC n’]) ([“Pr ==> Q”], “P (SUC x) /\ q”)
val _ = OK()


val _ = Process.exit Process.success;
