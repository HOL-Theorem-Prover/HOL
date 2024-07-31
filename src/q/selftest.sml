open Parse boolLib HolKernel testutils

val _ = tprint "Testing Q.EXISTS ... "
val _ = require (check_result (fn _ => true))
                (Q.EXISTS (`?f. f T T = T`, `$/\`))
                (REWRITE_CONV [] “T /\ T”)

exception InternalDie of string
val _ = tprint "Testing Q.REFINE_EXISTS_TAC"
val _ = let
  val asm = “!x1:'a x2:'a y1:'b y2:'b.
                (f x1 y1:'c = f x2 y2) <=> (x1 = x2) /\ (y1 = y2)”
  val goal = ``?a:'c b:'d. Q a b``
  val (sgs, vfn) = Q.REFINE_EXISTS_TAC `f x y` ([asm], goal)
                   handle _ => raise InternalDie "FAILED!"
  val expected_sg = ``?x:'a y:'b b:'d. Q (f x y:'c) b``
  val result =
      case sgs of
          [g as ([a],g')] => if aconv a asm andalso aconv g' expected_sg
                             then vfn [mk_thm g]
                             else raise InternalDie "FAILED!"
        | _ => raise InternalDie "FAILED!"
in
  if aconv (concl result) goal then
    case hyp result of
        [a] => if aconv a asm then OK() else die "FAILED!"
      | _ => die "FAILED!"
  else die "FAILED!"
end handle InternalDie s => die s

(* fake arithmetic *)
val _ = new_type ("num", 0)
val _ = new_constant ("*", ``:num -> num -> num``)
val _ = new_constant ("+", ``:num -> num -> num``)
val _ = new_constant ("<", ``:num -> num -> bool``)
val _ = new_constant ("SUC", ``:num -> num``)
val _ = new_constant ("zero", ``:num``)
val _ = new_constant ("three", ``:num``)
val _ = new_constant ("five", ``:num``)
val _ = set_fixity "+" (Infixl 500)
val _ = set_fixity "*" (Infixl 600)
val _ = set_fixity "<" (Infix(NONASSOC, 450))

val _ = let
    val tests = [ (* triples of: (goal, quotations, expected (single) subgoal) *)
      (* Simple test *)
      (
        ([], ``∃n m. n + m = zero``),
        [`_`, `SUC l`] : term frag list list,
        ``∃l n. n + SUC l = zero``
      ),
      (* Concrete test *)
      (
        ([], ``∃n m. n + m = SUC zero``),
        [`_`, `SUC zero`] : term frag list list,
        ``∃n. n + SUC zero = SUC zero``
      ),
      (* Use variable in assumption *)
      (
        ([``l = zero``], ``∃n m. n + m = zero``),
        [`_`, `SUC l`],
        ``∃n. n + SUC l = zero``
      ),
      (* Witness var shadowing boundvar *)
      (
        ([], ``∃(a:'a) (b:'b). f a b``),
        [`b`,`_`],
        ``∃(b:'a) (b':'b). f b b'``
      ),
      (* Boundvar `c` shadowing freevar *)
      (
        ([``c = five``], ``∃n m c. n + m = c``),
        [`_`,`SUC c`],
        ``∃n c'. n + SUC c = c'``
      ),
      (* Shadowed boundvars *)
      (
        ([], ``∃(c:'a) (c:'b). P c``),
        [`_`,`new`],
        ``∃(new:'b) (c':'a). P new``
      ),
      (* Re-use term across quotations *)
      (
        ([], ``∃n m l. n + m + l = zero``),
        [`_`,`k`,`SUC k`],
        ``∃k n. n + k + SUC k = zero``
      ),
      (* Slightly more involved tests *)
      (
        ([``n = three``,``c = five``], ``∃a b c d. a + b = c + d``),
        [`_`,`SUC c`, `_`, `n + m`],
        ``∃m a c'. a + SUC c = c' + (n + m)``
      ),
      (
        ([``h x = x:'b``],
         ``∃(a:'a) (b:'b) (c:'c) (d:'d) (e:'e). f a b = g c d e :num``),
        [`_`, `h x`, `foo x`, `bar (foo : 'b -> 'c) : 'd`],
        ``∃(foo:'b -> 'c) (bar: ('b -> 'c) -> 'd) (a:'a) (e:'e).
            f a (h x : 'b) = g (foo x) (bar foo) e :num``
      ),
      (
        ([``P1 (x:'a) :bool``,``P2 (x':'b) :bool``,``P3 (x'':'c) :bool``],
         ``∃(x:'a) (x':'b) (y:'c) (x:'d). P x x' y``),
        [`_`,`Q x x' (x''':'d)`,`x''''`,`_`],
        ``∃(x'³':'d) (Q:'a -> 'b -> 'd -> 'b) (x'⁴':'c) (x'':'a) (x'':'d).
            P x'' (Q x x' x'³') x'⁴'``
      )
    ]
    fun checkSubgoals (expected_asms, expected_goal) (sgs, vld:validation)  =
      case sgs of
        [(asms,sg)] =>
           ListPair.allEq (uncurry aconv) (asms, expected_asms) andalso
           aconv sg expected_goal andalso
           (can vld (map mk_thm sgs) orelse
            (die "FAILED! Bad validation"; false))
      | _ => (die "FAILED! Too many subgoals produced"; false)
    fun test_single (input, qs, expected) =
        let
          val _ = tprint ("Q.LIST_REFINE_EXISTS_TAC: " ^
                          term_to_string (#2 input))
          open HOLPP
        in
          require_pretty_msg (check_result $ checkSubgoals (#1 input, expected))
                             (block CONSISTENT 0 o
                              pr_list goalStack.pp_goal
                                      [add_string ",", add_break(1,0)] o
                              fst)
                             (Q.LIST_REFINE_EXISTS_TAC qs)
                             input
        end
  in
    List.app test_single tests
  end

(* combinator *)
val _ = new_definition("I_DEF", ``I = \x:'a. x``);


fun aconvdie m t1 t2 =
    aconv t1 t2 orelse raise InternalDie ("FAILED! (" ^ m ^ " wrong)")

val _ = tprint "Q.MATCH_RENAME_TAC 1"
val glZ = ([``x < y``], ``x = z:num``)
val expected_aZ = ``a < y``
val expected_cZ = ``a = b:num``
val (sgs, _) = Q.MATCH_RENAME_TAC `a = b` glZ
val _ = (case sgs of
            [([a], c)] => (aconvdie "assumption" a expected_aZ;
                           aconvdie "goal" c expected_cZ;
                           OK())
          | _ => die "FAILED!")
        handle InternalDie s => die s

val _ = tprint "Q.MATCH_RENAME_TAC 2"
val glmrt2 = ([] : term list, ``f ((h : 'a -> 'b) s) = s``)
val expected_mrt2 = ``(f : 'b -> 'a) z = v``
val (sgs, _) = Q.MATCH_RENAME_TAC `f z = v` glmrt2
val _ = (case sgs of
             [([], c)] => (aconvdie "conclusion" c expected_mrt2; OK())
           | _ => die "FAILED!") handle InternalDie s => die s

val _ = tprint "Q.MATCH_RENAME_TAC 3"
val glmrt3 = ([] : term list, ``f zero zero = (z:'a)``)
val expected_mrt3 = ``f (a:num) a = (u:'a)``
val (sgs, _) = Q.MATCH_RENAME_TAC `f b a = u` glmrt3
val _ = (case sgs of
            [([], c)] => (aconvdie "conclusion" c expected_mrt3; OK())
          | _ => die "FAILED!") handle InternalDie s => die s

val _ = tprint "Q.MATCH_ABBREV_TAC 1"
val expected_mat1c = ``f (a:num) a = (u:'a)``
val expected_mat1a1 = ``Abbrev (b = zero)``
val expected_mat1a2 = ``Abbrev (a:num = b)``
val expected_mat1a3 = ``Abbrev (u:'a = z)``
val (sgs, _) = Q.MATCH_ABBREV_TAC `f b a = u` glmrt3
val _ = case sgs of
            [([a1,a2,a3], c)] =>
            (let
               val _ = aconvdie "assumption #1" a1 expected_mat1a1
               val _ = aconvdie "assumption #2" a2 expected_mat1a2
               val _ = aconvdie "assumption #3" a3 expected_mat1a3
               val _ = aconvdie "goal conclusion" c expected_mat1c
             in
               OK()
             end handle InternalDie s => die s)
          | _ => die "FAILED! (new goal of wrong shape)"

val _ = tprint "Q.MATCH_ABBREV_TAC 2"
val expected_mat2c = ``(f : 'b -> 'a) z = v``
(* first assumption is most recently created *)
val expected_mat2a1 = ``Abbrev(v : 'a = s)``
val expected_mat2a2 = ``Abbrev(z :'b = h (v:'a))``
val (sgs, _) = Q.MATCH_ABBREV_TAC `f z = v` glmrt2
val _ = case sgs of
            [([a1, a2], c)] =>
            (let
               val _ = aconvdie "goal conclusion" c expected_mat2c
               val _ = aconvdie "assumption #1" a1 expected_mat2a1
               val _ = aconvdie "assumption #2" a2 expected_mat2a2
             in
               OK()
             end handle InternalDie s => die s)
          | _ => die "FAILED! (new goal of wrong shape)"

val _ = tprint "Q.MATCH_GOALSUB_RENAME_TAC 1"
val gl1 = ([] : term list,
          ``!x. x * SUC (SUC zero) < y * (z + SUC zero) * (y + a)``)
val expected_result1 =
    ``!x. x * SUC (SUC zero) < y * (z + SUC zero) * (y + c)``
fun check (sgs, _) =
    case sgs of
        [([], t)] => aconv t expected_result1
      | _ => false
val _ = require (check_result check) (Q.MATCH_GOALSUB_RENAME_TAC `y + c`) gl1

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
            if Term.aconv abb ``Abbrev(v <=> y < SUC zero)`` andalso
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
            if Term.aconv abb ``Abbrev (v <=> u < SUC (SUC zero))`` andalso
               Term.aconv sg ``(!y. y < SUC zero) /\ v``
            then OK()
            else die "FAILED!"
          | _ => die "FAILED!"

val _ = tprint "Q.PAT_ABBREV_TAC (gh262) 6"
val (sgs,_) = Q.PAT_ABBREV_TAC `v = (x < SUC z)`
                  ([], ``(!x. x < SUC zero) /\ u < SUC (SUC zero)``)
val _ = case sgs of
            [([abb], sg)] =>
            if Term.aconv abb ``Abbrev (v <=> u < SUC (SUC zero))`` andalso
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

val _ = require (check_result (fn _ => true))
                 (fn tac => TAC_PROOF(([], ``foo1 F x y``), tac))
                 (Q.MATCH_RENAME_TAC `foo F a b` >>
                  REWRITE_TAC [foo1_def]);

val _ = tprint "Q.RENAME1 on overloads"
val _ = require (check_result (fn _ => true))
                (fn tac => TAC_PROOF(([], ``?v. foo1 v x y``),tac))
                (Q.RENAME1_TAC `foo _ a b` >>
                 Q.EXISTS_TAC `F` >>
                 REWRITE_TAC [foo1_def]) ;

val _ = tprint "Q.kRENAME_TAC(1)"
val _ = require (check_result (fn _ => true))
                (fn tac =>
                    TAC_PROOF (
                      ([“foo1 a b c”, “foo2 d e f”], “?x y z. foo1 x y z”),
                      tac
                    )
                )
                (Q.kRENAME_TAC [`foo u v w`]
                               (MAP_EVERY Q.EXISTS_TAC [`u`, `v`, `w`] THEN
                                FIRST_ASSUM ACCEPT_TAC))

val _ = tprint "Q.kRENAME_TAC(2)"
val _ = require (check_result (fn _ => true))
                (fn tac =>
                    TAC_PROOF (
                      ([“foo2 a b c”, “foo1 d e f”], “?x y z. foo1 x y z”),tac))
                (Q.kRENAME_TAC [`foo u v w`]
                               (MAP_EVERY Q.EXISTS_TAC [`u`, `v`, `w`] THEN
                                FIRST_ASSUM ACCEPT_TAC))

val _ = tprint "PAT_ABBREV_TAC respects Parse.hide"
val _ = new_definition ("gh431_def", ``gh431 x = ~x``);
val _ = hide "gh431"
val _ = require (check_result (fn _ => true))
                (Q.PAT_ABBREV_TAC `gh431 = T` THEN Q.UNABBREV_TAC `gh431` THEN
                 REWRITE_TAC [])
                ([], ``p /\ T = p``)

val _ = new_definition ("gh425a_def", ``gh425a a = a``);
val _ = new_definition ("gh425b_def", ``gh425b p = (p ==> T)``);
val _ = overload_on ("gh425", ``gh425a``);
val _ = overload_on ("gh425", ``gh425b``);
val buf = ref ([] : string list)
fun app s = buf := s :: !buf
fun recording P f x =
    (buf := [];
     let
       val f' =
           (Lib.with_flag (Feedback.MESG_outstream, app) o
            Lib.with_flag (Feedback.ERR_outstream, app) o
            Lib.with_flag (Feedback.WARNING_outstream, app) o
            Lib.with_flag (Globals.interactive, true)) f
       val result = Exn.capture f' x
     in
       P result (!buf)
     end)

fun wasquiet res sl =
    if null sl then res
    else
        raise InternalDie
              ("\n  FAILED : buf contains " ^ String.concatWith "\n" sl)
fun testquiet f x = recording wasquiet f x

val _ = tprint "(Interactive) PAT_ASSUM quiet about tyvar guesses(1)"
val _ = let
  val result = testquiet
                 (Q.PAT_X_ASSUM `gh425a (g x)` mp_tac)
                 ([``gh425a (f T) : bool``], ``p /\ q``)
in
  case result of
      Exn.Res ([([], t)],_) =>
              if aconv t ``gh425a (f T) ==> p /\ q`` then OK()
              else die "\nFAILED - Incorrect result"
    | _ => die "\nFAILED - Incorrect result"
end handle InternalDie s => die s

val _ = tprint "(Interactive) PAT_ASSUM quiet about tyvar guesses(2)"
val _ = testquiet
                 (Q.PAT_X_ASSUM `gh245 (g x)` mp_tac)
                 ([``gh425a (f T) : bool``], ``p /\ q``)
val _ = OK()

val _ = tprint "(Interactive) PAT_ASSUM quiet about tyvar guesses(3)"
val _ = (testquiet
          (Q.PAT_X_ASSUM `gh245 x` mp_tac)
          ([``gh425b (f T) : bool``], ``p /\ q``); OK())
        handle InternalDie s => die s

val _ = tprint "(Interactive) RENAME_TAC quiet about tyvar guesses(1)"
val _ = (testquiet (Q.RENAME_TAC [‘f x /\ _’])
                   ([], “(gg : num -> bool) n /\ p”); OK())
        handle InternalDie s => die s

val _ = tprint "(Interactive) RENAME_TAC quiet about tyvar guesses(2)"
val _ = (testquiet (Q.RENAME_TAC [‘SUC n’]) ([], “p /\ q”); OK())
        handle InternalDie s => die s

val _ = tprint "(Interactive) RENAME_TAC quiet about tyvar guesses(3)"
val _ = (testquiet (Q.RENAME_TAC [‘SUC n’]) ([“P (SUC x) ==> Q”], “p /\ q”);
         OK()) handle InternalDie s => die s

val _ = tprint "(Interactive) RENAME_TAC quiet about tyvar guesses(4)"
val _ = (testquiet (Q.RENAME_TAC [‘SUC n’]) ([“Pr ==> Q”], “P (SUC x) /\ q”);
         OK()) handle InternalDie s => die s

val _ = tprint "Q.SPEC_THEN reports type errors"
val _ = let
  fun contains res sl =
      if Portable.is_substring "α -> bool" (String.concat sl) then OK()
      else die ""
in
  recording contains (Q.SPEC_THEN ‘T’ MP_TAC (ASSUME “∀f. f x”)) ([], “p /\ q”)
end

val _ = testutils.shouldfail {
      checkexn = check_HOL_ERRexn (fn (s,_,_) => mem s ["Tactical","Q"]),
      printarg = K "Q.RENAME_TAC (* a|sg *) correctly fails on sub-term",
      printresult = PP.pp_to_string 70 proofManagerLib.std_goal_pp,
      testfn = hd o #1 o Q.RENAME_TAC [‘_ < y (* a|sg *)’]
    } ([“~(x < y)”, “P (x:num):bool”], “a < b”)


val _ = Process.exit Process.success;
