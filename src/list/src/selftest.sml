open HolKernel Parse boolLib
open ListConv1

open testutils

fun parsetest(s, l) =
  let
    fun toN i = numSyntax.mk_numeral (Arbnum.fromInt i)
    val _ = tprint ("Parsing "^s)
    val res = Parse.Term [QUOTE s]
    val l_t = listSyntax.mk_list(map toN l, numSyntax.num)
  in
    if aconv res l_t then OK() else die "FAILED!"
  end

val _ = List.app parsetest [
      ("[]:num list", []),
      ("[1]", [1]), ("[1;]", [1]),
      ("[1;2]", [1,2]), ("[1;2;]", [1,2]),
      ("[1;2;3]", [1,2,3]), ("[1; 2; 3;]", [1,2,3]), ("[1; 2 ; 3 ; ]", [1,2,3]),
      ("[ 1 ;   2 ; 3 ; 4 ; ]", [1,2,3,4])
    ]

fun test0 nm cmp pr f (x, expected_opt) =
    case expected_opt of
        SOME t => convtest(nm ^ " " ^ term_to_string x,f,x,t)
      | NONE => shouldfail {checkexn = (fn HOL_ERR _ => true | _ => false),
                            printarg = K nm, printresult = thm_to_string,
                            testfn = f} x
fun test nm cmp pr f (x, e) = test0 nm cmp pr f (x, SOME e)

val _ = set_trace "Unicode" 0

val _ = app tpp [
  "MEM a l", "~MEM a l", "x NOTIN {1; 2; 3}",
  "case l of [] => 0 | h::t => h + LENGTH t",
  "[1; 2]",
  "[aaaa; bbbbb; cccc; dddd; eeee; ffff; gggg; hhhh; iiii; \
  \jjjj; kkkk; llll; mmmm;\n nnnn; oooo]",
  "f\n\
  \  [aaaa; bbbb; cccc; dddd; eeee; ffff; gggg; hhhh; iiii; jjjj; kkkk; llll; \
     \mmmm;\n\
  \   nnnn; oooo; pppp]"
]

val _ = tpp_expected {input = "SINGL 3", output = "[3]",
                      testf = standard_tpp_message}

val _ = app(test "FIRSTN_CONV" Term.compare term_to_string FIRSTN_CONV)
           [(``FIRSTN 3 [1;2;3;4;5]``, ``[1;2;3]``),
            (``FIRSTN 4 [1;2;3;4]``, ``[1;2;3;4]``),
            (``FIRSTN 0 [1;2]``, ``[] : num list``),
            (``FIRSTN 0 [] : num list``, ``[] : num list``)]
val _ = app(test "BUTFIRSTN_CONV" Term.compare term_to_string BUTFIRSTN_CONV)
           [(``BUTFIRSTN 3 [1;2;3;4]``, ``[4]``),
            (``BUTFIRSTN 0 [1;2]``, ``[1;2]``),
            (``BUTFIRSTN 3 [1;2;3]``, ``[] : num list``),
            (``BUTFIRSTN 0 [] : num list``, ``[] : num list``)]
val _ = app(test "LASTN_CONV" Term.compare term_to_string LASTN_CONV)
           [(``LASTN 3 [1;2;3;4]``, ``[2;3;4]``),
            (``LASTN 0 [1;2]``, ``[]: num list``),
            (``LASTN 3 [1;2;3]``, ``[1;2;3]``),
            (``LASTN 0 [] : num list``, ``[] : num list``)]
val _ = app(test "LIST_EQ_SIMP_CONV" Term.compare term_to_string
                 listSimps.LIST_EQ_SIMP_CONV)
           [(``(l1:'a list ++ [])::t = p ++ q``, ``(l1:'a list)::t = p ++ q``)]
val _ = app(test "APPEND_CONV" Term.compare term_to_string
                 ListConv1.APPEND_CONV)
           [(“[1;2;3] ++ [4;5;6]”, “[1;2;3;4;5;6]”),
            (“[] ++ [1]”, “[1]”), (“[1;2] ++ []”, “[1;2]”),
            (“[x;y] ++ [y;x]:'a list”, “[x;y;y;x]:'a list”)]

val _ = Lib.appi (fn i => fn t =>
                     test0 ("EL_CONV "^Int.toString (i+1))
                          Term.compare term_to_string EL_CONV t)
                 [(``EL 1 [3;4;5]``, SOME ``4``),
                  (``EL 0 [3+1;4;4*2]``, SOME ``3 + 1``),
                  (``EL 3 [1;2;3]``, NONE),
                  (``EL 1 (3::x::t)``, NONE),
                  (``EL 1 [a;b;c:num]``, SOME ``b:num``),
                  (``EL 3 [a;b;c:num;d]``, SOME ``d:num``)
                 ]

val _ = Lib.appi (fn i => fn t =>
                     test0 ("FLAT_CONV "^Int.toString (i + 1))
                           Term.compare term_to_string FLAT_CONV t)
                 [(``FLAT ([]:'a list list)``, SOME ``[] : 'a list``),
                  (``FLAT [[1];[2];[3];[1]]``, SOME ``[1;2;3;1]``),
                  (``FLAT [[];[];[]:'a list]``, SOME ``[]:'a list``),
                  (``FLAT [[1+2];[];[2*4]]``, SOME ``[1+2;2*4]``),
                  (``FLAT [[1+2;3;3*8];[];[];[1+21];[3;4]]``,
                     SOME ``[1+2;3;3*8;1+21;3;4]``),
                  (``FLAT ([]::(t:'a list list))``, NONE)
                 ]

val _ = test0 "FOLDR_CONV 1" Term.compare term_to_string
              (FOLDR_CONV ALL_CONV)
              (``FOLDR f 0 [1;2;3;x]``, SOME ``f 1 (f 2 (f 3 (f x 0)))``)
val _ = test0 "FOLDR_CONV 2" Term.compare term_to_string
              (FOLDR_CONV (TRY_CONV reduceLib.ADD_CONV))
              (``FOLDR f (3 + 2) [1 * 4; 3 - 1]``,
                   SOME ``f (1 * 4) (f (3 - 1) (3 + 2))``)
val _ = Lib.appi (fn i => fn t =>
                     test0 ("FOLDR_CONV "^Int.toString (i + 3))
                           Term.compare term_to_string
                           (FOLDR_CONV numLib.REDUCE_CONV) t)
                 [(``FOLDR (+) 0 [0;1;2;3]``, SOME ``6``),
                  (``FOLDR (-) 0 [3;2;1]``, SOME ``2``),
                  (``FOLDR $* 1 []``, SOME ``1``)]

local
  val cs = listSimps.list_compset()
  val () = List.app (fn f => f cs)
             [indexedListsSimps.add_indexedLists_compset,
              numposrepLib.add_numposrep_compset,
              bitLib.add_bit_compset]
in
  fun ct(s,inp,out) =
    testutils.convtest
      ("list_compset++ - " ^ s, computeLib.CBV_CONV cs, inp, out)
end

val _ = List.app ct [
  ("oHD-NONE", “oHD ([]:'a list)”, “NONE : 'a option”),
  ("oHD-SOME", “oHD ([3;4]:num list)”, “SOME 3n”),
  ("oEL-NONE1", “oEL 1 ([]:'a list)”, “NONE : 'a option”),
  ("oEL-NONE2", “oEL 2 [3;4]”, “NONE : num option”),
  ("oEL-SOME1", “oEL 0 [3;4]”, “SOME 3n”),
  ("oEL-SOME2", “oEL 4 [3;4;5;6;7;10]”, “SOME 7n”),
  ("MAP-NIL", “MAP SUC []”, “[] : num list”),
  ("MAP-CONS", “MAP SUC [1;2;3]”, “[2;3;4] : num list”),
  ("MAP2i-NIL1", “MAP2i (\i x y. x + i * y) [] []”, “[] : num list”),
  ("MAP2i-CONS", “MAP2i (\i x y. x + i * y) [1;2;3] [4;5;6]”,
                 “[1;7;15] : num list”),
  ("FOLDL1", “FOLDL $+ 0 [1;2;3;4]”, “10n”),
  ("FOLDR1", “FOLDR (\n a. (n * 2) :: a) [] [1;2;3;4]”, “[2;4;6;8]”),
  ("GENLIST", “GENLIST (\n. 2 * n + 4) 6”, “[4; 6; 8; 10; 12; 14]”),
  ("CONS-eq-NIL", “h::t = []”, “F”),
  ("LUPDATE(1)", “LUPDATE 9 2 [1;2;3;4]”, “[1;2;9;4]”),
  ("LUPDATE(2)", “LUPDATE 9 4 [1;2;3;4]”, “[1;2;3;4]”),
  ("SHORTLEX(1)", “SHORTLEX (<) [1;1] [1;2;3]”, “T”),
  ("SHORTLEX(2)", “SHORTLEX (<) [1;1;4] [1;1;3]”, “F”),
  ("SHORTLEX(3)", “SHORTLEX (<) [1;1;4] [1;1]”, “F”),
  ("LLEX(1)", “LLEX (<) [1;1;1] [1;2]”, “T”),
  ("l2n_empty",      ``l2n v []``, ``0n``),
  ("l2n_base_v",     ``l2n v [1]``, ``l2n v [1]``),
  ("l2n_base_3",     ``l2n 3 [1]``, ``l2n 3 [1]``),
  ("l2n_base_2_v",   ``l2n 2 v``, ``l2n 2 v``),
  ("l2n_base_8_v",   ``l2n 8 v``, ``l2n 8 v``),
  ("l2n_base_10_v",  ``l2n 10 v``, ``l2n 10 v``),
  ("l2n_base_16_v",  ``l2n 16 v``, ``l2n 16 v``),
  ("l2n_base_256_v", ``l2n 256 v``, ``l2n 256 v``),
  ("l2n_base_2",     ``l2n 2 [1; 0; 1; 1; 1]``, ``0b11101n``),
  ("l2n_base_8",     ``l2n 8 [1; 2; 3; 4; 5]``, ``22737n``),
  ("l2n_base_10",    ``l2n 10 [1; 2; 3; 4; 5]``, ``54321n``),
  ("l2n_base_16",    ``l2n 16 [1; 2; 3; 4; 5]``, ``344865n``),
  ("l2n_base_256",   ``l2n 256 [1; 2; 3; 4; 5]``, ``21542142465n``),
  ("n2l_base_v",     ``n2l v 12345``, ``n2l v 12345``),
  ("n2l_base_3",     ``n2l 3 12345``, ``n2l 3 12345``),
  ("n2l_base_2_v",   ``n2l 2 v``, ``n2l 2 v``),
  ("n2l_base_8_v",   ``n2l 8 v``, ``n2l 8 v``),
  ("n2l_base_10_v",  ``n2l 10 v``, ``n2l 10 v``),
  ("n2l_base_16_v",  ``n2l 16 v``, ``n2l 16 v``),
  ("n2l_base_256_v", ``n2l 256 v``, ``n2l 256 v``),
  ("n2l_base_2",     ``n2l 2 0b11101``, ``[1; 0; 1; 1; 1n]``),
  ("n2l_base_8",     ``n2l 8 22737``, ``[1; 2; 3; 4; 5n]``),
  ("n2l_base_10",    ``n2l 10 54321``, ``[1; 2; 3; 4; 5n]``),
  ("n2l_base_16",    ``n2l 16 344865``, ``[1; 2; 3; 4; 5n]``),
  ("n2l_base_256",   ``n2l 256 21542142465``, ``[1; 2; 3; 4; 5n]``)
]

val _ = let
  open BasicProvers listTheory
  val op using = markerLib.using
  val usingA = markerLib.usingA
  val g = “0 < LENGTH (l:num list)”
  val expected = [“0 < LENGTH ([]:num list)”, “0 < LENGTH (SNOC (x:num) l')”]
  val expected2 =
      [“0 < LENGTH ([]:num list)”, “∀x. 0 < LENGTH (SNOC (x:num) l)”]
  val expected2a = [[], [“0 < LENGTH (l:num list)”]]
  infix AND
  fun (f AND g) x = f x andalso g x
  fun check1 sgs = list_eq aconv expected (map snd sgs)
  fun check1a sgs = List.all null (map fst sgs : term list list)
  fun check2 sgs = list_eq (list_eq aconv) expected2a (map fst sgs)
  val ppgs = trace ("types", 1) (
        HOLPP.block HOLPP.CONSISTENT 4 o
        HOLPP.pr_list goalStack.pp_goal [HOLPP.NL, HOLPP.NL]
      )
  val rtcg = “!y:num x:num. RTC R x (f y) ==> Q x y”
  val rtc_expected = [“(!m:num n:num. f n = m ==> Q m n) /\
                       !a b c. (!d. f d = b ==> Q a d) /\ R b c ==>
                               !d. f d = c ==> Q a d”]
  val bit_cases = hd (Prim_rec.prove_cases_thm numeralTheory.bit_induction)
  val bitind_goal = “0 < n”
  val bitind_expected = [([], “0 < ZERO”), ([“0 < n”], “0 < BIT1 n”),
                         ([“0 < n”], “0 < BIT2 n”)]
  fun TAC t g = fst (VALID t g)
in
  tprint "Cases_on ‘m’ using bit_cases";
  require_msg (check_result (
                  (list_eq aconv [“0 < ZERO”, “0 < BIT1 n”, “0 < BIT2 n”] o
                   map snd) AND
                  (List.all null o map fst)
              ))
              (HOLPP.pp_to_string 65 ppgs)
              (TAC $ Cases_on ‘m’ using bit_cases) ([], “0 < m”);
  tprint "Cases_on ‘m’ using EVEN_OR_ODD";
  require_msg (check_result ((list_eq aconv [“0 < m”, “0 < m”] o map snd) AND
                             (list_eq (list_eq aconv) [[“EVEN m”], [“ODD m”]] o
                              map fst)))
              (HOLPP.pp_to_string 65 ppgs)
              (TAC $ Cases_on ‘m’ using arithmeticTheory.EVEN_OR_ODD)
              ([], “0 < m”);
  tprint "Cases_on ‘m’ using assumption";
  require_msg (check_result ((list_eq aconv [“0 < 2”, “0 < 4”] o map snd) AND
                             (List.all null o map fst)))
              (HOLPP.pp_to_string 65 ppgs)
              (TAC $ pop_assum $ usingA $ Cases_on ‘m’)
              ([“!a. a = 2 \/ a = 4”], “0 < m”);
  tprint "Cases_on ‘l’ using SNOC_CASES";
  require_msg (check_result (check1 AND check1a))
              (HOLPP.pp_to_string 65 ppgs)
              (TAC $ Cases_on ‘l’ using SNOC_CASES) ([], g);
  tprint "Induct_on ‘l’ using SNOC_INDUCT";
  require_msg (check_result ((list_eq aconv expected2 o map snd) AND check2))
              (HOLPP.pp_to_string 65 ppgs)
              (TAC (Induct_on ‘l’ using SNOC_INDUCT)) ([], g);
  tprint "Induct_on ‘RTC’ using RTC_INDUCT_RIGHT1";
  require_msg (check_result ((list_eq aconv rtc_expected o map snd)))
              (HOLPP.pp_to_string 65 ppgs)
              (TAC $ Induct_on ‘RTC’ using relationTheory.RTC_INDUCT_RIGHT1)
              ([], rtcg);
  tprint "Induct_on ‘n’ using numeralTheory.bit_induction";
  require_msg (check_result
                 (list_eq (pair_eq (list_eq aconv) aconv) bitind_expected))
              (HOLPP.pp_to_string 65 ppgs)
              (TAC $ Induct_on ‘n’ using numeralTheory.bit_induction)
              ([], bitind_goal)
end


val _ = let
  open BasicProvers simpLib listTheory
  val _ = tprint
  val MAP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG

  val t = “(!x:'a. MEM x l ==> g x = c:'b option) ==> P (MAP THE (MAP g l))”
  val expected =
      “(!x:'a. MEM x l ==> g x = c:'b option) ==> P (MAP THE (MAP (\x. c) l))”
in
  convtest("simplify with MAP_CONG; get eta-redex?",
           SIMP_CONV (quietly srw_ss()) [Cong MAP_CONG'], t, expected)
end
