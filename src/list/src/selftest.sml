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

datatype 'a exnsum = Some of 'a | Exn of exn
fun total f x = Some (f x) handle Interrupt => raise Interrupt | e => Exn e

fun test0 nm cmp pr f (x, expected_opt) = let
  val _ = tprint (StringCvt.padRight #" " 20 nm ^ pr x)
in
  case (total f x, expected_opt) of
      (Some result, SOME expected) =>
        if cmp(rhs (concl result),expected) <> EQUAL then die "FAILED - BAD RHS"
        else if not (null (hyp result)) then die "FAILED - HYPS"
        else if cmp(lhs (concl result),x) <> EQUAL then die "FAILED - BAD LHS"
        else OK()
    | (Some _, NONE) => die "FAILED - didn't raise EXN"
    | (Exn e, SOME _) => die ("FAILED\n  EXN: "^General.exnMessage e)
    | (Exn _, NONE) => OK()
end

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
val _ = app(test "LIST_EQ_SIMP_CONV" Term.compare term_to_string
                 listSimps.LIST_EQ_SIMP_CONV)
           [(``(l1:'a list ++ [])::t = p ++ q``, ``(l1:'a list)::t = p ++ q``)]

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

val cs = listSimps.list_compset()
val _ = indexedListsSimps.add_indexedLists_compset cs
fun ct(s,inp,out) =
  testutils.convtest ("list_compset - " ^ s, computeLib.CBV_CONV cs, inp, out)
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
  ("LLEX(1)", “LLEX (<) [1;1;1] [1;2]”, “T”)
]
