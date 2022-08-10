open HolKernel Parse boolTheory boolLib pairTheory
open constrFamiliesLib patternMatchesLib computeLib
open quantHeuristicsLib simpLib boolSimps listTheory
open BasicProvers
open testutils


val hard_fail = true;
val _ = testutils.diemode := ProcessExit
val quiet = false;
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Feedback.emit_MESG := false

(* For manual

set_trace "use pmatch_pp" 0
val hard_fail = false;
val _ = testutils.diemode := FailException
val quiet = false;
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;

*)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES ();
val list_ss  = numLib.arith_ss ++ listSimps.LIST_ss

fun pterm_to_string pfx t = pfx ^ " " ^ UnicodeChars.ldquo ^ term_to_string t ^
                            UnicodeChars.rdquo

val isHE = (fn HOL_ERR _ => true | _ => false)
val is_unchHE = (fn HOL_ERR _ => true | UNCHANGED => true | _ => false)
fun valid_conv_result inp out th = concl th ~~ mk_eq(inp,out)
fun test_conv nm c (inp,outopt) =
    case outopt of
        NONE => shouldfail {
                 checkexn = is_unchHE,
                 printarg = pterm_to_string (nm ^ "(valid exn)"),
                 printresult = term_to_string o concl,
                 testfn = quietly c
               } inp
      | SOME t =>
        let
          val _ = tprint (pterm_to_string nm inp)
        in
          require_msg (check_result (valid_conv_result inp t))
                      thm_to_string (quietly c) inp
        end


(* ----------------------------------------------------------------------
    Parser
   ---------------------------------------------------------------------- *)

fun pel2string [] = ""
  | pel2string (pLeft::rest) = "L" ^ pel2string rest
  | pel2string (pRight::rest) = "R" ^ pel2string rest
  | pel2string (pAbs::rest) = "A" ^ pel2string rest
fun d2string (p,t1,t2) =
  "   " ^
  trace ("types", 1) term_to_string t1 ^ " - " ^
  trace ("types", 1) term_to_string t2 ^
  "  (" ^ pel2string p ^ ")\n"

fun test(inp, expected) =
  let
    val _ = tprint ("Parsing "^inp)
    val tm = Parse.Term [QUOTE inp]
  in
    if aconv tm expected then OK()
    else
      let
        val diffs = term_diff expected tm
      in
        die ("FAILED!\n" ^ String.concat (map d2string diffs))
      end
  end

val _ = app test [
  ("case b of T => F | F => T",
   “PMATCH (b:bool) [PMATCH_ROW (\u:one. T) (\u:one. T) (\u:one. F);
                      PMATCH_ROW (\u:one. F) (\u:one. T) (\u:one. T)]”),

  ("case x of 0 => 3 | SUC n => n + 1",
   “PMATCH x [PMATCH_ROW (\u:one. 0) (\u:one. T) (\u:one. 3);
               PMATCH_ROW (\n. SUC n) (\n:num. T) (\n. n + 1)]”),

  ("case x of 0 => 3 | SUC _ => 4",
   “PMATCH x [PMATCH_ROW (\u:one. 0) (\u:one. T) (\u:one. 3);
               PMATCH_ROW (\n:num. SUC n) (\n:num. T) (\n:num. 4)]”),

  ("case (x : bool list) of [] => F | (x,xs) .| x::xs => x",
   “PMATCH x [PMATCH_ROW (\u:one. []:bool list) (\u:one. T) (\u:one. F);
               PMATCH_ROW (\ (x:bool,xs:bool list). x::xs)
                          (\ (x:bool,xs:bool list). T)
                          (\ (x:bool,xs:bool list). x)]”),

  ("(n:num) + case m of 0 => 3 | () .| SUC n => 10 | z => z",
   “(n:num) +
     PMATCH m [PMATCH_ROW (\u:one. 0n) (\u:one. T) (\u:one. 3n);
               PMATCH_ROW (\u:one. SUC n) (\u:one. T) (\u:one. 10);
               PMATCH_ROW (\z:num. z) (\z:num. T) (\z:num. z)]”),

  ("case x of 0 => 3 | () .| n => 4 | _ => 100",
   “PMATCH (x:num) [PMATCH_ROW (\u:one. 0n) (\u:one. T) (\u:one. 3n);
                     PMATCH_ROW (\u:one. n:num) (\u:one. T) (\u:one. 4n);
                     PMATCH_ROW (\x:num. x) (\x:num. T) (\x:num. 100n)]”),

  ("n + case b of T => 1 | n => 2",
   “n + PMATCH (b:bool)
                [PMATCH_ROW (\u:one. T) (\u:one. T) (\u:one. 1n);
                 PMATCH_ROW (\n:bool. n) (\n:bool. T) (\n:bool. 2n)]”),

  ("n + case x of 0 => 1 | m .| m + n => m * 2",
   “n + PMATCH (x:num)
                [PMATCH_ROW (\u:one. 0) (\u:one. T) (\u:one. 1);
                 PMATCH_ROW (\m:num. m + n) (\m:num. T) (\m:num. m * 2)]”),

  ("case x of 0 => 3 | () .| n => 4 | x => 100",
   “PMATCH (x:num) [PMATCH_ROW (\u:one. 0n) (\u:one. T) (\u:one. 3n);
                     PMATCH_ROW (\u:one. n:num) (\u:one. T) (\u:one. 4n);
                     PMATCH_ROW (\x:num. x) (\x:num. T) (\x:num. 100n)]”),

  ("case (y,x) of\
   \ | (NONE,[]) => 0\
   \ | (NONE,[T]) => 1\
   \ | (SOME T,[]) => 2\
   \ | (SOME _, _) => 3\
   \ | z .| (SOME _, z) => 4\
   \ | (z1, z2:'a) .| (SOME _, z1) => 5\
   \ | z .| (SOME T, z) when LENGTH x > 5 => 6\
   \ | (z1, z2, z3:'b list) .| (SOME z1, z2) when LENGTH z3 > 5 => 7",
   “PMATCH ((y :bool option),(x :bool list))
      [PMATCH_ROW (\_uv :unit. (NONE :bool option,[] :bool list))
                  (\_uv :unit. T)
                  (\_uv :unit. 0n);
       PMATCH_ROW (\_uv :unit. (NONE :bool option,[T]))
                  (\_uv:unit. T)
                  (\_uv:unit. 1n);
       PMATCH_ROW (\_uv:unit. (SOME T, [] :bool list)) (\_uv:unit. T)
                  (\_uv :unit. 2n);
       PMATCH_ROW (\ ((xx :bool),(yy :bool list)). (SOME xx,yy))
                  (\ ((xx :bool),(yy :bool list)). T)
                  (\ ((xx :bool),(yy :bool list)). 3n);
       PMATCH_ROW (\ ((z :bool list),(u2 :bool)). (SOME u2,z))
                  (\ ((z :bool list),(u2 :bool)). T)
                  (\ ((z :bool list),(u2 :bool)). 4n);
       PMATCH_ROW (\ (z1 :bool list, (z2 :'a, u3 :bool)). (SOME u3,z1))
                  (\ (z1 :bool list, (z2 :'a, u3 :bool)). T)
                  (\ (z1 :bool list, (z2 :'a, u3 :bool)). 5n);
       PMATCH_ROW (\ (z :bool list). (SOME T,z))
                  (\ (z :bool list). LENGTH x > 5n)
                  (\ (z :bool list). 6n);
       PMATCH_ROW
         (\ ((z1 :bool),(z2 :bool list),(z3 :'b list)). (SOME z1,z2))
         (\ ((z1 :bool),(z2 :bool list),(z3 :'b list)). LENGTH z3 > 5n)
         (\ ((z1 :bool),(z2 :bool list),(z3 :'b list)). 7n)]”),

  ("case x of NONE => y | SOME (z:'foo) => (f z : 'bar)",
   “PMATCH (x:'foo option) [
       PMATCH_ROW (\_uv:unit. NONE) (\_uv:unit. T) (\_uv:unit. y:'bar);
       PMATCH_ROW (\z:'foo. SOME z) (\z:'foo. T) (\z:'foo. f z : 'bar)
     ]”),

  ("case x of NONE => y | z:'foo .| SOME z => (f z : 'bar)",
   “PMATCH (x:'foo option) [
       PMATCH_ROW (\_uv:unit. NONE) (\_uv:unit. T) (\_uv:unit. y:'bar);
       PMATCH_ROW (\z:'foo. SOME z) (\z:'foo. T) (\z:'foo. f z : 'bar)
     ]”),

  ("dtcase x of NONE => 3 | SOME y => y + 1",
   “option_CASE (x : num option) 3n (\z:num. z + 1)”)

]

val parsefails =
    shouldfail {checkexn = isHE,
                printarg = fn s => "Should NOT parse: " ^ s,
                printresult = term_to_string,
                testfn = fn s => trace ("show_typecheck_errors", 0) Parse.Term
                                       [QUOTE s]};

val _ = app parsefails [
      "case x of NONE => F | y .| SOME(x,y) => x < y"
]

(* ----------------------------------------------------------------------
    Pretty-printer
   ---------------------------------------------------------------------- *)

val _ = app (raw_backend tpp) [
  "case x of 0 => 3 | SUC n => n",
  "dtcase x of 0 => 3 | SUC n => n",
  "(case x of 0 => 3 | SUC n => n) > 5",
  "(dtcase x of 0 => 3 | SUC n => n) = 3",
  "case SUC 5 of 0 => 3 | SUC n => n",
  "dtcase SUC (SUC 5) of 0 => 3 | SUC n => n",
  "case x of 0 => 4 | SUC _ => 10",
  "case (x,y) of (NONE,_) => 10 | (SOME n,0) when n < 10 => 11",
  "case x of 0 => 3 | () .| n => 4 | x => 100",
  "case x of NONE => 3 | () .| SOME n => n | SOME x => x + 1",
  "dtcase (x,y) of (NONE,z) => SUC z | (SOME n,z) => n",
  "SUC (case x of 0 => 3 | SUC n => n)",
  "SUC (dtcase x of 0 => 3 | SUC n => n)",
  "case x of z .| 0 => z | SUC _ => 10",
  "case x of (z,y) .| 0 => z | SUC _ => 10"
]


(******************************************************************************)
(* Converting from existing decision trees                                    *)
(******************************************************************************)

val tc = test_conv "PMATCH_INTRO_CONV" PMATCH_INTRO_CONV

val t = “dtcase x of (NONE, []) => 0”;
val r_thm = SOME “PMATCH (x :'a option # 'b list)
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),([] :'b list)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num))]”
val _ = tc (t, r_thm);

val t = “dtcase x of
   (NONE, []) => 0
 | (SOME 2, []) => 2
 | (SOME 3, (x :: xs)) => 3 + x
 | (SOME _, (x :: xs)) => x”
val r_thm = SOME “PMATCH x
     [PMATCH_ROW (\(_uv :unit). ((NONE :num option),([] :num list)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
      PMATCH_ROW (\(_uv :unit). (SOME (2 :num),([] :num list)))
        (\(_uv :unit). T) (\(_uv :unit). (2 :num));
      PMATCH_ROW (\((x :num),(_0 :num list)). (SOME (3 :num),x::_0))
        (\((x :num),(_0 :num list)). T)
        (\((x :num),(_0 :num list)). (3 :num) + x);
      PMATCH_ROW (\((_0 :num),(x :num),(_1 :num list)). (SOME _0,x::_1))
        (\((_0 :num),(x :num),(_1 :num list)). T)
        (\((_0 :num),(x :num),(_1 :num list)). x)]”
val _ = tc (t, r_thm);




val tcn = test_conv "PMATCH_INTRO_CONV_NO_OPTIMISE" PMATCH_INTRO_CONV_NO_OPTIMISE

val t = “dtcase x of (NONE, []) => 0”
val r_thm = SOME “PMATCH x
     [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),([] :'b list)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
      PMATCH_ROW (\((v4 :'b),(v5 :'b list)). ((NONE :'a option),v4::v5))
        (\((v4 :'b),(v5 :'b list)). T)
        (\((v4 :'b),(v5 :'b list)). (ARB :num));
      PMATCH_ROW (\((v2 :'a),(v1 :'b list)). (SOME v2,v1))
        (\((v2 :'a),(v1 :'b list)). T)
        (\((v2 :'a),(v1 :'b list)). (ARB :num))]”
val _ = tcn (t, r_thm);

val t = “dtcase x of
   (NONE, []) => 0
 | (SOME 2, []) => 2
 | (SOME 3, (x :: xs)) => 3 + x
 | (SOME _, (x :: xs)) => x”
val r_thm = SOME “
   PMATCH x
     [PMATCH_ROW (\(_uv :unit). ((NONE :num option),([] :num list)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
      PMATCH_ROW (\(_uv :unit). (SOME (2 :num),([] :num list)))
        (\(_uv :unit). T) (\(_uv :unit). (2 :num));
      PMATCH_ROW (\(v5 :num). (SOME v5,([] :num list))) (\(v5 :num). T)
        (\(v5 :num). (ARB :num));
      PMATCH_ROW
        (\((x :num),(xs :num list)). ((NONE :num option),x::xs))
        (\((x :num),(xs :num list)). T)
        (\((x :num),(xs :num list)). (ARB :num));
      PMATCH_ROW (\((x :num),(xs :num list)). (SOME (3 :num),x::xs))
        (\((x :num),(xs :num list)). T)
        (\((x :num),(xs :num list)). (3 :num) + x);
      PMATCH_ROW
        (\((v12 :num),(x :num),(xs :num list)). (SOME v12,x::xs))
        (\((v12 :num),(x :num),(xs :num list)). T)
        (\((v12 :num),(x :num),(xs :num list)). x)]”
val _ = tcn (t, r_thm);


val t = “dtcase x of 0 => 0 | SUC x => if (x+1 = 2) then 1 else 2”;
val r_thm = SOME “case x of 0 => 0 | SUC x => (if x + 1 = 2 then 1 else 2)”
val _ = tc (t, r_thm);


(******************************************************************************)
(* Simplification                                                             *)
(******************************************************************************)

val test =  test_conv "PMATCH_CLEANUP_PVARS_CONV" PMATCH_CLEANUP_PVARS_CONV (“PMATCH (x:('b # 'c) option) [
     PMATCH_ROW (\x:'a. NONE) (\x. T) (\x. 5);
     PMATCH_ROW (\ (x,y). SOME (x,z)) (\ (x,y). T) (\ (x,y). 8);
     PMATCH_ROW (\ (x,z). SOME (x,z)) (\_. T) (\ (a,y). 8)]”,
SOME “PMATCH (x:('b # 'c) option)
     [PMATCH_ROW (\_uv:unit. NONE) (\_uv. T) (\_uv. 5);
      PMATCH_ROW (\x. SOME (x,z)) (\x. T) (\x. 8);
      PMATCH_ROW (\(x,z). SOME (x,z)) (\(x,z). T) (\(x,z). 8)]”)

val test = test_conv "PMATCH_EXPAND_COLS_CONV" PMATCH_EXPAND_COLS_CONV (“PMATCH (x,y,z)
    [PMATCH_ROW (\y. (0,y,T)) (\y. T) (\y. y);
     PMATCH_ROW (\xyz. xyz) (\xyz. ~SND (SND xyz)) (\xyz. 2);
     PMATCH_ROW (\(x,yz). (x,yz)) (\(x,yz). T) (\(x,yz). x)]”,
SOME “PMATCH (x,y,z)
     [PMATCH_ROW (\y. (0,y,T)) (\y. T) (\y. y);
      PMATCH_ROW (\(xyz_0,xyz_1,xyz_2). (xyz_0,xyz_1,xyz_2))
        (\(xyz_0,xyz_1,xyz_2). ~SND (SND (xyz_0,xyz_1,xyz_2)))
        (\(xyz_0,xyz_1,xyz_2). 2);
      PMATCH_ROW (\(x,yz_0,yz_1). (x,yz_0,yz_1)) (\(x,yz_0,yz_1). T)
        (\(x,yz_0,yz_1). x)]”)

val test = test_conv "PMATCH_EXPAND_COLS_CONV" PMATCH_EXPAND_COLS_CONV (“case xy of
    | (SOME x, SOME y) => SOME (x + y)
    | _ => NONE”, SOME (“case xy of
        (SOME x,SOME y) => SOME (x + y) | (_,_) => NONE”))

val test = test_conv "PMATCH_EXPAND_COLS_CONV" PMATCH_EXPAND_COLS_CONV (“case (x,y) of
    | (SOME x, SOME y) => SOME (x + y)
    | _ => NONE”, SOME (“
      case (x,y) of
        (SOME x,SOME y) => SOME (x + y) | (_,_) => NONE”))

val test = test_conv "PMATCH_INTRO_WILDCARDS_CONV" PMATCH_INTRO_WILDCARDS_CONV (“PMATCH (x,y,z)
    [PMATCH_ROW (\(_x,y,z). (_x,y,z)) (\(_x,y,z). T) (\(_x,y,z). _x + y);
     PMATCH_ROW (\(x,y,z). (x,y,z)) (\(x,y,z). z) (\(x,y,z). x)]”, SOME “PMATCH (x,y,z)
     [PMATCH_ROW (\(x,y,_0). (x,y,_0)) (\(x,y,_0). T)
        (\(x,y,_0). x + y);
      PMATCH_ROW (\(x,_0,z). (x,_0,z)) (\(x,_0,z). z) (\(x,_0,z). x)]”)


val test = test_conv "PMATCH_CLEANUP_CONV" PMATCH_CLEANUP_CONV (“case (SUC x) of
     x => x + 5”, SOME “SUC x + 5”)

val test = test_conv "PMATCH_CLEANUP_CONV" PMATCH_CLEANUP_CONV (“case (SOME (x:'a),y) of
     (NONE, y) => 0
   | (x, 0) => 1
   | (SOME x, y) => 2
   | (x, y) => 3”, SOME “ PMATCH (SOME (x:'a),y)
     [PMATCH_ROW (\x. (x,0)) (\x. T) (\x. 1);
      PMATCH_ROW (\(x,y). (SOME x,y)) (\(x,y). T) (\(x,y). 2)]”)

val test = test_conv "PMATCH_CLEANUP_CONV" PMATCH_CLEANUP_CONV (“case (SOME (x:'a),y) of
     (NONE, y) => 0
   | (SOME x, y) => 2
   | (x, y) => 3”, SOME “2”)

val test = test_conv "PMATCH_SIMP_COLS_CONV" PMATCH_SIMP_COLS_CONV (“case (SOME x,y) of
   | (SOME x, 1) => x+y
   | (x, y) => 3”, SOME “PMATCH y
     [PMATCH_ROW (\(_uv:unit). 1) (\_uv. T) (\_uv. x + y);
      PMATCH_ROW (\y. y) (\y. T) (\y. 3)]”)

val test = test_conv "PMATCH_SIMP_COLS_CONV" PMATCH_SIMP_COLS_CONV (“case (SOME x,y) of
   | (SOME x, 1) => x+y
   | (SOME 2, 2) => y
   | (x, y) => 3”, SOME “PMATCH (x,y)
     [PMATCH_ROW (\x. (x,1)) (\x. T) (\x. x + y);
      PMATCH_ROW (\(_uv:unit). (2,2)) (\_uv. T) (\_uv. y);
      PMATCH_ROW (\(x_0,y). (x_0,y)) (\(x_0,y). T) (\(x_0,y). 3)]”)


val test =  test_conv "PMATCH_REMOVE_FAST_REDUNDANT_CONV" PMATCH_REMOVE_FAST_REDUNDANT_CONV (“case xy of
   | (SOME x, y) => 1
   | (SOME 2, 3) => 2
   | (NONE, y) => 3
   | (NONE, y) => 4
   | (x, 5) => 5”, SOME “
  case xy of
   | (SOME (x:num), y) => 1
   | (NONE, y) => 3
   | (x, 5) => 5”)

val test =  test_conv "PMATCH_REMOVE_REDUNDANT_CONV" PMATCH_REMOVE_REDUNDANT_CONV (“case xy of
   | (SOME x, y) => 1
   | (SOME 2, 3) => 2
   | (NONE, y) => 3
   | (NONE, y) => 4
   | (x, 5) => 5”, SOME “
  case xy of
   | (SOME (x:num), (y:num)) => 1
   | (NONE, y) => 3”)


val test =  test_conv "PMATCH_REMOVE_FAST_SUBSUMED_CONV true" (PMATCH_REMOVE_FAST_SUBSUMED_CONV true) (“case xy of
   | (SOME 2, _) => 2
   | (NONE, 3) => 1
   | (SOME x, _) => x
   | (NONE, y) => y
   | (x, 5) => ARB”, SOME
“case xy of
   | (NONE, 3) => 1
   | (SOME x, _) => x
   | (NONE, y) => y”)

val test =  test_conv "PMATCH_REMOVE_FAST_SUBSUMED_CONV false" (PMATCH_REMOVE_FAST_SUBSUMED_CONV false) (“case xy of
   | (SOME 2, _) => 2
   | (NONE, 3) => 1
   | (SOME x, _) => x
   | (NONE, y) => y
   | (x, 5) => ARB”, SOME
“case xy of
   | (NONE, 3) => 1
   | (SOME x, _) => x
   | (NONE, y) => y
   | (x, 5) => ARB”)

val test =  test_conv "PMATCH_SIMP_CONV" PMATCH_SIMP_CONV
val test_fast =  test_conv "PMATCH_FAST_SIMP_CONV" PMATCH_FAST_SIMP_CONV

val t =
   “PMATCH ((a :num option),(x :num),(xs :num list))
    [PMATCH_ROW (\(_0 :num). ((NONE :num option),_0,([] :num list)))
       (\(_0 :num). T) (\(_0 :num). (0 :num));
     PMATCH_ROW (\(x :num). ((NONE :num option),x,([] :num list)))
       (\(x :num). x < (10 :num)) (\(x :num). x);
     PMATCH_ROW (\(x :num). ((NONE :num option),x,[(2 :num)]))
       (\(x :num). T) (\(x :num). x);
     PMATCH_ROW (\((x :num),(v18 :num)). ((NONE :num option),x,[v18]))
       (\((x :num),(v18 :num)). T) (\((x :num),(v18 :num)). (3 :num));
     PMATCH_ROW
       (\((_3 :num),(_2 :num),(_1 :num)).
          ((NONE :num option),_1,[_2; _3]))
       (\((_3 :num),(_2 :num),(_1 :num)). T)
       (\((_3 :num),(_2 :num),(_1 :num)). x);
     PMATCH_ROW
       (\((x :num),(v12 :num),(v16 :num),(v17 :num list)).
          ((NONE :num option),x,v12::v16::v17))
       (\((x :num),(v12 :num),(v16 :num),(v17 :num list)). T)
       (\((x :num),(v12 :num),(v16 :num),(v17 :num list)). (3 :num));
     PMATCH_ROW (\((y :num),(x :num),(z :num),(zs :'a)). (SOME y,x,[z]))
       (\((y :num),(x :num),(z :num),(zs :'a)). T)
       (\((y :num),(x :num),(z :num),(zs :'a)). x + (5 :num) + z);
     PMATCH_ROW
       (\((y :num),(v23 :num),(v24 :num list)).
          (SOME y,(0 :num),v23::v24))
       (\((y :num),(v23 :num),(v24 :num list)). T)
       (\((y :num),(v23 :num),(v24 :num list)). v23 + y);
     PMATCH_ROW (\((y :num),(z :num),(v23 :num)). (SOME y,SUC z,[v23]))
       (\((y :num),(z :num),(v23 :num)). y > (5 :num))
       (\((y :num),(z :num),(v23 :num)). (3 :num));
     PMATCH_ROW
       (\((y :num),(z :num)). (SOME y,SUC z,[(1 :num); (2 :num)]))
       (\((y :num),(z :num)). T) (\((y :num),(z :num)). y + z)]”;

val t' = “PMATCH (a,x,xs)
     [PMATCH_ROW (\(_0 :num). ((NONE :num option),_0,([] :num list)))
        (\(_0 :num). T) (\(_0 :num). (0 :num));
      PMATCH_ROW (\(x :num). ((NONE :num option),x,[(2 :num)]))
        (\(x :num). T) (\(x :num). x);
      PMATCH_ROW (\((_0 :num),(_1 :num)). ((NONE :num option),_0,[_1]))
        (\((_0 :num),(_1 :num)). T) (\((_0 :num),(_1 :num)). (3 :num));
      PMATCH_ROW
        (\((_3 :num),(_2 :num),(_1 :num)).
           ((NONE :num option),_1,[_2; _3]))
        (\((_3 :num),(_2 :num),(_1 :num)). T)
        (\((_3 :num),(_2 :num),(_1 :num)). x);
      PMATCH_ROW
        (\((_0 :num),(_1 :num),(_2 :num),(_3 :num list)).
           ((NONE :num option),_0,_1::_2::_3))
        (\((_0 :num),(_1 :num),(_2 :num),(_3 :num list)). T)
        (\((_0 :num),(_1 :num),(_2 :num),(_3 :num list)). (3 :num));
      PMATCH_ROW (\((_0 :num),(x :num),(z :num)). (SOME _0,x,[z]))
        (\((_0 :num),(x :num),(z :num)). T)
        (\((_0 :num),(x :num),(z :num)). x + (5 :num) + z);
      PMATCH_ROW
        (\((y :num),(v23 :num),(_0 :num list)).
           (SOME y,(0 :num),v23::_0))
        (\((y :num),(v23 :num),(_0 :num list)). T)
        (\((y :num),(v23 :num),(_0 :num list)). v23 + y);
      PMATCH_ROW
        (\((y :num),(z :num)). (SOME y,SUC z,[(1 :num); (2 :num)]))
        (\((y :num),(z :num)). T) (\((y :num),(z :num)). y + z)]”;

val _ = test (t, (SOME t'))
val _ = test_fast (t, NONE)


val t = “PMATCH (x,y,z)
     [PMATCH_ROW (λ(y,z). (1,y,z)) (λ(y,z). T) (λ(y,z). y + z);
      PMATCH_ROW (λx. (x,2,4)) (λx. T) (λx. x + 4);
      PMATCH_ROW (λ(x,z). (x,2,z)) (λ(x,z). T) (λ(x,z). x + z);
      PMATCH_ROW (λ(x,y). (x,y,3)) (λ(x,y). T) (λ(x,y). x + y)]”;

val t' = “
   PMATCH (x,y,z)
     [PMATCH_ROW (λ(y,z). (1,y,z)) (λ(y,z). T) (λ(y,z). y + z);
      PMATCH_ROW (λ(x,z). (x,2,z)) (λ(x,z). T) (λ(x,z). x + z);
      PMATCH_ROW (λ(x,y). (x,y,3)) (λ(x,y). T) (λ(x,y). x + y)]”;

val _ = test (t, (SOME t'))
val _ = test_fast (t, NONE)


val t =
   “PMATCH ((NONE :'a option),(x :num),(xs :num list))
    [PMATCH_ROW (\(x :num). ((NONE :'a option),x,([] :num list)))
       (\(x :num). T) (\(x :num). x);
     PMATCH_ROW (\(x :num). ((NONE :'a option),x,[(2 :num)]))
       (\(x :num). T) (\(x :num). x);
     PMATCH_ROW (\((x :num),(v18 :num)). ((NONE :'a option),x,[v18]))
       (\((x :num),(v18 :num)). T) (\((x :num),(v18 :num)). (3 :num));
     PMATCH_ROW
       (\((x :num),(v12 :num),(v16 :num),(v17 :num list)).
          ((NONE :'a option),x,v12::v16::v17))
       (\((x :num),(v12 :num),(v16 :num),(v17 :num list)). T)
       (\((x :num),(v12 :num),(v16 :num),(v17 :num list)). (3 :num));
     PMATCH_ROW
       (\((y :'a option),(x :num)).
          (y,x,[(2 :num); (4 :num); (3 :num)]))
       (\((y :'a option),(x :num)). x > (5 :num))
       (\((y :'a option),(x :num)). (3 :num) + x)]”;

val t' = “
   PMATCH xs
     [PMATCH_ROW (\(_0 :unit). ([] :num list)) (\(_0 :unit). T)
        (\(_0 :unit). x);
      PMATCH_ROW (\(_0 :unit). [(2 :num)]) (\(_0 :unit). T)
        (\(_0 :unit). x);
      PMATCH_ROW (\(_0 :num). [_0]) (\(_0 :num). T)
        (\(_0 :num). (3 :num));
      PMATCH_ROW (\((_0 :num),(_1 :num),(_2 :num list)). _0::_1::_2)
        (\((_0 :num),(_1 :num),(_2 :num list)). T)
        (\((_0 :num),(_1 :num),(_2 :num list)). (3 :num))]”;

val t'' = “PMATCH xs
     [PMATCH_ROW (\(_uv:unit). []) (\_uv. T) (\_uv. x);
      PMATCH_ROW (\(_uv:unit). [2]) (\_uv. T) (\_uv. x);
      PMATCH_ROW (\v18. [v18]) (\v18. T) (\v18. 3);
      PMATCH_ROW (\(v12,v16,v17). v12::v16::v17) (\(v12,v16,v17). T)
        (\(v12,v16,v17). 3);
      PMATCH_ROW (\(_uv:unit). [2; 4; 3]) (\_uv. x > 5) (\_uv. 3 + x)]”

val _ = test (t, (SOME t'))
val _ = test_fast (t, (SOME t''))



(*************************************)
(* Removing DOUBLE-binds and guard   *)
(*************************************)

val t0 =
   “PMATCH (l :num list)
    [PMATCH_ROW (\(_uv :unit). ([] :num list)) (\(_uv :unit). T)
       (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((x :num),(y :num),(_0 :num list)). x::y::x::y::_0)
       (\((x :num),(y :num),(_0 :num list)). T)
       (\((x :num),(y :num),(_0 :num list)). x + y);
     PMATCH_ROW (\((x :num),(y :num),(_1 :num list)). x::x::x::y::_1)
       (\((x :num),(y :num),(_1 :num list)). T)
       (\((x :num),(y :num),(_1 :num list)). x + x + x);
     PMATCH_ROW (\((x :num),(_2 :num list)). x::_2)
       (\((x :num),(_2 :num list)). T)
       (\((x :num),(_2 :num list)). (1 :num))]”;

val t1 = “PMATCH l
     [PMATCH_ROW (\(_uv :unit). ([] :num list)) (\(_uv :unit). T)
        (\(_uv :unit). (0 :num));
      PMATCH_ROW
        (\((x :num),(y :num),(_0 :num list),(y' :num),(x' :num)).
           x::y::x'::y'::_0)
        (\((x :num),(y :num),(_0 :num list),(y' :num),(x' :num)).
           (y' = y) /\ (x' = x))
        (\((x :num),(y :num),(_0 :num list),(y' :num),(x' :num)).
           x + y);
      PMATCH_ROW
        (\((x :num),(y :num),(_1 :num list),(x'' :num),(x' :num)).
           x::x'::x''::y::_1)
        (\((x :num),(y :num),(_1 :num list),(x'' :num),(x' :num)).
           (x'' = x) /\ (x' = x))
        (\((x :num),(y :num),(_1 :num list),(x'' :num),(x' :num)).
           x + x + x);
      PMATCH_ROW (\((x :num),(_2 :num list)). x::_2)
        (\((x :num),(_2 :num list)). T)
        (\((x :num),(_2 :num list)). (1 :num))]”;

val t2 = “
   PMATCH l
     [PMATCH_ROW (\(_0 :unit). ([] :num list)) (\(_0 :unit). T)
        (\(_0 :unit). (0 :num));
      PMATCH_ROW
        (\((x :num),(y :num),(_0 :num list),(y' :num),(x' :num)).
           x::y::x'::y'::_0)
        (\((x :num),(y :num),(_0 :num list),(y' :num),(x' :num)). T)
        (\((x :num),(y :num),(_0 :num list),(y' :num),(x' :num)).
           if (y' = y) /\ (x' = x) then x + y
           else
             PMATCH (x::y::x'::y'::_0)
               [PMATCH_ROW
                  (\((x :num),(_0 :num),(_1 :num list),(x'' :num),
                     (x' :num)).
                     x::x'::x''::_0::_1)
                  (\((x :num),(_0 :num),(_1 :num list),(x'' :num),
                     (x' :num)).
                     (x'' = x) /\ (x' = x))
                  (\((x :num),(_0 :num),(_1 :num list),(x'' :num),
                     (x' :num)).
                     x + x + x);
                PMATCH_ROW (\((_0 :num),(_2 :num list)). _0::_2)
                  (\((_0 :num),(_2 :num list)). T)
                  (\((_0 :num),(_2 :num list)). (1 :num))]);
      PMATCH_ROW (\((_0 :num),(_2 :num list)). _0::_2)
        (\((_0 :num),(_2 :num list)). T)
        (\((_0 :num),(_2 :num list)). (1 :num))]”

val _ = test_conv "PMATCH_REMOVE_DOUBLE_BIND_CONV" PMATCH_REMOVE_DOUBLE_BIND_CONV (t0, SOME t1);

val _ = test_conv "PMATCH_REMOVE_DOUBLE_BIND_CONV" PMATCH_REMOVE_DOUBLE_BIND_CONV (“case xy of
   | (x, x) when x > 0 => x + x
   | x.| (x, y) => x
   | (x, _) => SUC x”, SOME “
case xy of
     (x,x') when (x' = x) /\ x > 0 => x + x
   | (x,y') when (y' = y) => x
   | (x,_) => SUC x”)


val _ = test_conv "PMATCH_REMOVE_DOUBLE_BIND_CONV" PMATCH_REMOVE_DOUBLE_BIND_CONV (“case (xx:('a # 'a)) of (x, x) => T | _ => F”, SOME “case (xx:('a # 'a)) of (x, x') when (x' = x) => T | _ => F”) ;

val _ = test_conv "PMATCH_REMOVE_GUARDS_CONV" PMATCH_REMOVE_GUARDS_CONV (t1, SOME t2);

val t = “PMATCH ((y :num option),(x :num option),(l :num list))
    [PMATCH_ROW (\(x :num option). (SOME (0 :num),x,([] :num list)))
       (\(x :num option). T) (\(x :num option). x);
     PMATCH_ROW (\(z :num option). (SOME (1 :num),z,[(2 :num)]))
       (\(z :num option). F) (\(z :num option). z);
     PMATCH_ROW (\(x :num option). (SOME (3 :num),x,[(2 :num)]))
       (\(x :num option). IS_SOME x) (\(x :num option). x);
     PMATCH_ROW (\((z :num option),(y :num option)). (y,z,[(2 :num)]))
       (\((z :num option),(y :num option)). IS_SOME y)
       (\((z :num option),(y :num option)). y);
     PMATCH_ROW (\(z :num option). (SOME (1 :num),z,[(2 :num)]))
       (\(z :num option). F) (\(z :num option). z);
     PMATCH_ROW (\(x :num option). (SOME (3 :num),x,[(2 :num)]))
       (\(x :num option). IS_SOME x) (\(x :num option). x)]”;

val t' = “   PMATCH (y,l)
     [PMATCH_ROW (\(_0 :unit). (SOME (0 :num),([] :num list)))
        (\(_0 :unit). T) (\(_0 :unit). x);
      PMATCH_ROW (\(_0 :unit). (SOME (3 :num),[(2 :num)]))
        (\(_0 :unit). T)
        (\(_0 :unit). if IS_SOME x then x else SOME (3 :num));
      PMATCH_ROW (\(y :num option). (y,[(2 :num)]))
        (\(y :num option). T)
        (\(y :num option).
           if IS_SOME y then y else (PMATCH_INCOMPLETE :num option))]”;

val _ = test_conv "PMATCH_REMOVE_GUARDS_CONV" PMATCH_REMOVE_GUARDS_CONV (t, SOME t');


val _ = test_conv "PMATCH_REMOVE_GUARDS_CONV" PMATCH_REMOVE_GUARDS_CONV (“case (x, y) of
  | (x, 2) when EVEN x => x + x
  | (SUC x, y) when ODD x => y + x + SUC x
  | (SUC x, 1) => x
  | (x, _) => x+3”, SOME “case (x,y) of
     (x,2) =>
          if EVEN x then x + x
          else (case x of SUC x when ODD x => 2 + x + SUC x | x => x + 3)
   | (SUC x,y) =>
          if ODD x then y + x + SUC x
          else (case y of 1 => x | _ => SUC x + 3)
   | (x,_) => x + 3”);



val _ = test_conv "PMATCH_REMOVE_GUARDS_CONV" PMATCH_REMOVE_GUARDS_CONV (“case (x, y) of
  | (x, 0) when EVEN x => (SOME x, T)
  | (x, 0) => (SOME x, F)
  | (0, _) => (NONE, T)
  | (_, _) => (NONE, F)”, SOME “case (x,y) of
     (x,0) => if EVEN x then (SOME x,T) else (SOME x,F)
   | (0,_) => (NONE,T)
   | (_,_) => (NONE,F)”);


val _ = test_conv "SIMP_CONV (numLib.std_ss ++ PMATCH_REMOVE_GUARDS_ss) []" (SIMP_CONV (numLib.std_ss ++ PMATCH_REMOVE_GUARDS_ss) []) (
  “case x of
  | _ when x < 5 => 0
  | _ when x < 10 => 1
  | _ when x < 15 => 2
  | _ => 3”, SOME “if x < 5 then 0 else if x < 10 then 1 else if x < 15 then 2 else 3”);


(*************************************)
(* LIFTING BOOLEAN                   *)
(*************************************)


val _ = test_conv "DEPTH_CONV (PMATCH_LIFT_BOOL_CONV false)" (DEPTH_CONV (PMATCH_LIFT_BOOL_CONV false)) (“P1 /\ (P (case (l1:'a list, l2) of
  | ([], _) => []
  | (_, []) => []
  | (x::xs, y::ys) => [(x, y)])):bool”,
  SOME “P1 /\ (((l1 = ([]:'a list)) ==> P []) /\ ((l2 = []) ==> P []) /\
   (!x xs y ys. (l1 = x::xs) /\ (l2 = y::ys) ==> P [(x,y)]) /\
   (~PMATCH_IS_EXHAUSTIVE (l1,l2)
       [PMATCH_ROW (\_0. ([],_0)) (\_0. T) (\_0. []);
        PMATCH_ROW (\_0. (_0,[])) (\_0. T) (\_0. []);
        PMATCH_ROW (\(x,xs,y,ys). (x::xs,y::ys)) (\(x,xs,y,ys). T)
          (\(x,xs,y,ys). [(x,y)])] ==>
    P ARB))”)


val _ = test_conv "DEPTH_CONV (PMATCH_LIFT_BOOL_CONV true)" (DEPTH_CONV (PMATCH_LIFT_BOOL_CONV true)) (“P1 /\ (P (case (l1:'a list, l2) of
  | ([], _) => []
  | (_, []) => []
  | (x::xs, y::ys) => [(x, y)])):bool”,
  SOME “P1 /\ (((l1 = ([]:'a list)) ==> P []) /\ ((l2 = []) ==> P []) /\
   (!x xs y ys. (l1 = x::xs) /\ (l2 = y::ys) ==> P [(x,y)]))”)


val _ = test_conv "DEPTH_CONV (PMATCH_LIFT_BOOL_CONV false)" (DEPTH_CONV (PMATCH_LIFT_BOOL_CONV false)) (“P1 /\ (P (case (l1:'a list, l2:'c list) of
  | ([], _) => ([]:'b list)
  | (_, []) => [])):bool”,
  SOME “P1 /\ ((l1 = ([] :'a list)) ==> P ([] :'b list)) /\
   ((l2 = ([] :'c list)) ==> P ([] :'b list)) /\
   (~PMATCH_IS_EXHAUSTIVE (l1,l2)
       [PMATCH_ROW (\(_0 :'c list). (([] :'a list),_0))
          (\(_0 :'c list). T) (\(_0 :'c list). ([] :'b list));
        PMATCH_ROW (\(_0 :'a list). (_0,([] :'c list)))
          (\(_0 :'a list). T) (\(_0 :'a list). ([] :'b list))] ==>
    P (ARB :'b list))”)

val _ = test_conv "DEPTH_CONV (PMATCH_LIFT_BOOL_CONV true)" (DEPTH_CONV (PMATCH_LIFT_BOOL_CONV true)) (“P1 /\ (P (case (l1:'a list, l2:'c list) of
  | ([], _) => ([]:'b list)
  | (_, []) => [])):bool”,
  SOME “P1 /\ (((l1:'a list) = []) ==> P ([]:'b list)) /\ (((l2:'c list) = []) ==> P []) /\
   (PMATCH_ROW_COND_EX (l1,l2) (\(v2,v3,v6,v7). (v2::v3,v6::v7))
      (\(v2,v3,v6,v7). T) ==>
    P ARB)”)


val _ = Datatype.Datatype ‘
  tree = Empty
       | Red tree 'a tree
       | Black tree 'a tree’;


val balance_black_def = TotalDefn.Define ‘balance_black a n b =
   case (a,b) of
       | (Red (Red a x b) y c,d) =>
            (Red (Black a x b) y (Black c n d))
       | (Red a x (Red b y c),d) =>
            (Red (Black a x b) y (Black c n d))
       | (a,Red (Red b y c) z d) =>
            (Red (Black a n b) y (Black c z d))
       | (a,Red b y (Red c z d)) =>
            (Red (Black a n b) y (Black c z d))
       | other => (Black a n b)’

val tm = #2 (strip_forall (concl (balance_black_def)))

val _ = test_conv "PMATCH_LIFT_BOOL_CONV true" (PMATCH_LIFT_BOOL_CONV true) (tm, SOME “
   (!a' x b' y c.
      (a = Red (Red a' x b') y c) ==>
      (balance_black a n b = Red (Black a' x b') y (Black c n b))) /\
   (!a' x b' y c.
      (a = Red a' x (Red b' y c)) ==>
      (!p_1 p_1' p_1''.
         (Red p_1 p_1' p_1'' = a') ==>
         ((p_1 = a') /\ (p_1' = x) /\ (p_1'' = b')) /\ (x = y) /\
         (Red b' y c = c)) ==>
      (balance_black a n b = Red (Black a' x b') y (Black c n b))) /\
   (!b' y c z d.
      (b = Red (Red b' y c) z d) ==>
      (!p_1 p_1' p_1'' p_1''' p_1''''.
         (Red p_1 p_1' (Red p_1'' p_1''' p_1'''') = a) ==>
         ((p_1 = a) /\ (p_1' = n) /\ (p_1'' = b')) /\ (p_1''' = y) /\
         (p_1'''' = c) /\ (n = z) /\ (Red (Red b' y c) z d = d)) /\
      (!p_1 p_1' p_1'' p_1''' p_1''''.
         (Red (Red p_1 p_1' p_1'') p_1''' p_1'''' = a) ==>
         ((p_1 = a) /\ (p_1' = n) /\ (p_1'' = b')) /\ (p_1''' = y) /\
         (p_1'''' = c) /\ (n = z) /\ (Red (Red b' y c) z d = d)) ==>
      (balance_black a n b = Red (Black a n b') y (Black c z d))) /\
   (!b' y c z d.
      (b = Red b' y (Red c z d)) ==>
      (!p_1' p_1'' p_1'''.
         (Red p_1' p_1'' p_1''' = b') ==>
         (p_1' = b') /\ (p_1'' = y) /\ (p_1''' = c) /\ (y = z) /\
         (Red c z d = d)) /\
      (!p_1 p_1' p_1'' p_1''' p_1''''.
         (Red p_1 p_1' (Red p_1'' p_1''' p_1'''') = a) ==>
         ((p_1 = a) /\ (p_1' = n) /\ (p_1'' = b')) /\ (p_1''' = y) /\
         (p_1'''' = c) /\ (n = z) /\ (Red b' y (Red c z d) = d)) /\
      (!p_1 p_1' p_1'' p_1''' p_1''''.
         (Red (Red p_1 p_1' p_1'') p_1''' p_1'''' = a) ==>
         ((p_1 = a) /\ (p_1' = n) /\ (p_1'' = b')) /\ (p_1''' = y) /\
         (p_1'''' = c) /\ (n = z) /\ (Red b' y (Red c z d) = d)) ==>
      (balance_black a n b = Red (Black a n b') y (Black c z d))) /\
   ((!p_1' p_1'' p_1''' p_1'''' p_2.
       Red p_1' p_1'' (Red p_1''' p_1'''' p_2) <> b) /\
    (!p_1' p_1'' p_1''' p_1'''' p_2.
       Red (Red p_1' p_1'' p_1''') p_1'''' p_2 <> b) /\
    (!p_1 p_1' p_1'' p_1''' p_1''''.
       Red p_1 p_1' (Red p_1'' p_1''' p_1'''') <> a) /\
    (!p_1 p_1' p_1'' p_1''' p_1''''.
       Red (Red p_1 p_1' p_1'') p_1''' p_1'''' <> a) ==>
    (balance_black a n b = Black a n b))”)


(*********************************)
(* Pattern Compilation           *)
(*********************************)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case l of NONE => 0 | SOME x => x”, SOME “option_CASE l 0 (\x'. x')”)

val t = “case xyz of
  | (_, F, T) => 1
  | (F, T, _) => 2
  | (_, _, F) => 3
  | (_, _, T) => 4”

val test =  test_conv "PMATCH_CASE_SPLIT_CONV_HEU colHeu_first_col" (PMATCH_CASE_SPLIT_CONV_HEU colHeu_first_col) (t, SOME
  “pair_CASE xyz
     (\v v'.
        pair_CASE v'
          (\v'' v'''.
             if v then
               if v'' then if v''' then 4 else 3
               else if v''' then 1
               else 3
             else if v'' then 2
             else if v''' then 1
             else 3))”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV_HEU colHeu_last_col" (PMATCH_CASE_SPLIT_CONV_HEU colHeu_last_col) (t, SOME
  “pair_CASE xyz
     (\v v'.
        pair_CASE v'
          (\v'' v'''.
             if v''' then if v'' then if v then 4 else 2 else 1
             else if v'' then if v then 3 else 2
             else 3))”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (t, SOME
  “pair_CASE xyz
     (\v v'.
        pair_CASE v'
          (\v'' v'''.
             if v'' then if v then if v''' then 4 else 3 else 2
             else if v''' then 1
             else 3))”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (t, SOME
  “pair_CASE xyz
     (\v v'.
        pair_CASE v'
          (\v'' v'''.
             if v'' then if v then if v''' then 4 else 3 else 2
             else if v''' then 1
             else 3))”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case l of (SOME x, SOME y) => SOME (x+y) | _ => NONE”, SOME “pair_CASE l
     (\v v'.
        option_CASE v NONE
          (\x'. option_CASE v' NONE (\x''. SOME (x' + x''))))”
)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case x of 3 => 1 | _ => 0”, SOME “literal_case (\v. if v = 3 then 1 else 0) x”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case x of 0 => 1 | 1 => 1 | 2 => 2”, SOME “   literal_case
     (\x.
        if x = 0 then 1
        else if x = 1 then 1
        else if x = 2 then 2
        else ARB) x”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case x of 1 => 1 | 0 => 1 | 2 => 2”, SOME “   literal_case
     (\x.
        if x = 1 then 1
        else if x = 0 then 1
        else if x = 2 then 2
        else ARB) x”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case x of 1 => 1 | ().| c => 1”, SOME “   literal_case
     (\x.
        if x = 1 then 1
        else if x = c then 1
        else ARB) x”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case x of 1 => 1 | ().| c => 2 | ().| d => 3”, SOME “   literal_case
     (\x.
        if x = 1 then 1
        else if x = c then 2
        else if x = d then 3
        else ARB) x”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case x of 0 => 1 | SUC 0 => 1 | SUC (SUC 0) => 2”, SOME “
        num_CASE x 1
          (\n. num_CASE n 1 (\n'. num_CASE n' 2 (\n''. ARB)))”)


val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case l of [] => 1 | [_;_] => 2 | [3] => 3 |  [_] => 4 | _ => 5”, SOME “
    list_CASE l 1
     (\h t.
        list_CASE t (literal_case (\x. if x = 3 then 3 else 4) h)
          (\h' t'. list_CASE t' 2 (\h'' t''. 5)))”)

val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case xy of (0,0) => 1 | (1,1) => 1 | (1,2) => 2”, SOME “pair_CASE xy
     (\v v'.
        literal_case
          (\x.
             if x = 0 then num_CASE v' 1 (\n. ARB)
             else if x = 1 then
               literal_case
                 (\x'. if x' = 1 then 1 else if x' = 2 then 2 else ARB)
                 v'
             else ARB) v)”)


val test =  test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
  “case xy of (0,0) => 1 | (1,1) => 1 | ().| (c,3) => 3 | (1,2) => 2 | ().| (c, 4) => 2”, SOME “pair_CASE xy
     (\v v'.
        literal_case
          (\x.
             if x = 0 then num_CASE v 1 (\n. ARB)
             else if x = 1 then
               literal_case (\x'. if x' = 1 then 1 else ARB) v
             else if x = 3 then
               literal_case (\x''. if x'' = c then 3 else ARB) v
             else if x = 2 then
               literal_case (\x'''. if x''' = 1 then 2 else ARB) v
             else if x = 4 then
               literal_case (\x''''. if x'''' = c then 2 else ARB) v
             else ARB) v')”)


val list_REVCASE_def = TotalDefn.Define ‘
  list_REVCASE l c_nil c_snoc =
    (if l = [] then c_nil else (
     c_snoc (LAST l) (BUTLAST l)))’

val list_REVCASE_THM = prove (“
  ((list_REVCASE [] c_nil c_snoc) = c_nil) /\
  ((list_REVCASE (SNOC x xs) c_nil c_snoc) = c_snoc x xs)”,
SIMP_TAC numLib.std_ss [list_REVCASE_def, rich_listTheory.NOT_SNOC_NIL, LAST_SNOC, FRONT_SNOC])

val cl = make_constructorList true [
  (“[]:'a list”, []),
  (“SNOC: 'a -> 'a list -> 'a list”,  ["x", "xs"])
]

(* set_constructorFamily (cl, ``list_REVCASE``) *)
val cf = mk_constructorFamily (cl, “list_REVCASE”,
  SIMP_TAC list_ss [rich_listTheory.NOT_SNOC_NIL] THEN
  REPEAT STRIP_TAC THENL [
    ASSUME_TAC (Q.SPEC ‘x’ listTheory.SNOC_CASES) THEN
    FULL_SIMP_TAC numLib.std_ss [list_REVCASE_THM],

    ASSUME_TAC (Q.SPEC ‘x’ listTheory.SNOC_CASES) THEN
    FULL_SIMP_TAC numLib.std_ss [list_REVCASE_THM],
    PROVE_TAC [listTheory.SNOC_CASES]
  ]
)

(* add this family *)
val _ = pmatch_compile_db_register_constrFam cf

val test = test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
 “case l of
  | [] => 0
  | SNOC x _ => x”, SOME “list_REVCASE l 0 (\x' xs. x')”)

val test = test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
 “case lx of
  | (_, NONE) => 0
  | (SNOC x _, SOME y) => x + y”, SOME “pair_CASE lx
     (\v v'.
        option_CASE v' 0 (\x'. list_REVCASE v ARB (\x'' xs. x'' + x')))”)

val test = test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
 “case lx of
  | [] => 0
  | x::_ => x + y
  ”, SOME “list_CASE lx 0 (\h t. h + y)”)

val test = test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
 “case lx of
  | [] => 0
  | SNOC x _ => x
  | x::_ => x + y
  ”, NONE)


val tree_case_def = DB.fetch "-" "tree_case_def";

val tree_red_CASE_def = TotalDefn.Define ‘
 tree_red_CASE tr f_red f_else =
 tree_CASE tr (f_else Empty) f_red
   (\t1 n t2. f_else (Black t1 n t2))’

val tree_red_CASE_THM = prove (“
  (tree_red_CASE Empty f_red f_else = f_else Empty) /\
  (tree_red_CASE (Red t1 n t2) f_red f_else = f_red t1 n t2) /\
  (tree_red_CASE (Black t1 n t2) f_red f_else = f_else (Black t1 n t2))”,
SIMP_TAC list_ss [tree_red_CASE_def, tree_case_def])

val cl = make_constructorList false [
  (“Red : 'a tree -> 'a -> 'a tree -> 'a tree”, ["t1", "n", "t2"])
]

(* set_constructorFamily (cl, ``tree_red_CASE``) *)
val cf = mk_constructorFamily (cl, “tree_red_CASE”,
  SIMP_TAC (srw_ss()) [tree_red_CASE_def] THEN
  CONJ_TAC THEN (
    Cases_on ‘x’ THEN
    SIMP_TAC (srw_ss()) [tree_red_CASE_def]
  ));

val _ = pmatch_compile_db_register_constrFam cf;

val test = test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
 “case (t:'a tree) of
  | Red _ _ _ => T
  | _ => F
  ”, SOME (“tree_red_CASE (t:'a tree) (\t a t0. T) (\x. F)”))

val test = test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
 “case (t:'a tree) of
  | Black _ _ _ => T
  | _ => F
  ”, SOME (“tree_CASE (t:'a tree) F (\t a t0. F) (\t' a' t0'. T)”))


(*********************************)
(* Compilation to nchotomies     *)
(*********************************)

fun test_nchot (inp,out) =
    let
      val _ = tprint ("nchotomy_of_pats: [" ^
                      String.concatWith "," (map term_to_string inp) ^ "]")
    in
      require_msg (check_result (aconv out o concl)) thm_to_string
                  (quietly nchotomy_of_pats)
                  inp
    end

val _ =  test_nchot ([“\x:unit. (NONE : num option)”,
   “\x:num. SOME x”] , “!x. (x = NONE) \/ ?v1:num. x = SOME v1”)

val _ =  test_nchot ([“\x:num. x”, “\x:num. x”],
  “!x. ?v0:num. x = v0”)

val _ =  test_nchot ([
   “\v:bool. (v, F, T)”,
   “\v:bool. (F, T, v)”,
   “\(v1:bool, v2:bool). (v1, v2, F)”,
   “\(v1:bool, v2:bool). (v1, v2, F)”],
   “!x.
     (x = (T,T,T)) \/ (x = (T,T,F)) \/ (x = (F,T,T)) \/ (x = (F,T,F)) \/
     (?v0. x = (v0,F,T)) \/ ?v0. x = (v0,F,F)”)

val _ =  test_nchot ([
   “\(x:num, y:num). (SOME x, SOME y)”,
   “\(x : num option, y : num option). (x, y)”],
   “!x.
     (?v1. x = (NONE,v1)) \/ (?v2. x = (SOME v2,NONE)) \/
     ?(v2:num) (v3:num). x = (SOME v2,SOME v3)”)

val _ =  test_nchot ([“\_:unit. 3”, “\x:num. x”],
  “!x. (x = 3) \/ ?v1. v1 <> 3 /\ (x = v1)”)

val _ =  test_nchot ([“\_:unit. 0”, “\_:unit. SUC 0”, “\_:unit. SUC (SUC 0)”],
  “!x. (x = 0) \/ (x = SUC 0) \/ (x = SUC (SUC 0)) \/
     ?v3. x = SUC (SUC (SUC v3))”)


(*********************************)
(* Fancy redundancy removal      *)
(*********************************)

val t =
   “PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\(_2 :'a option). (_2,(NONE :'b option)))
       (\(_2 :'a option). T) (\(_2 :'a option). (2 :num))]”;

val t' = “
   PMATCH (x,z)
     [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
      PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
        (\((_1 :'b option),(_0 :'a)). T)
        (\((_1 :'b option),(_0 :'a)). (1 :num))]”;

val _ = test_conv "PMATCH_REMOVE_REDUNDANT_CONV" PMATCH_REMOVE_REDUNDANT_CONV (t, SOME t');


(*********************************)
(* Exhaustiveness                *)
(*********************************)

fun precond_check (inp, out) res =
    let
      val (r, _) = dest_imp_only (concl res)
    in
      r ~~ out
    end
fun test_precond nm c (inp,outopt) =
    case outopt of
        SOME t =>
        let
          val _ = tprint (pterm_to_string (nm ^ "[precond]") inp)
        in
          require_msg (check_result (precond_check(inp,t))) thm_to_string
                      (quietly c) inp
        end
      | NONE => shouldfail {checkexn = K true,
                            printarg = pterm_to_string (nm ^ "[precond](exn)"),
                            printresult = thm_to_string, testfn = quietly c}
                           inp

fun rhs_check exp th = rhs (concl th) ~~ exp
fun test_rhs nm c (inp,outopt) =
    case outopt of
        SOME t =>
        let
          val _ = tprint (pterm_to_string (nm ^ "[rhs]") inp)
        in
          require_msg (check_result (rhs_check t)) thm_to_string (quietly c) inp
        end
      | NONE => shouldfail {checkexn = K true,
                            printarg = pterm_to_string (nm ^ "[rhs](exn)"),
                            printresult = thm_to_string, testfn = quietly c}
                           inp;

val t =
   “PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\((_3 :'b),(_2 :'a option)). (_2,SOME _3))
       (\((_3 :'b),(_2 :'a option)). T)
       (\((_3 :'b),(_2 :'a option)). (2 :num))]”;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK (t, SOME “~F”)

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK (t, SOME “~F”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_CHECK" PMATCH_IS_EXHAUSTIVE_CHECK (t, SOME T)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_FAST_CHECK" PMATCH_IS_EXHAUSTIVE_FAST_CHECK (t, NONE)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK (t, SOME T)


val t =
   “PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\((_3 :'b option),(_2 :'a option)). (_2,_3))
       (\((_3 :'b option),(_2 :'a option)). T)
       (\((_3 :'b option),(_2 :'a option)). (2 :num))]”;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK (t, SOME “~F”)

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK (t, SOME “~F”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_CHECK" PMATCH_IS_EXHAUSTIVE_CHECK (t, SOME T)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_FAST_CHECK" PMATCH_IS_EXHAUSTIVE_FAST_CHECK (t, SOME T)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK (t, SOME T)


val t =
   “PMATCH (xy : ('a option # 'b option))
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\ (_3 : ('a option # 'b option)). _3)
       (\_. T)
       (\_. (2 :num))]”;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK (t, SOME “~F”)

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK (t, SOME “~F”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_CHECK" PMATCH_IS_EXHAUSTIVE_CHECK (t, SOME T)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_FAST_CHECK" PMATCH_IS_EXHAUSTIVE_FAST_CHECK (t, SOME T)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK (t, SOME T)

val t =
   “PMATCH (xy : ('a option # 'b option))
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\((_3 :'b option),(_2 :'a option)). (_2,_3))
       (\((_3 :'b option),(_2 :'a option)). T)
       (\((_3 :'b option),(_2 :'a option)). (2 :num))]”;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK (t, SOME “~F”)

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK (t, SOME “~F”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_CHECK" PMATCH_IS_EXHAUSTIVE_CHECK (t, SOME T)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_FAST_CHECK" PMATCH_IS_EXHAUSTIVE_FAST_CHECK (t, SOME T)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK (t, SOME T)


val t =“PMATCH xy []”;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK (t, NONE)

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK (t, SOME “F”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_CHECK" PMATCH_IS_EXHAUSTIVE_CHECK (t, SOME F)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_FAST_CHECK" PMATCH_IS_EXHAUSTIVE_FAST_CHECK (t, SOME F)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK (t, NONE)


val t =
   “PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_3 :'b),(_2 :'a option)). (_2,SOME _3))
       (\((_3 :'b),(_2 :'a option)). T)
       (\((_3 :'b),(_2 :'a option)). (2 :num))]”;

val t' = “PMATCH (x,z)
     [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
      PMATCH_ROW (\((_3 :'b),(_2 :'a option)). (_2,SOME _3))
        (\((_3 :'b),(_2 :'a option)). T)
        (\((_3 :'b),(_2 :'a option)). (2 :num));
      PMATCH_ROW (\(v3 :'a). (SOME v3,(NONE :'b option))) (\(v3 :'a). T)
        (\(v3 :'a). (ARB :num))]”

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK (t, SOME “~PMATCH_ROW_COND_EX (x,z) (\v3. (SOME v3,NONE)) (\v3. T)”)

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK (t, SOME “~PMATCH_ROW_COND_EX (x,z) (\v3. (SOME v3,NONE)) (\v3. T)”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_CHECK" PMATCH_IS_EXHAUSTIVE_CHECK (t, SOME “~PMATCH_ROW_COND_EX (x,z) (\v3. (SOME v3,NONE)) (\v3. T)”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_FAST_CHECK" PMATCH_IS_EXHAUSTIVE_FAST_CHECK (t, NONE)

val _ = test_conv "PMATCH_COMPLETE_CONV true" (PMATCH_COMPLETE_CONV true) (t, SOME t')

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK (t, SOME “~PMATCH_ROW_COND_EX (x,z) (\v3. (SOME v3,NONE)) (\v3. T)”)

val t =
   “PMATCH (SOME x, NONE)
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_3 :'b),(_2 :'a option)). (_2,SOME _3))
       (\((_3 :'b),(_2 :'a option)). T)
       (\((_3 :'b),(_2 :'a option)). (2 :num))]”;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK (t, SOME “~PMATCH_ROW_COND_EX (SOME x,NONE) (\v3. (SOME v3,NONE)) (\v3. T)”)

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK (t, SOME “F”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_CHECK" PMATCH_IS_EXHAUSTIVE_CHECK (t, SOME F)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_FAST_CHECK" PMATCH_IS_EXHAUSTIVE_FAST_CHECK (t, SOME F)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK (t, SOME
“~PMATCH_ROW_COND_EX (SOME x,NONE) (\v3. (SOME v3,NONE)) (\v3. T)”)


val t =
   “PMATCH (NONE, SOME b)
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_3 :'b),(_2 :'a option)). (_2,SOME _3))
       (\((_3 :'b),(_2 :'a option)). T)
       (\((_3 :'b),(_2 :'a option)). (2 :num))]”;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK (t, SOME “~PMATCH_ROW_COND_EX (NONE,SOME b) (\v3. (SOME v3,NONE)) (\v3. T)”)

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK (t, SOME “~F”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_CHECK" PMATCH_IS_EXHAUSTIVE_CHECK (t, SOME T)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_FAST_CHECK" PMATCH_IS_EXHAUSTIVE_FAST_CHECK (t, SOME T)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK (t, SOME T)


val t = “PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\(_2 :'a option). (_2,(NONE :'b option)))
       (\(_2 :'a option). T) (\(_2 :'a option). (2 :num))]”;

val p = “~PMATCH_ROW_COND_EX ((x :'a option),(z :'b option))
      (\(v3 :'b). ((NONE :'a option),SOME v3)) (\(v3 :'b). T)”

val t' = “PMATCH (x,z)
     [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
      PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
        (\((_1 :'b option),(_0 :'a)). T)
        (\((_1 :'b option),(_0 :'a)). (1 :num));
      PMATCH_ROW (\(_2 :'a option). (_2,(NONE :'b option)))
        (\(_2 :'a option). T) (\(_2 :'a option). (2 :num));
      PMATCH_ROW (\(v3 :'b). ((NONE :'a option),SOME v3)) (\(v3 :'b). T)
        (\(v3 :'b). (ARB :num))]”;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK (t, SOME “ ~PMATCH_ROW_COND_EX (x,z) (\v3. (NONE,SOME v3)) (\v3. T)”)

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK" PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK (t, SOME “ ~PMATCH_ROW_COND_EX (x,z) (\v3. (NONE,SOME v3)) (\v3. T)”)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_CHECK" PMATCH_IS_EXHAUSTIVE_CHECK (t, SOME p)

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_FAST_CHECK" PMATCH_IS_EXHAUSTIVE_FAST_CHECK (t, NONE)

val _ = test_conv "PMATCH_COMPLETE_CONV true" (PMATCH_COMPLETE_CONV true) (t, SOME t')

val _ = test_rhs "PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK" PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK (t, SOME p)


(*********************************)
(* LIFTING                       *)
(*********************************)

val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“case t of [] => 0 | x::_ => x”, NONE)

val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“SUC (case t of [] => 0 | x::_ => x)”, SOME
   “case t of [] => SUC 0 | x::_ => SUC x”)

val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“SUC ((\c. (case t of [] => 0 | x::_ => x) + c) 5)”, SOME
   “case t of [] => SUC ((\c. 0 + c) 5) | x::_ => SUC ((\c. x + c) 5)”)

val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“(\c. (case t of [] => 0 | x::_ => x) + c)”, SOME
   “case t of [] => (\c. 0 + c) | x::_ => (\c. x + c)”)

val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“SUC ((\c. (case t of [] => c | x::_ => x) + c) 5)”, NONE)

val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“(\c. (case t of [] => c | x::_ => x) + c)”, NONE)

val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“SUC (case t of [] => 0)”, SOME
   “case t of [] => SUC 0 | v1::v2 => SUC ARB”)

val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“SUC ((\c. (case t of [] => 0) + c) 5)”, SOME
   “case t of [] => SUC ((\c. 0 + c) 5) | _::_ => SUC ((\c. ARB + c) 5)”)

val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“(\c. (case t of [] => 0) + c)”, SOME
   “case t of [] => (\c. 0 + c) | _::_ => (\c. ARB + c)”)


val _ = test_conv "PMATCH_LIFT_CONV" PMATCH_LIFT_CONV
  (“(\c. (case t of [] => 0) + c + 2 * (case t of [] => 0))”, SOME
   “case t of [] => (\c. 0 + c + 2 * 0) | _::_ => (\c. ARB + c + 2 * ARB)”)


(*********************************)
(* EXTENDING INPUT               *)
(*********************************)

val _ = test_conv "PMATCH_EXTEND_INPUT_CONV" (PMATCH_EXTEND_INPUT_CONV “(n:num, l:num list)”)
  (“case (l, n) of ([], _) => c | (x::_, SUC m) => x + m”, SOME
   “PMATCH ((n :num),(l :num list))
     [PMATCH_ROW (\(_0 :num). (_0,([] :num list))) (\(_0 :num). T)
        (\(_0 :num). c);
      PMATCH_ROW (\((x :num),(_0 :num list),(m :num)). (SUC m,x::_0))
        (\((x :num),(_0 :num list),(m :num)). T)
        (\((x :num),(_0 :num list),(m :num)). x + m)]”)


val _ = test_conv "PMATCH_EXTEND_INPUT_CONV" (PMATCH_EXTEND_INPUT_CONV “(x1: 'a, n:num, x2:'b, l:num list, x3:'c)”)
  (“case (l, n) of ([], _) => c | (x::_, SUC m) => x + m”, SOME
   “PMATCH ((x1 :'a),n,(x2 :'b),l,(x3 :num))
     [PMATCH_ROW
        (\((_0 :num),(_1 :'a),(_2 :'b),(_3 :num)).
           (_1,_0,_2,([] :num list),_3))
        (\((_0 :num),(_1 :'a),(_2 :'b),(_3 :num)). T)
        (\((_0 :num),(_1 :'a),(_2 :'b),(_3 :num)). c);
      PMATCH_ROW
        (\((x :num),(_0 :num list),(m :num),(_1 :'a),(_2 :'b),
           (_3 :num)).
           (_1,SUC m,_2,x::_0,_3))
        (\((x :num),(_0 :num list),(m :num),(_1 :'a),(_2 :'b),
           (_3 :num)).
           T)
        (\((x :num),(_0 :num list),(m :num),(_1 :'a),(_2 :'b),
           (_3 :num)).
           x + m)]”)


val _ = test_conv "PMATCH_EXTEND_INPUT_CONV" (PMATCH_EXTEND_INPUT_CONV “(x1: 'a, n:num, n, x2:'b, l:num list, x3:'c)”)
  (“case (l, n) of ([], _) => c | (x::_, SUC m) => x + m”, SOME
   “PMATCH ((x1 :'a),n,n,(x2 :'b),l,(x3 :num))
     [PMATCH_ROW
        (\((_0 :num),(_1 :'a),(_2 :num),(_3 :'b),(_4 :num)).
           (_1,_0,_2,_3,([] :num list),_4))
        (\((_0 :num),(_1 :'a),(_2 :num),(_3 :'b),(_4 :num)). T)
        (\((_0 :num),(_1 :'a),(_2 :num),(_3 :'b),(_4 :num)). c);
      PMATCH_ROW
        (\((x :num),(_0 :num list),(m :num),(_1 :'a),(_2 :num),(_3 :'b),
           (_4 :num)).
           (_1,SUC m,_2,_3,x::_0,_4))
        (\((x :num),(_0 :num list),(m :num),(_1 :'a),(_2 :num),(_3 :'b),
           (_4 :num)).
           T)
        (\((x :num),(_0 :num list),(m :num),(_1 :'a),(_2 :num),(_3 :'b),
           (_4 :num)).
           x + m)]”)


val _ = test_conv "PMATCH_EXTEND_INPUT_CONV" (PMATCH_EXTEND_INPUT_CONV “(c:num, n:num, l:num list)”)
  (“case (l, n) of ([], _) => c | (x::_, SUC m) => x + m + n”, SOME
   “PMATCH (c,n,l)
     [PMATCH_ROW (\(_0,c). (c,_0,[])) (\(_0,c). T) (\(_0,c). c);
      PMATCH_ROW (\(x,_0,m,_1). (_1,SUC m,x::_0)) (\(x,_0,m,_1). T)
        (\(x,_0,m,_1). x + m + SUC m)]”)


(*********************************)
(* FLATTENING                    *)
(*********************************)

val _ = test_conv "PMATCH_FLATTEN_CONV false" (PMATCH_FLATTEN_CONV false)
  (“case (x, y) of ([], x::xs) => (
           case xs of [] => 1 + x | (x::xs) => 5 + x + LENGTH xs) | (_, []) => 1”,
   SOME “PMATCH (x,y)
     [PMATCH_ROW (\x. ([],[x])) (\x. T) (\x. 1 + x);
      PMATCH_ROW (\(x,xs,_0). ([],_0::x::xs)) (\(x,xs,_0). T)
        (\(x,xs,_0). 5 + x + LENGTH xs);
      PMATCH_ROW (\_0. (_0,[])) (\_0. T) (\_0. 1)]”)

val _ = test_conv "PMATCH_FLATTEN_CONV true" (PMATCH_FLATTEN_CONV true)
  (“case (x, y) of ([], x::xs) => (
           case xs of [] => 1 + x | (x::xs) => 5 + x + LENGTH xs) | (_, []) => 1”,
   SOME “PMATCH (x,y)
     [PMATCH_ROW (\x. ([],[x])) (\x. T) (\x. 1 + x);
      PMATCH_ROW (\(x,xs,_0). ([],_0::x::xs)) (\(x,xs,_0). T)
        (\(x,xs,_0). 5 + x + LENGTH xs);
      PMATCH_ROW (\_0. (_0,[])) (\_0. T) (\_0. 1)]”)

val _ = test_conv "PMATCH_FLATTEN_CONV false" (PMATCH_FLATTEN_CONV false)
  (“case (x, y) of ([], x::xs) => SUC (
           case xs of [] => 1 + x | (x::xs) => 5 + x + LENGTH xs) | (_, []) => 1”,
   NONE)


val _ = test_conv "PMATCH_FLATTEN_CONV true" (PMATCH_FLATTEN_CONV true)
  (“case (x, y) of ([], x::xs) => SUC (
       case xs of [] => 1 + x | (x::xs) => 5 + x + LENGTH xs) | (_, []) => 1”,
   SOME “PMATCH (x,y)
     [PMATCH_ROW (\x. ([],[x])) (\x. T) (\x. SUC (1 + x));
      PMATCH_ROW (\(x,xs,_0). ([],_0::x::xs)) (\(x,xs,_0). T)
        (\(x,xs,_0). SUC (5 + x + LENGTH xs));
      PMATCH_ROW (\_0. (_0,[])) (\_0. T) (\_0. 1)]”)


val _ = test_conv "PMATCH_FLATTEN_CONV true" (PMATCH_FLATTEN_CONV true)
  (“case (x, y) of ([], x::xs) => SUC (
       case xs of [] => 1 + x | (x::xs) => 5 + x + LENGTH xs) | (y::ys, []) => (case y of 0 => 1 | _ => 2)”,
   SOME “PMATCH (x,y)
     [PMATCH_ROW (\x. ([],[x])) (\x. T) (\x. SUC (1 + x));
      PMATCH_ROW (\(x,xs,_0). ([],_0::x::xs)) (\(x,xs,_0). T)
        (\(x,xs,_0). SUC (5 + x + LENGTH xs));
      PMATCH_ROW (\_1. (0::_1,[])) (\_1. T) (\_1. 1);
      PMATCH_ROW (\(_0,_1). (_0::_1,[])) (\(_0,_1). T) (\(_0,_1). 2)]”)


val _ = test_conv "PMATCH_FLATTEN_CONV true" (PMATCH_FLATTEN_CONV true)
  (“case (x, y) of ([], x::xs) => SUC (
       case xs of [] => 1 + x | (x::xs) => 5 + x + LENGTH xs) | (y::ys, []) => (case z of 0 => 1 | _ => 2)”,
   SOME “PMATCH (x,y)
     [PMATCH_ROW (\x. ([],[x])) (\x. T) (\x. SUC (1 + x));
      PMATCH_ROW (\(x,xs,_0). ([],_0::x::xs)) (\(x,xs,_0). T)
        (\(x,xs,_0). SUC (5 + x + LENGTH xs));
      PMATCH_ROW (\(_0,_1). (_0::_1,[])) (\(_0,_1). T)
        (\(_0,_1).
           PMATCH z
             [PMATCH_ROW (\_:unit. 0) (\_. T) (\_. 1);
              PMATCH_ROW (\_0. _0) (\_0. T) (\_0. 2)])]”)


(*********************************)
(* EVAL                          *)
(*********************************)

fun mk_t t  = “PMATCH (^t :num list)
    [PMATCH_ROW (\((y :num),(_0 :num)). [_0; y])
       (\((y :num),(_0 :num)). T) (\((y :num),(_0 :num)). y);
     PMATCH_ROW (\((x :num),(_2 :num),(_1 :num)). [x; _1; _2])
       (\((x :num),(_2 :num),(_1 :num)). T)
       (\((x :num),(_2 :num),(_1 :num)). x);
     PMATCH_ROW (\((x :num),(y :num),(_3 :num list)). x::y::_3)
       (\((x :num),(y :num),(_3 :num list)). T)
       (\((x :num),(y :num),(_3 :num list)). x + y);
     PMATCH_ROW (\(_uv :unit). ([] :num list)) (\(_uv :unit). T)
       (\(_uv :unit). (0 :num));
     PMATCH_ROW (\(_4 :num list). _4) (\(_4 :num list). T)
       (\(_4 :num list). (1 :num))]”;

fun run_test (t, r) =
  test_conv "EVAL_CONV" EVAL_CONV (mk_t t, SOME r);

val _ = run_test (“[] : num list”, “0”);
val _ = run_test (“[2;3] : num list”, “3”);
val _ = run_test (“[2;30] : num list”, “30”);
val _ = run_test (“[2;3;4] : num list”, “2”);
val _ = run_test (“[4;3;4] : num list”, “4”);
val _ = run_test (“[4;3;4;3] : num list”, “7”);
val _ = run_test (“(4::3::l) : num list”, “PMATCH ((4 :num)::(3 :num)::l)
     [PMATCH_ROW (\((y :num),(_0 :num)). [_0; y])
        (\((y :num),(_0 :num)). T) (\((y :num),(_0 :num)). y);
      PMATCH_ROW (\((x :num),(_2 :num),(_1 :num)). [x; _1; _2])
        (\((x :num),(_2 :num),(_1 :num)). T)
        (\((x :num),(_2 :num),(_1 :num)). x);
      PMATCH_ROW (\((x :num),(y :num),(_3 :num list)). x::y::_3)
        (\((x :num),(y :num),(_3 :num list)). T)
        (\((x :num),(y :num),(_3 :num list)). x + y)]”);

val _ = test_conv "EVAL_CONV" EVAL_CONV (“case [] of x::xs => SUC x”, SOME “ARB:num”);

val _ = test_conv "EVAL_CONV" EVAL_CONV (“case [] of SNOC x xs => SUC x”, SOME “ARB:num”);

val _ = test_conv "EVAL_CONV" EVAL_CONV (“case [] of [] => 0 | SNOC x xs => SUC x”, SOME “0”);

val _ = test_conv "EVAL_CONV" EVAL_CONV (“case SNOC x xs of [] => 0 | SNOC x xs => SUC x”, SOME “SUC x”);

val test = test_conv "PMATCH_CASE_SPLIT_CONV" PMATCH_CASE_SPLIT_CONV (
 “case lx of
  | [] => 0
  | SNOC x _ => x
  | x::_ => x + y
  ”, NONE)
