open HolKernel Parse boolTheory boolLib pairTheory
open constrFamiliesLib patternMatchesLib computeLib
open quantHeuristicsLib simpLib boolSimps

val hard_fail = true;
val quiet = false;
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

(* For manual

set_trace "use pmatch_pp" 0
val hard_fail = false;
val quiet = false;
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;

*)

fun test_conv_gen dest s conv (t, r_opt) =
let
    open PPBackEnd Parse
    val _ = print (if quiet then "``" else "Testing "^s^" ``");
    val _ = print_term t;
    val _ = print ("``\n   ");
    val ct = Timer.startCPUTimer();
    val thm_opt = SOME (conv t) handle Interrupt => raise Interrupt
                                     | _ => NONE;

    val ok = if not (isSome r_opt) then not (isSome thm_opt) else
             isSome thm_opt andalso
             let
                val thm_t = concl (valOf thm_opt);
                val (t'_opt, r') = dest thm_t;
             in
               (aconv r' (valOf r_opt)) andalso
               case t'_opt of
                    SOME t' => (aconv t' t)
                  | _ => true
             end handle HOL_ERR _ => false
    val quiet = quiet andalso ok
    val _ = if ok then
               print_with_style [FG Green] "OK "
            else
               (print_with_style [FG OrangeRed] "FAILED ")

    val d_time = #usr (Timer.checkCPUTimer ct);
    val _ = print ((Time.toString d_time)^ " s");
    val _ = if quiet then () else print ("\n   ");

    val _ = if quiet then () else
       let
          val _ = print "---> ";
          val _ = if isSome thm_opt then (print_thm (valOf thm_opt);print "\n")
                  else print "-\n"
          val _ = if (not ok) then
                     (print "   EXPECTED ";
                      if isSome r_opt then (print "``";print_term (valOf r_opt);print "``\n")
                      else print "-\n")
                  else ()
       in () end
    val _ = print "\n";
    val _ = if (not ok andalso hard_fail) then Process.exit Process.failure else ();
in
    ()
end;


val test_conv = test_conv_gen (fn t => let
  val (l, r) = dest_eq t
in
  (SOME l, r)
end)


(******************************************************************************)
(* Converting from existing decision trees                                    *)
(******************************************************************************)

val tc = test_conv "PMATCH_INTRO_CONV" PMATCH_INTRO_CONV

val t = ``case x of (NONE, []) => 0``;
val r_thm = SOME ``PMATCH (x :'a option # 'b list)
    [PMATCH_ROW (\(uv :unit). ((NONE :'a option),([] :'b list)))
       (\(uv :unit). T) (\(uv :unit). (0 :num))]``
val _ = tc (t, r_thm);

val t = ``case x of
   (NONE, []) => 0
 | (SOME 2, []) => 2
 | (SOME 3, (x :: xs)) => 3 + x
 | (SOME _, (x :: xs)) => x``
val r_thm = SOME ``PMATCH x
     [PMATCH_ROW (\(uv :unit). ((NONE :num option),([] :num list)))
        (\(uv :unit). T) (\(uv :unit). (0 :num));
      PMATCH_ROW (\(uv :unit). (SOME (2 :num),([] :num list)))
        (\(uv :unit). T) (\(uv :unit). (2 :num));
      PMATCH_ROW (\((x :num),(_0 :num list)). (SOME (3 :num),x::_0))
        (\((x :num),(_0 :num list)). T)
        (\((x :num),(_0 :num list)). (3 :num) + x);
      PMATCH_ROW (\((_0 :num),(x :num),(_1 :num list)). (SOME _0,x::_1))
        (\((_0 :num),(x :num),(_1 :num list)). T)
        (\((_0 :num),(x :num),(_1 :num list)). x)]``
val _ = tc (t, r_thm);



val tcn = test_conv "PMATCH_INTRO_CONV_NO_OPTIMISE" PMATCH_INTRO_CONV_NO_OPTIMISE

val t = ``case x of (NONE, []) => 0``
val r_thm = SOME ``PMATCH x
     [PMATCH_ROW (\(uv :unit). ((NONE :'a option),([] :'b list)))
        (\(uv :unit). T) (\(uv :unit). (0 :num));
      PMATCH_ROW (\((v4 :'b),(v5 :'b list)). ((NONE :'a option),v4::v5))
        (\((v4 :'b),(v5 :'b list)). T)
        (\((v4 :'b),(v5 :'b list)). (ARB :num));
      PMATCH_ROW (\((v2 :'a),(v1 :'b list)). (SOME v2,v1))
        (\((v2 :'a),(v1 :'b list)). T)
        (\((v2 :'a),(v1 :'b list)). (ARB :num))]``
val _ = tcn (t, r_thm);

val t = ``case x of
   (NONE, []) => 0
 | (SOME 2, []) => 2
 | (SOME 3, (x :: xs)) => 3 + x
 | (SOME _, (x :: xs)) => x``
val r_thm = SOME ``
   PMATCH x
     [PMATCH_ROW (\(uv :unit). ((NONE :num option),([] :num list)))
        (\(uv :unit). T) (\(uv :unit). (0 :num));
      PMATCH_ROW (\(uv :unit). (SOME (2 :num),([] :num list)))
        (\(uv :unit). T) (\(uv :unit). (2 :num));
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
        (\((v12 :num),(x :num),(xs :num list)). x)]``
val _ = tcn (t, r_thm);



(******************************************************************************)
(* Simplification                                                             *)
(******************************************************************************)

val test =  test_conv "PMATCH_SIMP_CONV" PMATCH_SIMP_CONV

val t =
   ``PMATCH ((a :num option),(x :num),(xs :num list))
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
       (\((y :num),(z :num)). T) (\((y :num),(z :num)). y + z)]``;

val t' = ``PMATCH (a,x,xs)
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
        (\((y :num),(z :num)). T) (\((y :num),(z :num)). y + z)]``;

val _ = test (t, (SOME t'))


val t =
   ``PMATCH ((h :num)::(t :num list))
    [PMATCH_ROW (\(_ :'a). ([] :num list)) (\(_ :'a). T)
       (\(_ :'a). (x :num));
     PMATCH_ROW (\(_ :'b). [(2 :num)]) (\(_ :'b). T) (\(_ :'b). x);
     PMATCH_ROW (\(v18 :num). [v18]) (\(v19 :num). T)
       (\(v18 :num). (3 :num));
     PMATCH_ROW
       (\((v12 :num),(v16 :num),(v17 :num list)). v12::v16::v17)
       (K T :num # num # num list -> bool)
       (\((v12 :num),(v16 :num),(v17 :num list)). (3 :num));
     PMATCH_ROW (\(_ :'c). [(2 :num); (4 :num); (3 :num)]) (\(_ :'c). T)
       (\(_ :'c). (3 :num) + x)]``;

val t' = ``PMATCH (h,t)
     [PMATCH_ROW (\(_0 :unit). ((2 :num),([] :num list)))
        (\(_0 :unit). T) (\(_0 :unit). x);
      PMATCH_ROW (\(_0 :num). (_0,([] :num list))) (\(_0 :num). T)
        (\(_0 :num). (3 :num));
      PMATCH_ROW (\((_0 :num),(_1 :num),(_2 :num list)). (_0,_1::_2))
        (\((_0 :num),(_1 :num),(_2 :num list)). T)
        (\((_0 :num),(_1 :num),(_2 :num list)). (3 :num))]``

val _ = test (t, (SOME t'))


val t =
   ``PMATCH ((NONE :'a option),(x :num),(xs :num list))
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
       (\((y :'a option),(x :num)). (3 :num) + x)]``;

val t' = ``
   PMATCH xs
     [PMATCH_ROW (\(_0 :unit). ([] :num list)) (\(_0 :unit). T)
        (\(_0 :unit). x);
      PMATCH_ROW (\(_0 :unit). [(2 :num)]) (\(_0 :unit). T)
        (\(_0 :unit). x);
      PMATCH_ROW (\(_0 :num). [_0]) (\(_0 :num). T)
        (\(_0 :num). (3 :num));
      PMATCH_ROW (\((_0 :num),(_1 :num),(_2 :num list)). _0::_1::_2)
        (\((_0 :num),(_1 :num),(_2 :num list)). T)
        (\((_0 :num),(_1 :num),(_2 :num list)). (3 :num))]``;

val _ = test (t, (SOME t'))




(*************************************)
(* Removing DOUBLE-binds and guard   *)
(*************************************)

val t0 =
   ``PMATCH (l :num list)
    [PMATCH_ROW (\(uv :unit). ([] :num list)) (\(uv :unit). T)
       (\(uv :unit). (0 :num));
     PMATCH_ROW (\((x :num),(y :num),(_0 :num list)). x::y::x::y::_0)
       (\((x :num),(y :num),(_0 :num list)). T)
       (\((x :num),(y :num),(_0 :num list)). x + y);
     PMATCH_ROW (\((x :num),(y :num),(_1 :num list)). x::x::x::y::_1)
       (\((x :num),(y :num),(_1 :num list)). T)
       (\((x :num),(y :num),(_1 :num list)). x + x + x);
     PMATCH_ROW (\((x :num),(_2 :num list)). x::_2)
       (\((x :num),(_2 :num list)). T)
       (\((x :num),(_2 :num list)). (1 :num))]``;

val t1 = ``PMATCH l
     [PMATCH_ROW (\(uv :unit). ([] :num list)) (\(uv :unit). T)
        (\(uv :unit). (0 :num));
      PMATCH_ROW
        (\((x :num),(y :num),(_0 :num list),(y' :num),(x' :num)).
           x::y::x'::y'::_0)
        (\((x :num),(y :num),(_0 :num list),(y' :num),(x' :num)).
           (y' = y) /\ (x' = x) /\ T)
        (\((x :num),(y :num),(_0 :num list),(y' :num),(x' :num)).
           x + y);
      PMATCH_ROW
        (\((x :num),(y :num),(_1 :num list),(x'' :num),(x' :num)).
           x::x'::x''::y::_1)
        (\((x :num),(y :num),(_1 :num list),(x'' :num),(x' :num)).
           (x'' = x) /\ (x' = x) /\ T)
        (\((x :num),(y :num),(_1 :num list),(x'' :num),(x' :num)).
           x + x + x);
      PMATCH_ROW (\((x :num),(_2 :num list)). x::_2)
        (\((x :num),(_2 :num list)). T)
        (\((x :num),(_2 :num list)). (1 :num))]``;

val t2 = ``
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
        (\((_0 :num),(_2 :num list)). (1 :num))]``

val _ = test_conv "PMATCH_REMOVE_DOUBLE_BIND_CONV" PMATCH_REMOVE_DOUBLE_BIND_CONV (t0, SOME t1);
val _ = test_conv "PMATCH_REMOVE_GUARDS_CONV" PMATCH_REMOVE_GUARDS_CONV (t1, SOME t2);

val t = ``PMATCH ((y :num option),(x :num option),(l :num list))
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
       (\(x :num option). IS_SOME x) (\(x :num option). x)]``;

val t' = ``   PMATCH (y,l)
     [PMATCH_ROW (\(_0 :unit). (SOME (0 :num),([] :num list)))
        (\(_0 :unit). T) (\(_0 :unit). x);
      PMATCH_ROW (\(_0 :unit). (SOME (3 :num),[(2 :num)]))
        (\(_0 :unit). T)
        (\(_0 :unit). if IS_SOME x then x else SOME (3 :num));
      PMATCH_ROW (\(y :num option). (y,[(2 :num)]))
        (\(y :num option). T)
        (\(y :num option).
           if IS_SOME y then y else (PMATCH_INCOMPLETE :num option))]``;

val _ = test_conv "PMATCH_REMOVE_GUARDS_CONV" PMATCH_REMOVE_GUARDS_CONV (t, SOME t');



(*********************************)
(* Fancy redundancy removal      *)
(*********************************)

val t =
   ``PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(uv :unit). T) (\(uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\(_2 :'a option). (_2,(NONE :'b option)))
       (\(_2 :'a option). T) (\(_2 :'a option). (2 :num))]``;

val t' = ``
   PMATCH (x,z)
     [PMATCH_ROW (\(uv :unit). ((NONE :'a option),(NONE :'b option)))
        (\(uv :unit). T) (\(uv :unit). (0 :num));
      PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
        (\((_1 :'b option),(_0 :'a)). T)
        (\((_1 :'b option),(_0 :'a)). (1 :num))]``;

val _ = test_conv "PMATCH_REMOVE_REDUNDANT_CONV" PMATCH_REMOVE_REDUNDANT_CONV (t, SOME t');


(*********************************)
(* Exhaustiveness                *)
(*********************************)

val test_precond = test_conv_gen (fn t => let
  val (p, c) = dest_imp_only t
in
  (NONE, p)
end)

val t =
   ``PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(uv :unit). T) (\(uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\((_3 :'b),(_2 :'a option)). (_2,SOME _3))
       (\((_3 :'b),(_2 :'a option)). T)
       (\((_3 :'b),(_2 :'a option)). (2 :num))]``;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CONV" PMATCH_IS_EXHAUSTIVE_CONSEQ_CONV (t, SOME ``~F``)

val t = ``PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(uv :unit). T) (\(uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\(_2 :'a option). (_2,(NONE :'b option)))
       (\(_2 :'a option). T) (\(_2 :'a option). (2 :num))]``;

val p = ``~PMATCH_ROW_COND_EX ((x :'a option),(z :'b option))
      (\(v3 :'b). ((NONE :'a option),SOME v3)) (\(v3 :'b). T)``

val t' = ``PMATCH (x,z)
     [PMATCH_ROW (\(uv :unit). ((NONE :'a option),(NONE :'b option)))
        (\(uv :unit). T) (\(uv :unit). (0 :num));
      PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
        (\((_1 :'b option),(_0 :'a)). T)
        (\((_1 :'b option),(_0 :'a)). (1 :num));
      PMATCH_ROW (\(_2 :'a option). (_2,(NONE :'b option)))
        (\(_2 :'a option). T) (\(_2 :'a option). (2 :num));
      PMATCH_ROW (\(v3 :'b). ((NONE :'a option),SOME v3)) (\(v3 :'b). T)
        (\(v3 :'b). (ARB :num))]``;


val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CONV" PMATCH_IS_EXHAUSTIVE_CONSEQ_CONV (t, SOME p)
val _ = test_conv "PMATCH_COMPLETE_CONV true" (PMATCH_COMPLETE_CONV true) (t, SOME t')

(*********************************)
(* Exhaustiveness                *)
(*********************************)

fun mk_t t  = ``PMATCH (^t :num list)
    [PMATCH_ROW (\((y :num),(_0 :num)). [_0; y])
       (\((y :num),(_0 :num)). T) (\((y :num),(_0 :num)). y);
     PMATCH_ROW (\((x :num),(_2 :num),(_1 :num)). [x; _1; _2])
       (\((x :num),(_2 :num),(_1 :num)). T)
       (\((x :num),(_2 :num),(_1 :num)). x);
     PMATCH_ROW (\((x :num),(y :num),(_3 :num list)). x::y::_3)
       (\((x :num),(y :num),(_3 :num list)). T)
       (\((x :num),(y :num),(_3 :num list)). x + y);
     PMATCH_ROW (\(uv :unit). ([] :num list)) (\(uv :unit). T)
       (\(uv :unit). (0 :num));
     PMATCH_ROW (\(_4 :num list). _4) (\(_4 :num list). T)
       (\(_4 :num list). (1 :num))]``;

fun run_test (t, r) =
  test_conv "EVAL_CONV" EVAL_CONV (mk_t t, SOME r);

val _ = run_test (``[] : num list``, ``0``);
val _ = run_test (``[2;3] : num list``, ``3``);
val _ = run_test (``[2;30] : num list``, ``30``);
val _ = run_test (``[2;3;4] : num list``, ``2``);
val _ = run_test (``[4;3;4] : num list``, ``4``);
val _ = run_test (``[4;3;4;3] : num list``, ``7``);
val _ = run_test (``(4::3::l) : num list``, ``PMATCH ((4 :num)::(3 :num)::l)
     [PMATCH_ROW (\((y :num),(_0 :num)). [_0; y])
        (\((y :num),(_0 :num)). T) (\((y :num),(_0 :num)). y);
      PMATCH_ROW (\((x :num),(_2 :num),(_1 :num)). [x; _1; _2])
        (\((x :num),(_2 :num),(_1 :num)). T)
        (\((x :num),(_2 :num),(_1 :num)). x);
      PMATCH_ROW (\((x :num),(y :num),(_3 :num list)). x::y::_3)
        (\((x :num),(y :num),(_3 :num list)). T)
        (\((x :num),(y :num),(_3 :num list)). x + y)]``);


(* ----------------------------------------------------------------------
    Parser
   ---------------------------------------------------------------------- *)

open testutils
val _ = patternMatchesLib.ENABLE_PMATCH_CASES ()
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
   ``PMATCH (b:bool) [PMATCH_ROW (\u:one. T) (\u:one. T) (\u:one. F);
                      PMATCH_ROW (\u:one. F) (\u:one. T) (\u:one. T)]``),

  ("case x of 0 => 3 | SUC n => n + 1",
   ``PMATCH x [PMATCH_ROW (\u:one. 0) (\u:one. T) (\u:one. 3);
               PMATCH_ROW (\n. SUC n) (\n:num. T) (\n. n + 1)]``),

  ("case x of 0 => 3 | SUC _ => 4",
   ``PMATCH x [PMATCH_ROW (\u:one. 0) (\u:one. T) (\u:one. 3);
               PMATCH_ROW (\n:num. SUC n) (\n:num. T) (\n:num. 4)]``),

  ("case (x : bool list) of [] => F | (x,xs) .| x::xs => x",
   ``PMATCH x [PMATCH_ROW (\u:one. []:bool list) (\u:one. T) (\u:one. F);
               PMATCH_ROW (\ (x:bool,xs:bool list). x::xs)
                          (\ (x:bool,xs:bool list). T)
                          (\ (x:bool,xs:bool list). x)]``),

  ("(n:num) + case m of 0 => 3 | () .| SUC n => 10 | z => z",
   ``(n:num) +
     PMATCH m [PMATCH_ROW (\u:one. 0n) (\u:one. T) (\u:one. 3n);
               PMATCH_ROW (\u:one. SUC n) (\u:one. T) (\u:one. 10);
               PMATCH_ROW (\z:num. z) (\z:num. T) (\z:num. z)]``),

  ("case x of 0 => 3 | () .| n => 4 | _ => 100",
   ``PMATCH (x:num) [PMATCH_ROW (\u:one. 0n) (\u:one. T) (\u:one. 3n);
                     PMATCH_ROW (\u:one. n:num) (\u:one. T) (\u:one. 4n);
                     PMATCH_ROW (\x:num. x) (\x:num. T) (\x:num. 100n)]``),

  ("n + case b of T => 1 | n => 2",
   ``n + PMATCH (b:bool)
                [PMATCH_ROW (\u:one. T) (\u:one. T) (\u:one. 1n);
                 PMATCH_ROW (\n:bool. n) (\n:bool. T) (\n:bool. 2n)]``),

  ("n + case x of 0 => 1 | m .| m + n => m * 2",
   ``n + PMATCH (x:num)
                [PMATCH_ROW (\u:one. 0) (\u:one. T) (\u:one. 1);
                 PMATCH_ROW (\m:num. m + n) (\m:num. T) (\m:num. m * 2)]``),

  ("case x of 0 => 3 | () .| n => 4 | x => 100",
   ``PMATCH (x:num) [PMATCH_ROW (\u:one. 0n) (\u:one. T) (\u:one. 3n);
                     PMATCH_ROW (\u:one. n:num) (\u:one. T) (\u:one. 4n);
                     PMATCH_ROW (\x:num. x) (\x:num. T) (\x:num. 100n)]``),

  ("case (y,x) of\
   \ | (NONE,[]) => 0\
   \ | (NONE,[T]) => 1\
   \ | (SOME T,[]) => 2\
   \ | (SOME _, _) => 3\
   \ | z .| (SOME _, z) => 4\
   \ | (z1, z2:'a) .| (SOME _, z1) => 5\
   \ | z .| (SOME T, z) when LENGTH x > 5 => 6\
   \ | (z1, z2, z3:'b list) .| (SOME z1, z2) when LENGTH z3 > 5 => 7",
   ``PMATCH ((y :bool option),(x :bool list))
      [PMATCH_ROW (\uv :unit. (NONE :bool option,[] :bool list))
                  (\uv :unit. T)
                  (\uv :unit. 0n);
       PMATCH_ROW (\uv :unit. (NONE :bool option,[T]))
                  (\uv:unit. T)
                  (\uv:unit. 1n);
       PMATCH_ROW (\uv:unit. (SOME T, [] :bool list)) (\uv:unit. T)
                  (\uv :unit. 2n);
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
         (\ ((z1 :bool),(z2 :bool list),(z3 :'b list)). 7n)]``),

  ("case x of NONE => y | SOME (z:'foo) => (f z : 'bar)",
   ``PMATCH (x:'foo option) [
       PMATCH_ROW (\uv:unit. NONE) (\uv:unit. T) (\uv:unit. y:'bar);
       PMATCH_ROW (\z:'foo. SOME z) (\z:'foo. T) (\z:'foo. f z : 'bar)
     ]``),

  ("case x of NONE => y | z:'foo .| SOME z => (f z : 'bar)",
   ``PMATCH (x:'foo option) [
       PMATCH_ROW (\uv:unit. NONE) (\uv:unit. T) (\uv:unit. y:'bar);
       PMATCH_ROW (\z:'foo. SOME z) (\z:'foo. T) (\z:'foo. f z : 'bar)
     ]``),

  ("dtcase x of NONE => 3 | SOME y => y + 1",
   ``option_CASE (x : num option) 3n (\z:num. z + 1)``)

]

fun shouldfail s = let
  val _ = tprint ("Should NOT parse: " ^ s)
in
  case Lib.total (trace ("show_typecheck_errors", 0) Parse.Term) [QUOTE s] of
      NONE => OK()
    | SOME t => die ("FAILED!\n  Parsed to: " ^ term_to_string t)
end


val _ = app shouldfail [
      "case x of NONE => F | y .| SOME(x,y) => x < y"
]

(* ----------------------------------------------------------------------
    Pretty-printer
   ---------------------------------------------------------------------- *)

val _ = app (raw_backend tpp) [
  "case x of 0 => 3 | SUC n => n",
  "case x of 0 => 4 | SUC _ => 10",
  "case (x,y) of (NONE,_) => 10 | (SOME n,0) when n < 10 => 11",
  "case x of 0 => 3 | () .| n => 4 | x => 100",
  "case x of NONE => 3 | () .| SOME n => n | SOME x => x + 1"
]
