open HolKernel Parse boolTheory boolLib pairTheory
open constrFamiliesLib patternMatchesLib computeLib
open quantHeuristicsLib simpLib boolSimps
open testutils

val hard_fail = true;
val _ = really_die := true;
val quiet = false;
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

(* For manual

set_trace "use pmatch_pp" 0
val hard_fail = false;
val _ = really_die := false;
val quiet = false;
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;

*)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES ()

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

val t = ``dtcase x of (NONE, []) => 0``;
val r_thm = SOME ``PMATCH (x :'a option # 'b list)
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),([] :'b list)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num))]``
val _ = tc (t, r_thm);

val t = ``dtcase x of
   (NONE, []) => 0
 | (SOME 2, []) => 2
 | (SOME 3, (x :: xs)) => 3 + x
 | (SOME _, (x :: xs)) => x``
val r_thm = SOME ``PMATCH x
     [PMATCH_ROW (\(_uv :unit). ((NONE :num option),([] :num list)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
      PMATCH_ROW (\(_uv :unit). (SOME (2 :num),([] :num list)))
        (\(_uv :unit). T) (\(_uv :unit). (2 :num));
      PMATCH_ROW (\((x :num),(_0 :num list)). (SOME (3 :num),x::_0))
        (\((x :num),(_0 :num list)). T)
        (\((x :num),(_0 :num list)). (3 :num) + x);
      PMATCH_ROW (\((_0 :num),(x :num),(_1 :num list)). (SOME _0,x::_1))
        (\((_0 :num),(x :num),(_1 :num list)). T)
        (\((_0 :num),(x :num),(_1 :num list)). x)]``
val _ = tc (t, r_thm);




val tcn = test_conv "PMATCH_INTRO_CONV_NO_OPTIMISE" PMATCH_INTRO_CONV_NO_OPTIMISE

val t = ``dtcase x of (NONE, []) => 0``
val r_thm = SOME ``PMATCH x
     [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),([] :'b list)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
      PMATCH_ROW (\((v4 :'b),(v5 :'b list)). ((NONE :'a option),v4::v5))
        (\((v4 :'b),(v5 :'b list)). T)
        (\((v4 :'b),(v5 :'b list)). (ARB :num));
      PMATCH_ROW (\((v2 :'a),(v1 :'b list)). (SOME v2,v1))
        (\((v2 :'a),(v1 :'b list)). T)
        (\((v2 :'a),(v1 :'b list)). (ARB :num))]``
val _ = tcn (t, r_thm);

val t = ``dtcase x of
   (NONE, []) => 0
 | (SOME 2, []) => 2
 | (SOME 3, (x :: xs)) => 3 + x
 | (SOME _, (x :: xs)) => x``
val r_thm = SOME ``
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
        (\((v12 :num),(x :num),(xs :num list)). x)]``
val _ = tcn (t, r_thm);



(******************************************************************************)
(* Simplification                                                             *)
(******************************************************************************)

val test =  test_conv "PMATCH_CLEANUP_PVARS_CONV" PMATCH_CLEANUP_PVARS_CONV (``PMATCH (x:('b # 'c) option) [
     PMATCH_ROW (\x:'a. NONE) (\x. T) (\x. 5);
     PMATCH_ROW (\ (x,y). SOME (x,z)) (\ (x,y). T) (\ (x,y). 8);
     PMATCH_ROW (\ (x,z). SOME (x,z)) (\_. T) (\ (a,y). 8)]``,
SOME ``PMATCH (x:('b # 'c) option)
     [PMATCH_ROW (\_uv:unit. NONE) (\_uv. T) (\_uv. 5);
      PMATCH_ROW (\x. SOME (x,z)) (\x. T) (\x. 8);
      PMATCH_ROW (\(x,z). SOME (x,z)) (\(x,z). T) (\(x,z). 8)]``)

val test = test_conv "PMATCH_EXPAND_COLS_CONV" PMATCH_EXPAND_COLS_CONV (``PMATCH (x,y,z)
    [PMATCH_ROW (\y. (0,y,T)) (\y. T) (\y. y);
     PMATCH_ROW (\xyz. xyz) (\xyz. ~SND (SND xyz)) (\xyz. 2);
     PMATCH_ROW (\(x,yz). (x,yz)) (\(x,yz). T) (\(x,yz). x)]``,
SOME ``PMATCH (x,y,z)
     [PMATCH_ROW (\y. (0,y,T)) (\y. T) (\y. y);
      PMATCH_ROW (\(xyz_0,xyz_1,xyz_2). (xyz_0,xyz_1,xyz_2))
        (\(xyz_0,xyz_1,xyz_2). ~SND (SND (xyz_0,xyz_1,xyz_2)))
        (\(xyz_0,xyz_1,xyz_2). 2);
      PMATCH_ROW (\(x,yz_0,yz_1). (x,yz_0,yz_1)) (\(x,yz_0,yz_1). T)
        (\(x,yz_0,yz_1). x)]``)


val test = test_conv "PMATCH_INTRO_WILDCARDS_CONV" PMATCH_INTRO_WILDCARDS_CONV (``PMATCH (x,y,z)
    [PMATCH_ROW (\(x,y,z). (x,y,z)) (\(x,y,z). T) (\(x,y,z). x + y);
     PMATCH_ROW (\(x,y,z). (x,y,z)) (\(x,y,z). z) (\(x,y,z). x)]``, SOME ``PMATCH (x,y,z)
     [PMATCH_ROW (\(x,y,_0). (x,y,_0)) (\(x,y,_0). T)
        (\(x,y,_0). x + y);
      PMATCH_ROW (\(x,_0,z). (x,_0,z)) (\(x,_0,z). z) (\(x,_0,z). x)]``)


val test = test_conv "PMATCH_CLEANUP_CONV" PMATCH_CLEANUP_CONV (``case (SUC x) of
     x => x + 5``, SOME ``SUC x + 5``)

val test = test_conv "PMATCH_CLEANUP_CONV" PMATCH_CLEANUP_CONV (``case (SOME (x:'a),y) of
     (NONE, y) => 0
   | (x, 0) => 1
   | (SOME x, y) => 2
   | (x, y) => 3``, SOME `` PMATCH (SOME (x:'a),y)
     [PMATCH_ROW (\x. (x,0)) (\x. T) (\x. 1);
      PMATCH_ROW (\(x,y). (SOME x,y)) (\(x,y). T) (\(x,y). 2)]``)

val test = test_conv "PMATCH_CLEANUP_CONV" PMATCH_CLEANUP_CONV (``case (SOME (x:'a),y) of
     (NONE, y) => 0
   | (SOME x, y) => 2
   | (x, y) => 3``, SOME ``2``)

val test = test_conv "PMATCH_SIMP_COLS_CONV" PMATCH_SIMP_COLS_CONV (``case (SOME x,y) of
   | (SOME x, 1) => x+y
   | (x, y) => 3``, SOME ``PMATCH y
     [PMATCH_ROW (\(_uv:unit). 1) (\_uv. T) (\_uv. x + y);
      PMATCH_ROW (\y. y) (\y. T) (\y. 3)]``)

val test = test_conv "PMATCH_SIMP_COLS_CONV" PMATCH_SIMP_COLS_CONV (``case (SOME x,y) of
   | (SOME x, 1) => x+y
   | (SOME 2, 2) => y
   | (x, y) => 3``, SOME ``PMATCH (x,y)
     [PMATCH_ROW (\x. (x,1)) (\x. T) (\x. x + y);
      PMATCH_ROW (\(_uv:unit). (2,2)) (\_uv. T) (\_uv. y);
      PMATCH_ROW (\(x_0,y). (x_0,y)) (\(x_0,y). T) (\(x_0,y). 3)]``)


val test =  test_conv "PMATCH_REMOVE_FAST_REDUNDANT_CONV" PMATCH_REMOVE_FAST_REDUNDANT_CONV (``case xy of
   | (SOME x, y) => 1
   | (SOME 2, 3) => 2
   | (NONE, y) => 3
   | (NONE, y) => 4
   | (x, 5) => 5``, SOME ``
  case xy of
   | (SOME (x:num), y) => 1
   | (NONE, y) => 3
   | (x, 5) => 5``)

val test =  test_conv "PMATCH_REMOVE_REDUNDANT_CONV" PMATCH_REMOVE_REDUNDANT_CONV (``case xy of
   | (SOME x, y) => 1
   | (SOME 2, 3) => 2
   | (NONE, y) => 3
   | (NONE, y) => 4
   | (x, 5) => 5``, SOME ``
  case xy of
   | (SOME (x:num), (y:num)) => 1
   | (NONE, y) => 3``)


val test =  test_conv "PMATCH_REMOVE_FAST_SUBSUMED_CONV true" (PMATCH_REMOVE_FAST_SUBSUMED_CONV true) (``case xy of
   | (SOME 2, _) => 2
   | (NONE, 3) => 1
   | (SOME x, _) => x
   | (NONE, y) => y
   | (x, 5) => ARB``, SOME
``case xy of
   | (NONE, 3) => 1
   | (SOME x, _) => x
   | (NONE, y) => y``)

val test =  test_conv "PMATCH_REMOVE_FAST_SUBSUMED_CONV false" (PMATCH_REMOVE_FAST_SUBSUMED_CONV false) (``case xy of
   | (SOME 2, _) => 2
   | (NONE, 3) => 1
   | (SOME x, _) => x
   | (NONE, y) => y
   | (x, 5) => ARB``, SOME
``case xy of
   | (NONE, 3) => 1
   | (SOME x, _) => x
   | (NONE, y) => y
   | (x, 5) => ARB``)

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


val t = ``PMATCH (x,y,z)
     [PMATCH_ROW (λ(y,z). (1,y,z)) (λ(y,z). T) (λ(y,z). y + z);
      PMATCH_ROW (λx. (x,2,4)) (λx. T) (λx. x + 4);
      PMATCH_ROW (λ(x,z). (x,2,z)) (λ(x,z). T) (λ(x,z). x + z);
      PMATCH_ROW (λ(x,y). (x,y,3)) (λ(x,y). T) (λ(x,y). x + y)]``;

val t' = ``
   PMATCH (x,y,z)
     [PMATCH_ROW (λ(y,z). (1,y,z)) (λ(y,z). T) (λ(y,z). y + z);
      PMATCH_ROW (λ(x,z). (x,2,z)) (λ(x,z). T) (λ(x,z). x + z);
      PMATCH_ROW (λ(x,y). (x,y,3)) (λ(x,y). T) (λ(x,y). x + y)]``;

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
       (\((x :num),(_2 :num list)). (1 :num))]``;

val t1 = ``PMATCH l
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

val _ = test_conv "PMATCH_REMOVE_DOUBLE_BIND_CONV" PMATCH_REMOVE_DOUBLE_BIND_CONV (``case xy of
   | (x, x) when x > 0 => x + x
   | x.| (x, y) => x
   | (x, _) => SUC x``, SOME ``
case xy of
     (x,x') when (x' = x) /\ x > 0 => x + x
   | (x,y') when (y' = y) => x
   | (x,_) => SUC x``)


val _ = test_conv "PMATCH_REMOVE_DOUBLE_BIND_CONV" PMATCH_REMOVE_DOUBLE_BIND_CONV (``case (xx:('a # 'a)) of (x, x) => T | _ => F``, SOME ``case (xx:('a # 'a)) of (x, x') when (x' = x) => T | _ => F``) ;

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


val _ = test_conv "PMATCH_REMOVE_GUARDS_CONV" PMATCH_REMOVE_GUARDS_CONV (``case (x, y) of
  | (x, 2) when EVEN x => x + x
  | (SUC x, y) when ODD x => y + x + SUC x
  | (SUC x, 1) => x
  | (x, _) => x+3``, SOME ``case (x,y) of
     (x,2) =>
          if EVEN x then x + x
          else (case x of SUC x when ODD x => 2 + x + SUC x | x => x + 3)
   | (SUC x,y) =>
          if ODD x then y + x + SUC x
          else (case y of 1 => x | _ => SUC x + 3)
   | (x,_) => x + 3``);



val _ = test_conv "PMATCH_REMOVE_GUARDS_CONV" PMATCH_REMOVE_GUARDS_CONV (``case (x, y) of
  | (x, 0) when EVEN x => (SOME x, T)
  | (x, 0) => (SOME x, F)
  | (0, _) => (NONE, T)
  | (_, _) => (NONE, F)``, SOME ``case (x,y) of
     (x,0) => if EVEN x then (SOME x,T) else (SOME x,F)
   | (0,_) => (NONE,T)
   | (_,_) => (NONE,F)``);


val _ = test_conv "SIMP_CONV (numLib.std_ss ++ PMATCH_REMOVE_GUARDS_ss) []" (SIMP_CONV (numLib.std_ss ++ PMATCH_REMOVE_GUARDS_ss) []) (
  ``case x of
  | _ when x < 5 => 0
  | _ when x < 10 => 1
  | _ when x < 15 => 2
  | _ => 3``, SOME ``if x < 5 then 0 else if x < 10 then 1 else if x < 15 then 2 else 3``);

(*********************************)
(* Fancy redundancy removal      *)
(*********************************)

val t =
   ``PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\(_2 :'a option). (_2,(NONE :'b option)))
       (\(_2 :'a option). T) (\(_2 :'a option). (2 :num))]``;

val t' = ``
   PMATCH (x,z)
     [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
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
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\((_3 :'b),(_2 :'a option)). (_2,SOME _3))
       (\((_3 :'b),(_2 :'a option)). T)
       (\((_3 :'b),(_2 :'a option)). (2 :num))]``;

val _ = test_precond "PMATCH_IS_EXHAUSTIVE_CONSEQ_CONV" PMATCH_IS_EXHAUSTIVE_CONSEQ_CONV (t, SOME ``~F``)

val t = ``PMATCH ((x :'a option),(z :'b option))
    [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
       (\(_uv :unit). T) (\(_uv :unit). (0 :num));
     PMATCH_ROW (\((_1 :'b option),(_0 :'a)). (SOME _0,_1))
       (\((_1 :'b option),(_0 :'a)). T)
       (\((_1 :'b option),(_0 :'a)). (1 :num));
     PMATCH_ROW (\(_2 :'a option). (_2,(NONE :'b option)))
       (\(_2 :'a option). T) (\(_2 :'a option). (2 :num))]``;

val p = ``~PMATCH_ROW_COND_EX ((x :'a option),(z :'b option))
      (\(v3 :'b). ((NONE :'a option),SOME v3)) (\(v3 :'b). T)``

val t' = ``PMATCH (x,z)
     [PMATCH_ROW (\(_uv :unit). ((NONE :'a option),(NONE :'b option)))
        (\(_uv :unit). T) (\(_uv :unit). (0 :num));
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
     PMATCH_ROW (\(_uv :unit). ([] :num list)) (\(_uv :unit). T)
       (\(_uv :unit). (0 :num));
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
         (\ ((z1 :bool),(z2 :bool list),(z3 :'b list)). 7n)]``),

  ("case x of NONE => y | SOME (z:'foo) => (f z : 'bar)",
   ``PMATCH (x:'foo option) [
       PMATCH_ROW (\_uv:unit. NONE) (\_uv:unit. T) (\_uv:unit. y:'bar);
       PMATCH_ROW (\z:'foo. SOME z) (\z:'foo. T) (\z:'foo. f z : 'bar)
     ]``),

  ("case x of NONE => y | z:'foo .| SOME z => (f z : 'bar)",
   ``PMATCH (x:'foo option) [
       PMATCH_ROW (\_uv:unit. NONE) (\_uv:unit. T) (\_uv:unit. y:'bar);
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
