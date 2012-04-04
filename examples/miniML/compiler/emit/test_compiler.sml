open HolKernel stringLib ml_translatorLib bytecodeML compileML

fun bc_evaln 0 s = s
  | bc_evaln n s = let
    val SOME s = bc_eval1 s in
      bc_evaln (n-1) s
    end handle Bind => (print "Fail\n"; s)

fun bc_eval_limit l s = let
     val SOME s = bc_eval1 s
     val n = length (bc_state_stack s)
  in if n > l then NONE else bc_eval_limit l s
   end handle Bind => SOME s

fun dest_list f = map f o (fst o listSyntax.dest_list)
fun dest_pair f1 f2 = (f1 ## f2) o pairSyntax.dest_pair
fun term_to_int tm = intML.fromString((Parse.term_to_string tm)^"i")
fun term_to_bool tm = tm = boolSyntax.T
fun term_to_lit tm = let
  val (f,x) = dest_comb tm
in case fst(dest_const f) of
    "IntLit" => IntLit (term_to_int x)
  | "Bool" => Bool (term_to_bool x)
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_opb tm =
  case fst(dest_const tm) of
    "Geq" => Geq
  | "Gt" => Gt
  | "Lt" => Lt
  | "Leq" => Leq
  | s => raise Fail s
fun term_to_opn tm =
  case fst(dest_const tm) of
    "Minus" => Minus
  | "Plus" => Plus
  | "Times" => Times
  | s => raise Fail s
fun term_to_op_ tm = let
  val (f,x) = dest_comb tm
in case fst(dest_const f) of
    "Opn" => Opn (term_to_opn x)
  | "Opb" => Opb (term_to_opb x)
  | s => raise Fail s
end handle _ => (
case fst(dest_const tm) of
    "Opapp" => Opapp
  | "Equality" => Equality
  | s => raise Fail s )
handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_pat tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Pvar" => let val [x1] = xs in Pvar (fromHOLstring x1) end
  | "Plit" => let val [x1] = xs in Plit (term_to_lit x1) end
  | "Pcon" => let val [x1,x2] = xs in Pcon (fromHOLstring x1, dest_list term_to_pat x2) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_v tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Lit" => let val [x1] = xs in Lit (term_to_lit x1) end
  | "Closure" => let val [x1,x2,x3] = xs in Closure (dest_list (dest_pair fromHOLstring term_to_v) x1,fromHOLstring x2,term_to_exp x3) end
  | "Conv" => let val [x1,x2] = xs in Conv (fromHOLstring x1,dest_list term_to_v x2) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
and term_to_exp tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Val" => let val [x1] = xs in Val (term_to_v x1) end
  | "If"  => let val [x1,x2,x3] = xs in If (term_to_exp x1, term_to_exp x2, term_to_exp x3) end
  | "App" => let val [x1,x2,x3] = xs in App (term_to_op_ x1, term_to_exp x2, term_to_exp x3) end
  | "Fun" => let val [x1,x2] = xs in Fun (fromHOLstring x1, term_to_exp x2) end
  | "Var" => let val [x1] = xs in Var (fromHOLstring x1) end
  | "Let" => let val [x1,x2,x3] = xs in Let (fromHOLstring x1,term_to_exp x2,term_to_exp x3) end
  | "Mat" => let val [x1,x2] = xs in Mat (term_to_exp x1,dest_list (dest_pair term_to_pat term_to_exp) x2) end
  | "Con" => let val [x1,x2] = xs in Con (fromHOLstring x1,dest_list term_to_exp x2) end
  | "Letrec" => let val [x1,x2] = xs in Letrec (dest_list (dest_pair fromHOLstring (dest_pair fromHOLstring term_to_exp)) x1,term_to_exp x2) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_t tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Tnum" => Tnum
  | "Tvar" => let val [x1] = xs in Tvar (fromHOLstring x1) end
  | "Tapp" => let val [x1,x2] = xs in Tapp (dest_list term_to_t x1, fromHOLstring x2) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_dec tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Dlet" => let val [x1,x2] = xs in Dlet (term_to_pat x1, term_to_exp x2) end
  | "Dtype" => let val [x1] = xs in Dtype (dest_list (dest_pair (dest_list fromHOLstring) (dest_pair fromHOLstring (dest_list (dest_pair fromHOLstring (dest_list term_to_t))))) x1) end
  | "Dletrec" => let val [x1] = xs in Dletrec (dest_list (dest_pair fromHOLstring (dest_pair fromHOLstring term_to_exp)) x1) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)

fun f1 s e =
let val rs = repl_exp s (term_to_exp e) in
  (rev (compiler_state_code (repl_state_cs rs)),
   repl_state_cpam rs)
end
fun f2 s e = fst(f1 s e)
fun f e = f2 init_repl_state e
fun fd0 f e = let
  fun q s [] = f s e
    | q s (d::ds) = let
      val s = repl_dec s (term_to_dec d)
      in q s ds end
in q init_repl_state end
val fd = fd0 f2
fun g1 c = bc_eval (init_state c)
fun g c = bc_state_stack (g1 c)
val pd0 = fd0 f1
fun pd1 e ds = let
  val (c,m) = pd0 e ds
  val st = g c
  in (m,st) end
fun pv m bv ty = bcv_to_v m ty bv
fun pd tys e ds =
  let val (m,st) = pd1 e ds
  in map2 (pv m) st tys end

val e1 = ``Val (Lit (IntLit 42))``
val c1 = f e1
val [Number i] = g c1
val SOME 42 = intML.toInt i;
val true = [term_to_v ``Lit (IntLit 42)``] = (pd [NTnum] e1 [])
val e2 = ``If (Val (Lit (Bool T))) (Val (Lit (IntLit 1))) (Val (Lit (IntLit 2)))``
val c2 = f e2
val [Number i] = g c2
val SOME 1 = intML.toInt i;
val e3 = ``If (Val (Lit (Bool F))) (Val (Lit (IntLit 1))) (Val (Lit (IntLit 2)))``
val c3 = f e3
val [Number i] = g c3
val SOME 2 = intML.toInt i;
val e4 = ``App Equality (Val (Lit (IntLit 1))) (Val (Lit (IntLit 2)))``
val c4 = f e4
val [Number i] = g c4
val SOME 0 = intML.toInt i;
val e5 = ``Fun "x" (Var "x")``
val c5 = f e5
val st = g c5
val true = [term_to_v ``Closure [] "" (Var "")``] = pd [NTfn] e5 []
val e6 = ``Let "x" (Val (Lit (IntLit 1))) (App (Opn Plus) (Var "x") (Var "x"))``
val c6 = f e6
val [Number i] = g c6
val SOME 2 = intML.toInt i;
val e7 = ``Let "x" (Val (Lit (IntLit 1)))
             (Let "y" (Val (Lit (IntLit 2)))
                (Let "x" (Val (Lit (IntLit 3)))
                   (App (Opn Plus) (Var "x") (Var "y"))))``
val c7 = f e7
val [Number i] = g c7
val SOME 5 = intML.toInt i;
val e8 = ``
Let "0?" (Fun "x" (App Equality (Var "x") (Val (Lit (IntLit 0)))))
  (Let "x" (Val (Lit (IntLit 1)))
    (Let "x" (App (Opn Minus) (Var "x") (Var "x"))
      (App Opapp (Var "0?") (Var "x"))))``
val c8 = f e8
val [Number i] = g c8
val SOME 1 = intML.toInt i;
val e9 = ``
Let "1?" (Fun "x" (App Equality (Var "x") (Val (Lit (IntLit 1)))))
  (Let "x" (Val (Lit (IntLit 1)))
    (Let "x" (App (Opn Minus) (Var "x") (Var "x"))
      (App Opapp (Var "1?") (Var "x"))))``
val c9 = f e9
val [Number i] = g c9
val SOME 0 = intML.toInt i;
val e10 = ``
Let "x" (Val (Lit (IntLit 3)))
(If (App (Opb Gt) (Var "x") (App (Opn Plus) (Var "x") (Var "x")))
  (Var "x") (Val (Lit (IntLit 4))))``
val c10 = f e10
val [Number i] = g c10
val SOME 4 = intML.toInt i;
val e11 = ``
Let "x" (Val (Lit (IntLit 3)))
(If (App (Opb Geq) (Var "x") (Var "x"))
  (Var "x") (Val (Lit (IntLit 4))))``
val c11 = f e11
val [Number i] = g c11
val SOME 3 = intML.toInt i;
val e12 = ``
Let "lt2" (Fun "x" (App (Opb Lt) (Var "x") (Val (Lit (IntLit 2)))))
  (App Opapp (Var "lt2") (Val (Lit (IntLit 3))))``
val c12 = f e12
val [Number i] = g c12
val SOME 0 = intML.toInt i;
val e13 = ``
Let "lq2" (Fun "x" (App (Opb Leq) (Var "x") (Val (Lit (IntLit 2)))))
  (App Opapp (Var "lq2") (Val (Lit (IntLit 0))))``
val c13 = f e13
val [Number i] = g c13
val SOME 1 = intML.toInt i;
val e14 = ``
Let "x" (Val (Lit (IntLit 0)))
  (Let "y" (App (Opn Plus) (Var "x") (Val (Lit (IntLit 2))))
    (If (App (Opb Geq) (Var "y") (Var "x"))
      (Var "x") (Val (Lit (IntLit 4)))))``
val c14 = f e14
val [Number i] = g c14
val SOME 0 = intML.toInt i;
val e15 = ``
Let "x" (Val (Lit (Bool T)))
(App Equality
  (Mat (Var "x")
    [(Plit (Bool F), (Val (Lit (IntLit 1))));
     (Pvar "y", (Var "y"))])
  (Var "x"))``
val c15 = f e15
val [Number i] = g c15
val SOME 1 = intML.toInt i;
val e16 = ``App Equality (Let "x" (Val (Lit (Bool T))) (Var "x")) (Val (Lit (Bool F)))``
val c16 = f e16
val [Number i] = g c16
val SOME 0 = intML.toInt i;
val e17 = ``App Equality
  (Let "f" (Fun "_" (Val (Lit (Bool T)))) (App Opapp (Var "f") (Val (Lit (Bool T)))))
  (Val (Lit (Bool F)))``
val c17 = f e17
val [Number i] = g c17
val SOME 0 = intML.toInt i;
val e18 = ``
Let "x" (Val (Lit (Bool T)))
  (App Equality
    (Let "f" (Fun "_" (Var "x")) (App Opapp (Var "f") (Var "x")))
    (Var "x"))``
val c18 = f e18
val [Number i] = g c18
val SOME 1 = intML.toInt i;
val e19 = ``
Let "x" (Val (Lit (Bool T)))
  (App Opapp (Fun "_" (Var "x")) (Val (Lit (Bool F))))``
val c19 = f e19
val [Number i] = g c19
val SOME 1 = intML.toInt i;
val e20 = ``
Let "f" (Fun "_" (Val (Lit (Bool T))))
(App Equality
  (App Opapp (Var "f") (Val (Lit (Bool T))))
  (Val (Lit (Bool F))))``
val c20 = f e20
val [Number i] = g c20
val SOME 0 = intML.toInt i;
val e21 = ``Let "x" (Val (Lit (Bool T)))
(App Equality
  (Let "f" (Fun "_" (Var "x"))
    (App Opapp (Var "f") (Var "x")))
  (Var "x"))``
val c21 = f e21
val [Number i] = g c21
val SOME 1 = intML.toInt i;
val listd = ``
Dtype
  [(["'a"],"list",
    [("Cons",[Tvar "'a"; Tapp [Tvar "'a"] "list"]); ("Nil",[])])]
``
val e22 = ``Con "Cons" [Val (Lit (Bool T)); Con "Nil" []]``
val c22 = fd e22 [listd]
val [Block (t1,[Number i,Number t2])] = g c22
val SOME 0 = numML.toInt t1
val SOME 1 = intML.toInt i
val SOME 1 = intML.toInt t2;
val e23 = ``Mat (Con "Cons" [Val (Lit (IntLit 2));
                 Con "Cons" [Val (Lit (IntLit 3));
                 Con "Nil" []]])
            [(Pcon "Cons" [Pvar "x"; Pvar "xs"],
              Var "x");
             (Pcon "Nil" [],
              Val (Lit (IntLit 1)))]``
val c23 = fd e23 [listd]
val [Number i] = g c23
val SOME 2 = intML.toInt i;
val e24 = ``Mat (Con "Nil" [])
            [(Pcon "Nil" [], Val (Lit (Bool F)))]``
val c24 = fd e24 [listd]
val [Number i] = g c24
val SOME 0 = intML.toInt i;
val e25 = ``Mat (Con "Cons" [Val (Lit (IntLit 2));
                 Con "Nil" []])
            [(Pcon "Cons" [Pvar "x"; Pvar "xs"],
              Var "x")]``
val c25 = fd e25 [listd]
val [Number i] = g c25
val SOME 2 = intML.toInt i;
val e26 = ``Mat (Con "Cons" [Val (Lit (IntLit 2));
                 Con "Nil" []])
            [(Pcon "Cons" [Plit (IntLit 2);
              Pcon "Nil" []],
              Val (Lit (IntLit 5)))]``
val c26 = fd e26 [listd]
val [Number i] = g c26
val SOME 5 = intML.toInt i;
(*val e27 = ``
CLetfun F [1] [([],CRaise Bind_error)]
(CLprim CIf [CPrim2 CEq (CLit (IntLit 0)) (CLit (IntLit 0)); CLit (IntLit 1); CCall (CVar 1) []])``
val c27 = term_to_bc_list(rhs(concl(computeLib.CBV_CONV compset ``REVERSE (compile ^s ^e27).code``)))
val [Number i] = g c27
val SOME 1 = intML.toInt i;*)
val e28 = ``
Letrec [("fac",("n",
  If (App Equality (Var "n") (Val (Lit (IntLit 0))))
     (Val (Lit (IntLit 1)))
     (App (Opn Times)
       (Var "n")
       (App Opapp (Var "fac") (App (Opn Minus)
                                   (Var "n")
                                   (Val (Lit (IntLit 1))))))))]
  (App Opapp (Var "fac") (Val (Lit (IntLit 5))))``
val c28 = f e28
val [Number i] = g c28
val SOME 120 = intML.toInt i;
val d = ``Dlet (Pvar "Foo") (Val (Lit (IntLit 42)))``
val e41 = ``Var "Foo"``
val c41 = fd e41 [d]
val [Number i,Number j] = g c41
val SOME 42 = intML.toInt i;
val true = i = j;
val d = ``Dletrec [("I","x",(Var "x"))]``
val e42 = ``App Opapp (Var "I") (Val (Lit (IntLit 42)))``
val c42 = fd e42 [d]
val [Number i,cl] = g c42
val SOME 42 = intML.toInt i;
val d0 = ``
Dletrec
  [("N","v1",
    If (App (Opb Gt) (Var "v1") (Val (Lit (IntLit 100))))
      (App (Opn Minus) (Var "v1") (Val (Lit (IntLit 10))))
      (App Opapp (Var "N")
         (App Opapp (Var "N")
            (App (Opn Plus) (Var "v1") (Val (Lit (IntLit 11)))))))]
``
val e29 = ``App Opapp (Var "N") (Val (Lit (IntLit 42)))``
val c29 = fd e29 [d0]
val [Number i,cl] = g c29
val SOME 91 = intML.toInt i;
val e35 = ``Let "f" (Fun "x" (Fun "y" (App (Opn Plus) (Var "x") (Var "y")))) (App Opapp (App Opapp (Var "f") (Val (Lit (IntLit 2)))) (Val (Lit (IntLit 3))))``
val c35 = f e35
val [Number i] = g c35
val SOME 5 = intML.toInt i;
val e36 = ``Letrec [("f", ("x", (Fun "y" (App (Opn Plus) (Var "x") (Var "y")))))] (App Opapp (App Opapp (Var "f") (Val (Lit (IntLit 2)))) (Val (Lit (IntLit 3))))``
val c36 = f e36
val [Number i] = g c36
val SOME 5 = intML.toInt i;
val e37 = ``Letrec [("z", ("x", (Mat (Var "x") [(Plit (IntLit 0), (Var "x"));(Pvar "y", App Opapp (Var "z") (App (Opn Minus) (Var "x") (Var "y")))])))] (App Opapp (Var "z") (Val (Lit (IntLit 5))))``
val c37 = f e37
val [Number i] = g c37
val SOME 0 = intML.toInt i;
val e38 = ``Let "z" (Fun "x" (Mat (Var "x") [(Plit (IntLit 0), (Var "x"));(Pvar "y", (App (Opn Minus) (Var "x") (Var "y")))])) (App Opapp (Var "z") (Val (Lit (IntLit 5))))``
val c38 = f e38
val [Number i] = g c38
val SOME 0 = intML.toInt i;
val e39 = ``Letrec [("z", ("x", (Mat (Var "x") [(Plit (IntLit 0), (Var "x"));(Pvar "y", (App (Opn Minus) (Var "x") (Var "y")))])))] (App Opapp (Var "z") (Val (Lit (IntLit 5))))``
val c39 = f e39
val [Number i] = g c39
val SOME 0 = intML.toInt i;
val _ = ml_translatorLib.translate listTheory.APPEND
val d0 = listd
val append_defs = ``
  [("APPEND","v3",
    Fun "v4"
      (Mat (Var "v3")
         [(Pcon "Nil" [],Var "v4");
          (Pcon "Cons" [Pvar "v2"; Pvar "v1"],
           Con "Cons"
             [Var "v2";
              App Opapp (App Opapp (Var "APPEND") (Var "v1"))
                (Var "v4")])]))] ``
val d1 = ``Dletrec ^append_defs``
val e33 = ``App Opapp (Var "APPEND") (Con "Nil" [])``
val (m,st) = pd1 e33 [d0,d1]
val tm = pv m (hd st) NTfn
val true = tm = (term_to_v ``Closure [] "" (Var "")``);
val e34 = ``App Opapp (App Opapp (Var "APPEND") (Con "Nil" []))
                      (Con "Nil" [])``
val (m,st) = pd1 e34 [d0,d1]
val [r,cl] = st
val tm = pv m r (NTapp ([NTnum],"list"))
val true = tm = (term_to_v ``Conv "Nil" []``)
val tm = pv m cl NTfn
val true = tm = (term_to_v ``Closure [] "" (Var "")``);
fun h t = hd(tl(snd(strip_comb(concl t))))
val t = ml_translatorLib.hol2deep ``[1;2;3]++[4;5;6:num]``
val e30 = h t
val (m,st) = pd1 e30 [d0,d1]
val [res,cl] = st
val tm = pv m res (NTapp ([NTnum],"list"))
val true = tm = (term_to_v (ml_translatorLib.hol2val ``[1;2;3;4;5;6:num]``));
val t = ml_translatorLib.hol2deep ``[]++[4:num]``
val e32 = h t
val (m,st) = pd1 e32 [d0,d1]
val [res,cl] = st
val tm = pv m res (NTapp ([NTnum],"list"))
val true = tm = (term_to_v ``Conv "Cons" [Lit (IntLit 4); Conv "Nil" []]``);
val paird = ``
Dtype [(["'a"; "'b"],"prod",[("Pair_type",[Tvar "'a"; Tvar "'b"])])]
``
val d2 = paird
val d3 = ``
Dletrec
  [("PART","v3",
    Fun "v4"
      (Fun "v5"
         (Fun "v6"
            (Mat (Var "v4")
               [(Pcon "Nil" [],Con "Pair_type" [Var "v5"; Var "v6"]);
                (Pcon "Cons" [Pvar "v2"; Pvar "v1"],
                 If (App Opapp (Var "v3") (Var "v2"))
                   (App Opapp
                      (App Opapp
                         (App Opapp (App Opapp (Var "PART") (Var "v3"))
                            (Var "v1"))
                         (Con "Cons" [Var "v2"; Var "v5"])) (Var "v6"))
                   (App Opapp
                      (App Opapp
                         (App Opapp (App Opapp (Var "PART") (Var "v3"))
                            (Var "v1")) (Var "v5"))
                      (Con "Cons" [Var "v2"; Var "v6"])))]))))]
`` val d4 = ``
Dlet (Pvar "PARTITION")
  (Fun "v1"
     (Fun "v2"
        (App Opapp
           (App Opapp
              (App Opapp (App Opapp (Var "PART") (Var "v1")) (Var "v2"))
              (Con "Nil" [])) (Con "Nil" []))))
`` val d5 = ``
Dletrec
  [("QSORT","v7",
    Fun "v8"
      (Mat (Var "v8")
         [(Pcon "Nil" [],Con "Nil" []);
          (Pcon "Cons" [Pvar "v6"; Pvar "v5"],
           Let "v3"
             (App Opapp
                (App Opapp (Var "PARTITION")
                   (Fun "v4"
                      (App Opapp (App Opapp (Var "v7") (Var "v4"))
                         (Var "v6")))) (Var "v5"))
             (Mat (Var "v3")
                [(Pcon "Pair_type" [Pvar "v2"; Pvar "v1"],
                  App Opapp
                    (App Opapp (Var "APPEND")
                       (App Opapp
                          (App Opapp (Var "APPEND")
                             (App Opapp
                                (App Opapp (Var "QSORT") (Var "v7"))
                                (Var "v2")))
                          (Con "Cons" [Var "v6"; Con "Nil" []])))
                    (App Opapp (App Opapp (Var "QSORT") (Var "v7"))
                       (Var "v1")))]))]))]
``
val _ = ml_translatorLib.translate sortingTheory.PART_DEF
val _ = ml_translatorLib.translate sortingTheory.PARTITION_DEF
val _ = ml_translatorLib.translate sortingTheory.QSORT_DEF
val t = ml_translatorLib.hol2deep ``QSORT (λx y. x ≤ y) [9;8;7;6;2;3;4;5:num]``
val e31 = h t;
val (m,st) = pd1 e31 [d0,d1,d2,d3,d4,d5]
val [res,clQSORT,clPARTITION,clPART,clAPPEND] = st
val tm = pv m res (NTapp([NTnum],"list"))
val true = tm = term_to_v(ml_translatorLib.hol2val ``[2;3;4;5;6;7;8;9:num]``);
val d = ``
Dlet (Pvar "add1")
  (Fun "x" (App (Opn Plus) (Var "x") (Val (Lit (IntLit 1)))))``
val e40 = ``App Opapp (Var "add1") (Val (Lit (IntLit 1)))``
val (m,st) = pd1 e40 [d]
val [res,add1] = st
val true = pv m res NTnum = term_to_v(ml_translatorLib.hol2val ``2:int``);
val e43 = ``Letrec [("o","n",
  If (App Equality (Var "n") (Val (Lit (IntLit 0))))
     (Var "n")
     (App Opapp
       (Var "o")
       (App (Opn Minus) (Var "n") (Val (Lit (IntLit 1))))))]
  (App Opapp (Var "o") (Val (Lit (IntLit 1000))))``
val c43 = f e43
val SOME s43 = bc_eval_limit 12 (init_state c43)
val [Number i] = bc_state_stack s43
val SOME 0 = intML.toInt i;
val d = ``Dletrec
[("o","n",
  If (App Equality (Var "n") (Val (Lit (IntLit 0))))
     (Var "n")
     (App Opapp
       (Var "o")
       (App (Opn Minus) (Var "n") (Val (Lit (IntLit 1))))))]``
val e44 = ``App Opapp (Var "o") (Val (Lit (IntLit 1000)))``
val (m,st) = pd1 e44 [d]
val [Number i, cl] = st
val SOME 0 = intML.toInt i;
val d0 = paird
val d1 = ``Dlet (Pcon "Pair_type" [Pvar "x";Pvar "y"]) (Con "Pair_type" [Val (Lit (IntLit 1));Val (Lit (IntLit 2))])``
val d2 = ``Dlet (Pvar "x") (Val (Lit (IntLit 3)))``
val e45 = ``Con "Pair_type" [Var "x";Var "y"]``
val (m,st) = pd1 e45 [d0,d1,d2]
val [Block (_,[Number xb,Number yb]),Number x,Number y] = st
val SOME 3 = intML.toInt x
val SOME 2 = intML.toInt y
val true = xb = x
val true = yb = y;
val d1 = ``Dlet (Pcon "Pair_type" [Pvar "y";Pvar "x"]) (Con "Pair_type" [Val (Lit (IntLit 1));Val (Lit (IntLit 2))])``
val d2 = ``Dlet (Pvar "x") (Val (Lit (IntLit 3)))``
val e46 = ``Con "Pair_type" [Var "x";Var "y"]``
val (m,st) = pd1 e46 [d0,d1,d2]
val [Block (_,[Number xb,Number yb]),Number y,Number x] = st
val SOME 3 = intML.toInt xb
val SOME 1 = intML.toInt yb
val true = x = xb
val true = y = yb;
