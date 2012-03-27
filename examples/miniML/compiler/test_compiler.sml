val _ = map load ["rich_listTheory","compileProofsTheory"]

val REPLACE_ELEMENT_compute =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV rich_listTheory.REPLACE_ELEMENT_DEF

val ITSET_FOLDL = prove(
``∀f s a. ITSET f s a = if FINITE s then FOLDL (combin$C f) a (SET_TO_LIST s) else ARB``, SRW_TAC[][listTheory.ITSET_eq_FOLDL_SET_TO_LIST] THEN
   SRW_TAC[][Once pred_setTheory.ITSET_def])

val compset = listSimps.list_compset()

val _ = computeLib.add_thms
[ listTheory.LIST_TO_SET_THM
, listTheory.SUM
, REPLACE_ELEMENT_compute
, pred_setTheory.EMPTY_DIFF
, pred_setTheory.INSERT_DIFF
, pred_setTheory.FINITE_EMPTY
, pred_setTheory.FINITE_INSERT
, ITSET_FOLDL
, pairTheory.UNCURRY
, pairTheory.FST
, pairTheory.SND
, combinTheory.K_THM
, combinTheory.K_o_THM
, combinTheory.C_DEF
, optionTheory.option_case_compute
, optionTheory.IS_SOME_DEF
, optionTheory.THE_DEF
, finite_mapTheory.FAPPLY_FUPDATE_THM
, finite_mapTheory.FRANGE_FEMPTY
, finite_mapTheory.FINITE_FRANGE
, compileProofsTheory.FINITE_free_vars
, BytecodeTheory.bool_to_int_def
, compileProofsTheory.remove_Gt_Geq_def
, compileProofsTheory.remove_mat_exp_def
, compileProofsTheory.exp_to_Cexp_def
, CompileTheory.compile0_def
, compileProofsTheory.free_vars_def
, compileProofsTheory.remove_mat_def
, CompileTheory.remove_mat_vp_def
, CompileTheory.extend_def
, CompileTheory.incsz_def
, CompileTheory.decsz_def
, CompileTheory.emit_def
, CompileTheory.prim2_to_bc_def
, CompileTheory.find_index_def
, compileProofsTheory.compile_varref_def
, compileProofsTheory.compile_def
, CompileTheory.compiler_state_accessors
, CompileTheory.compiler_state_updates_eq_literal
, CompileTheory.compiler_state_accfupds
, CompileTheory.compiler_state_fupdfupds
, CompileTheory.compiler_state_literal_11
, CompileTheory.compiler_state_fupdfupds_comp
, CompileTheory.compiler_state_fupdcanon
, CompileTheory.compiler_state_fupdcanon_comp
] compset

val _ = computeLib.set_skip compset combinSyntax.K_tm (SOME 1)

val _ = computeLib.add_conv (``least_not_in``,1,
  fn tm => let
  val (_,[s]) = boolSyntax.strip_comb tm
  val finite = EQT_ELIM (computeLib.CBV_CONV compset ``FINITE ^s``)
  val th = MP (SPEC s compileProofsTheory.least_not_in_thm) finite
  in th end) compset

val _ = computeLib.add_conv (``least_aux``,2,
let fun f tm = let
  val (_,[p,n]) = boolSyntax.strip_comb tm
  val pp = SIMP_CONV (srw_ss()) [] ``^p ^n``
  val th = SIMP_CONV bool_ss [Once fsetTheory.least_aux_def,pp] tm
  in if rhs(concl(pp)) = T then TRANS th (f(rhs(concl th))) else th end
in f end) compset

(*
val _ = computeLib.add_conv (``num_set_fold``,...
*)

val d = !Globals.emitMLDir
val _ = map (fn s => (use (d^s^"ML.sig"); use (d^s^"ML.sml")))
["combin","pair","num","option","list","set",
 "fmap","sum","fcp","string","bit","words","int",
 "rich_list","bytecode"]

open bytecodeML

fun bc_evaln 0 s = s
  | bc_evaln n s = let
    val SOME s = bc_eval1 s in
      bc_evaln (n-1) s
    end handle Bind => (print "Fail\n"; s)

val test_cnmap = ``FEMPTY |+ ("Nil",0:num) |+ ("Cons",1)``
val s = ``<| env := FEMPTY; code := []; next_label := 1; sz := 0; inst_length := λi. 0 |>``
fun term_to_num x = (numML.fromString (Parse.term_to_string x))
fun term_to_int x = (intML.fromString ((Parse.term_to_string x)^"i"))
fun term_to_stack_op tm = let
  val (f,x) = dest_comb tm
in(case fst (dest_const f) of
    "PushInt" => PushInt (term_to_int x)
  | "Load" => Load (term_to_num x)
  | "Store" => Store (term_to_num x)
  | "Pops" => Pops (term_to_num x)
  | "El" => El (term_to_num x)
  | "TagEquals" => TagEquals (term_to_num x)
  | s => raise Fail s
  )
handle HOL_ERR _ => let
  val (f,w) = dest_comb f
in case fst (dest_const f) of
    "Cons" => Cons (term_to_num w,term_to_num x)
  | s => raise Fail s
end end handle HOL_ERR _ =>
  case fst (dest_const tm) of
    "Equal" => Equal
  | "Pop" => Pop
  | "Add" => Add
  | "Sub" => Sub
  | "Less" => Less
  | "IsNum" => IsNum
  | s => raise Fail s
fun term_to_bc tm = let
  val (f,x) = dest_comb tm
in case fst (dest_const f) of
    "Jump" => Jump (term_to_num x)
  | "JumpNil" => JumpNil (term_to_num x)
  | "Stack" => Stack (term_to_stack_op x)
  | "Call" => Call (term_to_num x)
  | s => raise Fail s
end handle HOL_ERR _ =>
  case fst (dest_const tm) of
    "Return" => Return
  | "CallPtr" => CallPtr
  | "Exception" => Exception
  | s => raise Fail s
val term_to_bc_list = (map term_to_bc) o fst o listSyntax.dest_list
fun f0 e = ``compile0 ^test_cnmap ^e``
fun f1 e = computeLib.CBV_CONV compset ``REVERSE (compile ^s ^(f0 e)).code``
fun f2 e = rhs (concl (f1 e))
fun f e = term_to_bc_list (f2 e)
fun g1 c = bc_eval (init_state c)
fun g c = bc_state_stack (g1 c)

val e1 = ``Val (Lit (IntLit 42))``
val c1 = f e1
val [Number i] = g c1
val SOME 42 = intML.toInt i;
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

f2 e5
computeLib.CBV_CONV compset ``
      FOLDL
                          (combin$C
                             (λfv (n,env,ec).
                                if
                                  IS_SOME
                                    (if least_not_in ∅ = fv then
                                       SOME 1
                                     else
                                       NONE)
                                then
                                  (n,
                                   env |+
                                   (fv,
                                    CTArg
                                      (3 −
                                       THE
                                         (if least_not_in ∅ = fv then
                                            SOME 1
                                          else
                                            NONE))),ec)
                                else
                                  (n + 1,env |+ (fv,CTEnv n),
                                   CEEnv fv::ec))) (0,FEMPTY,[])
                          (SET_TO_LIST {least_not_in ∅})
``

val c5 = f e5
val st = g c5
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
val c8 = ff e8
val [Number i] = g c8
val SOME 1 = intML.toInt i;
val e9 = ``
Let "1?" (Fun "x" (App Equality (Var "x") (Val (Lit (IntLit 1)))))
  (Let "x" (Val (Lit (IntLit 1)))
    (Let "x" (App (Opn Minus) (Var "x") (Var "x"))
      (App Opapp (Var "1?") (Var "x"))))``
val c9 = ff e9
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
val c12 = ff e12
val [Number i] = g c12
val SOME 0 = intML.toInt i;
val e13 = ``
Let "lq2" (Fun "x" (App (Opb Leq) (Var "x") (Val (Lit (IntLit 2)))))
  (App Opapp (Var "lq2") (Val (Lit (IntLit 0))))``
val c13 = ff e13
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

EVAL(f0 e15)

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
val e22 = ``Con (SOME "Cons") [Val (Lit (Bool T)); Con (SOME "Nil") []]``
val c22 = f e22
val [Block (t1,[Number i,Number t2])] = g c22
val SOME 1 = numML.toInt t1
val SOME 1 = intML.toInt i
val SOME 0 = intML.toInt t2;
val e23 = ``Mat (Con (SOME "Cons") [Val (Lit (IntLit 2));
                 Con (SOME "Cons") [Val (Lit (IntLit 3));
                 Con (SOME "Nil") []]])
            [(Pcon (SOME "Cons") [Pvar "x"; Pvar "xs"],
              Var "x");
             (Pcon (SOME "Nil") [],
              Val (Lit (IntLit 1)))]``
val c23 = f e23
val [Number i] = g c23 (* TODO: Exception- Bind raised *)
val SOME 2 = intML.toInt i;
val e24 = ``Mat (Con (SOME "Nil") [])
            [(Pcon (SOME "Nil") [], Val (Lit (Bool F)))]``
val c24 = f e24
val [Number i] = g c24
val SOME 0 = intML.toInt i;
val e25 = ``Mat (Con (SOME "Cons") [Val (Lit (IntLit 2));
                 Con (SOME "Nil") []])
            [(Pcon (SOME "Cons") [Pvar "x"; Pvar "xs"],
              Var "x")]``
val c25 = f e25
val [Number i] = g c25
val SOME 2 = intML.toInt i;
val e26 = ``Mat (Con (SOME "Cons") [Val (Lit (IntLit 2));
                 Con (SOME "Nil") []])
            [(Pcon (SOME "Cons") [Plit (IntLit 2);
              Pcon (SOME "Nil") []],
              Val (Lit (IntLit 5)))]``
val c26 = f e26
val [Number i] = g c26 (* TODO: Exception- Bind raised *)
val SOME 5 = intML.toInt i;
