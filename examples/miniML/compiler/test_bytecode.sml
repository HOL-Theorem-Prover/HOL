val _ = map load ["rich_listTheory","compilerTheory"]

val REPLACE_ELEMENT_compute =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV rich_listTheory.REPLACE_ELEMENT_DEF

val d = !Globals.emitMLDir
val _ = map (fn s => (use (d^s^"ML.sig"); use (d^s^"ML.sml")))
["combin","pair","num","option","list","set",
 "fmap","sum","fcp","string","bit","words","int",
 "rich_list","bytecode"]

open bytecodeML

open compilerTheory

val s = ``<| env := []; next_label := 0; inst_length := λi. 0 |>``

val _ = computeLib.add_thms
[ listTheory.SUM
, REPLACE_ELEMENT_compute
] computeLib.the_compset

fun term_to_num x = (numML.fromString (Parse.term_to_string x))
fun term_to_int x = (intML.fromString ((Parse.term_to_string x)^"i"))

fun term_to_stack_op tm = let
  val (f,x) = dest_comb tm
in(case fst (dest_const f) of
    "PushInt" => PushInt (term_to_int x)
  | "Load" => Load (term_to_num x)
  | "Store" => Store (term_to_num x)
  | "Pops" => Pops (term_to_num x)
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
  | s => raise Fail s
val term_to_bc_list = (map term_to_bc) o fst o listSyntax.dest_list
fun f1 e = EVAL ``FST (compile (^e,^s))``
fun f2 e = rhs (concl (f1 e))
fun f e = term_to_bc_list (f2 e)
fun g1 c = bc_eval (init_state c)
fun g c = bc_state_stack (g1 c)

val e1 = ``Val (Lit (IntLit 42))``
val c1 = f e1
val [Number i] = g c1
val SOME 42 = intML.toInt i
val e2 = ``If (Val (Lit (Bool T))) (Val (Lit (IntLit 1))) (Val (Lit (IntLit 2)))``
val c2 = f e2
val [Number i] = g c2
val SOME 1 = intML.toInt i
val e3 = ``If (Val (Lit (Bool F))) (Val (Lit (IntLit 1))) (Val (Lit (IntLit 2)))``
val c3 = f e3
val [Number i] = g c3
val SOME 2 = intML.toInt i
val e4 = ``App Equality (Val (Lit (IntLit 1))) (Val (Lit (IntLit 2)))``
val c4 = f e4
val [Number i] = g c4
val SOME 0 = intML.toInt i
val e5 = ``Fun "x" (Var "x")``
val c5 = f e5
val st = g c5 (* TODO: looks like closures might contain empty blocks. don't do that *)
val e6 = ``Let "x" (Val (Lit (IntLit 1))) (App (Opn Plus) (Var "x") (Var "x"))``
val c6 = f e6
val [Number i] = g c6
val SOME 2 = intML.toInt i (* TODO: Exception- Bind raised. fix this *)
