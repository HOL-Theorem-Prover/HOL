open HolKernel Parse boolTheory boolLib

fun tprint s = print (StringCvt.padRight #" " 65 (s ^ " ... "))

fun substtest (M, x, N, result) = let
in
  tprint("Testing ["^term_to_string M^"/"^term_to_string x^"] ("^
         term_to_string N^") = "^term_to_string result);
  if aconv (Term.subst[x |-> M] N) result then (print "OK\n"; true)
  else (print "FAILED!\n"; false)
end

val x = mk_var("x", Type.alpha)
val xfun = mk_var("x", Type.alpha --> Type.alpha)
val y = mk_var("y", Type.alpha)
val Id = mk_abs(x,x)
val Idy = mk_abs(y,y)

(* tests that substitutions work, deferred until this point so that we get
   access to the parser (which is implicitly a test of the parser too) *)

val tests = [(x,x,y,y),
             (x,y,y,x),
             (x,x,x,x),
             (y,x,Id,Id),
             (Id,xfun,xfun,Id),
             (x,y,Id,Idy),
             (y,x,``\y. y ^x : 'b``, ``\z. z ^y :'b``)]

(* test for the INST_TYPE bug that allows instantiation to cause a
   free variable to become captured.  *)
val inst_type_test = let
  val _ = tprint "Testing HOL Light INST_TYPE bug"
  val ximpnx = prove(
    ``(x ==> ~x) = ~x``,
    ASM_CASES_TAC ``x:bool`` THEN ASM_REWRITE_TAC [])
  val nximpx = prove(
    ``(~x ==> x) = x``,
    ASM_CASES_TAC ``x:bool`` THEN ASM_REWRITE_TAC [])
  val xandnx = prove(
    ``~(x /\ ~x) /\ ~(~x /\ x)``,
    ASM_CASES_TAC ``x:bool`` THEN ASM_REWRITE_TAC [])
  val x_b = mk_var("x", bool)
  val x_a = mk_var("x", alpha)
  val P = mk_var("P", alpha --> bool --> bool)
  val Pxaxb = list_mk_comb(P, [x_a, x_b])
  val exxPxaxb = mk_exists(x_b, Pxaxb)
  val nonempty_t = mk_var("nonempty", (bool --> bool) --> bool)
  val f = mk_var("f", bool --> bool)
  val nonempty_rhs = mk_abs(f, mk_exists(x_b, mk_comb(f, x_b)))
  val nonempty_eqn = mk_eq(nonempty_t, nonempty_rhs)
  val nonempty_exists =
      EQT_ELIM (REWRITE_CONV [EXISTS_REFL]
                             (mk_exists(nonempty_t, nonempty_eqn)))
  val nonempty_th = ASSUME nonempty_eqn
  val nonempty_Px = ASSUME (mk_comb(nonempty_t, mk_comb(P, x_a)))
  val exxPxaxb_th = ASSUME exxPxaxb
  val nonempty_Px_th = RIGHT_BETA (AP_THM nonempty_th (mk_comb(P, x_a)))
  val Pxx' = rhs (concl nonempty_Px_th)
  val Pxx'_eq_Pxx = ALPHA Pxx' exxPxaxb
  val th0 = EQ_MP Pxx'_eq_Pxx (EQ_MP nonempty_Px_th nonempty_Px)
  val th1 = INST_TYPE [alpha |-> bool] th0
  val uvneg = ``\u v. v = ~u``
  val th2 = INST [inst [alpha |-> bool] P |-> uvneg] th1
  val uvneg_x = mk_comb(uvneg, x_b)
  val uvneg_nonempty =
      EQT_ELIM
        (CONV_RULE
           (RAND_CONV (REWRITE_CONV [nonempty_th] THENC BETA_CONV THENC
                       QUANT_CONV BETA_CONV THENC REWRITE_CONV [EXISTS_REFL]))
           (AP_TERM nonempty_t (BETA_CONV uvneg_x)))
  val th3 = BETA_RULE (PROVE_HYP uvneg_nonempty th2)
  val th4 = REWRITE_RULE [EQ_IMP_THM, ximpnx, nximpx, xandnx] th3
  val final_th = CHOOSE (nonempty_t, nonempty_exists) th4
in
  if same_const (concl final_th) (mk_const("F", bool)) then
    (print "FAILED!\n"; Process.exit Process.failure)
  else print "OK\n"
end

(* Test for the experimental kernel's INST_TYPE bug (discovered by Peter
   Homeier in June 2009). *)
exception ExitOK
val _ = let
  val _ = tprint "Testing for expk INST_TYPE bug"
  fun x ty = mk_var("x", ty)
  fun y ty = mk_var("y", ty)
  val a = alpha
  val b = beta
  val t1 = list_mk_abs ([x a,x b], x a)
  val t1_applied = list_mk_comb(t1, [x a, y b])
  val t1_th = RIGHT_LIST_BETA (REFL t1_applied)
  val t2 = list_mk_abs([x a,x a], x a)
  val t2_applied = list_mk_comb(t2, [x a, y a])
  val t2_th = RIGHT_LIST_BETA (REFL t2_applied)
  val t1_inst = INST_TYPE [beta |-> alpha] t1_th (* bug *)
  val bad1 = TRANS (SYM t1_inst) t2_th
             handle HOL_ERR _ => raise ExitOK
  val bad2 = INST_TYPE [alpha |-> bool] bad1
  val Falsity = EQ_MP (INST [x bool |-> T, y bool |-> F] bad2) TRUTH
in
  if aconv (concl Falsity) F then print "FAILED!\n" else print "Huh???\n";
  Process.exit Process.failure
end handle ExitOK => print "OK\n"

val _ = Process.atExit (fn () => let
                             fun rm s = FileSys.remove s
                                        handle _ => ()
                           in
                             app rm ["scratchTheory.sml", "scratchTheory.sig"]
                           end)

fun test f x = f x orelse (print "FAILED!\n"; Process.exit Process.failure)
val oldconstants_test = let
  val _ = tprint "Identity of old constants test"
  val defn1_t = mk_eq(mk_var("foo", bool), boolSyntax.T)
  val defn2_t = mk_eq(mk_var("foo", bool), boolSyntax.F)
  val defn1 = new_definition("foo", defn1_t)
  val defn2 = new_definition("foo2", defn2_t)
  val defn3 = new_definition("foo3", defn1_t)
  val c1 = lhs (concl defn1)
  val c2 = lhs (concl defn2)
  val c3 = lhs (concl defn3)
  val _ = test (fn (c1,c2) => Term.compare(c1, c2) <> EQUAL) (c1, c2)
  val _ = test (not o uncurry aconv) (c1, c2)
  val _ = test (not o uncurry aconv) (c1, c3)
  val _ = test (not o uncurry aconv) (c2, c3)
  val _ = test (String.isPrefix "old" o #Name o dest_thy_const) c1
  val _ = test (String.isPrefix "old" o #Name o dest_thy_const) c2
  val _ = Feedback.emit_MESG := false
  val _ = Feedback.emit_WARNING := false
  val _ = new_theory "foo"
  val defn1 = new_definition("c", mk_eq(mk_var("c", bool), boolSyntax.T))
  val _ = new_theory "foo"
  val defn2 = new_definition("c", mk_eq(mk_var("c", bool), boolSyntax.T))
  val c1 = lhs (concl defn1)
  val c2 = lhs (concl defn2)
  val _ = test (fn (c1, c2) => Term.compare(c1,c2) <> EQUAL) (c1, c2)
  val _ = test (not o uncurry aconv) (c1, c2)
in
  print "OK\n"
end

val t = Parse.Term `(case T of T -> (\x. x) || F -> (~)) y`
val _ = tprint "Testing parsing of case expressions with function type"
val _ = case Lib.total (find_term (same_const ``bool_case``)) t of
          NONE => (print "FAILED\n"; Process.exit Process.failure)
        | SOME _ => print "OK\n"

val _ = tprint "Testing parsing of _ variables (1)"
val t = case Lib.total Parse.Term `case b of T -> F || _ -> T` of
          NONE => (print "FAILED\n"; Process.exit Process.failure)
        | SOME _ => print "OK\n"
val _ = tprint "Testing parsing of _ variables (2)"
val t = case Lib.total Parse.Term `case b of T -> F || _1 -> T` of
          NONE => (print "FAILED\n"; Process.exit Process.failure)
        | SOME _ => print "OK\n"
val _ = tprint "Testing independence of case branch vars"
val t = case Lib.total Parse.Term `v (case b of T -> F || v -> T)` of
          NONE => (print "FAILED\n"; Process.exit Process.failure)
        | SOME _ => print "OK\n"


fun tpp s = let
  val t = Parse.Term [QUOTE s]
  val _ = tprint ("Testing printing of `"^s^"`")
  val res = term_to_string t
in
  if res = s then print "OK\n"
  else (print "FAILED!\n"; Process.exit Process.failure)
end


val _ = app tpp ["let x = T in x /\\ y",
                 "(let x = T in \\y. x /\\ y) p",
                 "f ($/\\ p)",
                 "(((p /\\ q) /\\ r) /\\ s) /\\ t",
                 "(case x of T -> (\\x. x) || F -> $~) y"]


val _ = Process.exit (if List.all substtest tests then Process.success
                      else Process.failure)
