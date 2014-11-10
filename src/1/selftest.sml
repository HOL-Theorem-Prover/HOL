open HolKernel Parse boolTheory boolLib

val _ = set_trace "Unicode" 0

fun die s = (print (s ^ "\n"); OS.Process.exit OS.Process.failure)

val tprint = testutils.tprint

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
  if same_const (concl final_th) (mk_const("F", bool)) then die "FAILED!"
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
  if aconv (concl Falsity) F then die "FAILED!" else die "Huh???"
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

val t = Parse.Term `(case T of T => (\x. x) | F => (~)) y`
val _ = tprint "Testing parsing of case expressions with function type"
val _ = case Lib.total (find_term (same_const boolSyntax.bool_case)) t of
          NONE => die "FAILED"
        | SOME _ => print "OK\n"

val _ = tprint "Testing parsing of case expressions with leading bar"
val t_opt = SOME (trace ("syntax_error", 0) Parse.Term
                        `case T of | T => F | F => T`)
    handle HOL_ERR _ => NONE
val _ = case t_opt of
          SOME t =>
            if Lib.can (find_term (same_const boolSyntax.bool_case)) t then
              print "OK\n"
            else die "FAILED"
        | NONE => die "FAILED"

val _ = tprint "Testing parsing of _ variables (1)"
val t = case Lib.total Parse.Term `case b of T => F | _ => T` of
          NONE => die "FAILED"
        | SOME _ => print "OK\n"
val _ = tprint "Testing parsing of _ variables (2)"
val t = case Lib.total Parse.Term `case b of T => F | _1 => T` of
          NONE => die "FAILED"
        | SOME _ => print "OK\n"
val _ = tprint "Testing independence of case branch vars"
val t = case Lib.total Parse.Term `v (case b of T => F | v => T)` of
          NONE => die "FAILED"
        | SOME _ => print "OK\n"

val _ = tprint "Testing higher-order match 1"
local
val thy = current_theory()
val fmap_ty = let val () = new_type("fmap", 2) in mk_type("fmap", [alpha,beta])
              end
val submap = let
  val () = new_constant("SUBMAP", fmap_ty --> fmap_ty --> bool)
in
  prim_mk_const{Thy = thy, Name = "SUBMAP"}
end
val pair_ty = let val () = new_type("prod", 2) in
                mk_thy_type{Thy = thy, Tyop = "prod", Args = [alpha,beta]}
              end
val fmpair_ty = mk_thy_type{Thy = thy, Tyop = "prod", Args = [fmap_ty, gamma]}
val num_ty = let val () = new_type("num", 0)
             in mk_thy_type{Thy = thy, Tyop = "num", Args = []}
             end
val lt = let val () = new_constant("<", num_ty --> num_ty --> bool)
         in
           prim_mk_const{Thy = thy, Name = "<"}
         end
val FST = let val () = new_constant("FST", pair_ty --> alpha)
          in
            mk_thy_const{Thy = thy, Name = "FST", Ty = fmpair_ty --> fmap_ty}
          end
val R = mk_var("R", alpha --> alpha --> bool)
val f = mk_var("f", num_ty --> alpha)
val f' = mk_var("f", num_ty --> fmpair_ty)
val m = mk_var("m", num_ty)
val n = mk_var("n", num_ty)
val ant = let
  val () = new_constant("ant", (alpha --> alpha --> bool) -->
                               (num_ty --> alpha) --> bool)
in
  prim_mk_const{Thy = thy, Name = "ant"}
end
val th = let
  val concl =
      list_mk_forall([m,n],
                     mk_imp(list_mk_comb(lt,[m,n]),
                            list_mk_comb(R,[mk_comb(f,m), mk_comb(f,n)])))
in
  mk_thm([], list_mk_forall([R,f],
                            mk_imp(list_mk_comb(ant, [R,f]), concl)))
end
val goal = list_mk_forall([m,n],
                          mk_imp(list_mk_comb(lt, [m,n]),
                                 list_mk_comb(submap,
                                              [mk_comb(FST, mk_comb(f',m)),
                                               mk_comb(FST, mk_comb(f',n))])))
val expected = let
  val ant' = Term.inst [alpha |-> fmap_ty] ant
  val abs = mk_abs(n, mk_comb(FST, mk_comb(f',n)))
in
  list_mk_comb(ant', [submap, abs])
end
in
val _ =
    case Lib.total (VALID (HO_MATCH_MP_TAC th)) ([], goal) of
      SOME ([([],subgoal)],_) => if aconv subgoal expected then print "OK\n"
                                 else die "FAILED!"
    | _ => die "FAILED!"
end (* local *)

val _ = tprint "Testing type-specific Unicode overload 1"
val _ = set_trace "Unicode" 1
val _ = overload_on (UnicodeChars.delta, ``$! :(('a -> 'b)->bool)->bool``)
fun checkparse () = let
  val tm = Lib.with_flag (Globals.notify_on_tyvar_guess, false)
                         Parse.Term
                         `!x. P x`
  val randty =  type_of (rand tm)
in
  if Type.compare(randty, alpha --> bool) <> EQUAL then die "FAILED!"
  else print "OK\n"
end
val _ = checkparse()

(* bounce Unicode trace - and repeat *)
val _ = tprint "Testing type-specific Unicode overload 2"
val _ = set_trace "Unicode" 0
val _ = set_trace "Unicode" 1
val _ = checkparse ()

(* test for type abbreviation bug caused by stale types in a TypeNet.*)
val _ = tprint "Testing stale type abbreviations bug"
val _ = new_type ("foo", 1)
val _ = type_abbrev("bar", ``:bool foo``)
val _ = new_type ("foo", 0)
val _ = type_abbrev("baz", ``:foo``) handle _ => die "FAILED!"
val _ = print "OK\n"


(* pretty-printing tests - turn Unicode off *)
val tpp = let open testutils
             in
               unicode_off (raw_backend testutils.tpp)
             end

fun typp s = let
  open testutils
  val ty = Parse.Type [QUOTE s]
  val _ = tprint ("Testing p/printing of "^s)
  val res = unicode_off (raw_backend type_to_string) ty
in
  if s <> res then die "FAILED!\n" else print "OK\n"
end

val _ = app typp [":bool", ":bool -> bool", ":'a -> bool",
                  ":'a -> 'b -> 'c",
                  ":(bool -> bool) -> 'a"]
local
  open testutils
  val ct = current_theory
  val _ = new_type ("option", 1)
  val ty = mk_thy_type{Thy = ct(), Tyop = "option", Args = [alpha --> beta]}
  val _ = tprint ("Testing p/printing of (min_grammar) (('a -> 'b) "^ct()^"$option)")
  val pfn =
    PP.pp_to_string 70 (#1 (print_from_grammars min_grammars))
                    |> raw_backend
                    |> unicode_off
  val s = pfn ty
in
val _ = if s = "(('a -> 'b) "^ct()^"$option)" then print "OK\n"
        else die ("FAILED! - "^s)
end


val _ = app tpp ["let x = T in x /\\ y",
                 "(let x = T in \\y. x /\\ y) p",
                 "f ($/\\ p)",
                 "(((p /\\ q) /\\ r) /\\ s) /\\ t",
                 "!x. P (x /\\ y)",
                 "P (!x. Q x)",
                 "\\x. ?y. P x y",
                 "P (\\x. ?y. Q x y)",
                 "(:'a)"]

val _ = tpp "x = y"
val _ = Lib.with_flag (testutils.linewidth, 10) tpp "xxxxxx =\nyyyyyy"

val _ = add_rule {term_name = "=",
                  fixity = Infix(NONASSOC, 100),
                  block_style = (AroundSamePrec, (PP.CONSISTENT,0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,2)]}
val _ = Lib.with_flag (testutils.linewidth, 10) tpp "xxxxxx =\n  yyyyyy"

val _ = print "** Tests with Unicode on PP.avoid_unicode both on\n"
val _ = let
  open testutils
  fun md f = trace ("Unicode", 1) (trace ("PP.avoid_unicode", 1) f)
  fun texp (i,out) = md tpp_expected
                        {testf = standard_tpp_message, input = i, output = out}
  val _ = temp_overload_on ("⊤", ``T``)
in
  app (md tpp) ["!x. p x /\\ q x", "\\x. x", "\\x::p. x /\\ y",
                "!x::p. q x \\/ r x", "!x. x /\\ T <=> x"];
  app texp [("∀x. p x", "!x. p x"), ("x ∧ y", "x /\\ y"),
            ("λx. x", "\\x. x")];
  temp_clear_overloads_on "⊤"
end

val _ = print "** Tests with pp_dollar_escapes = 0.\n"
val _ = set_trace "pp_dollar_escapes" 0
val _ = app tpp ["(/\\)", "(if)"]
val _ = set_trace "pp_dollar_escapes" 1

val _ = new_type ("foo", 2)
val _ = new_constant ("con", ``:'a -> ('a,'b)foo``)
val _ = set_trace "types" 1
val _ = print "** Tests with 'types' trace on.\n"
val _ = tpp "(con (x :'a) :('a, 'b) foo)"
val _ = tpp "\\(x :'a) (y :'a). x = y"
val _ = tpp "(ARB (x :'a) :'b)"

(* pretty-printing - tests of colouring *)
val _ = Parse.current_backend := PPBackEnd.vt100_terminal
val _ = set_trace "types" 0
val _ = set_trace "Unicode" 0
fun tpp (s,expected) = let
  val t = Parse.Term [QUOTE s]
  val _ = tprint ("Testing (colour-)printing of `"^s^"`")
  val res = ppstring pp_term t
in
  if res = expected then print "OK\n"
  else (print "FAILED\n"; Process.exit Process.failure)
end

fun bound s = "\^[[0;32m" ^ s ^ "\^[[0m"
fun free s = "\^[[0;1;34m" ^ s ^ "\^[[0m"
val concat = String.concat

val bx = bound "x"
val fy = free "y"
val fp = free "p"
val fx = free "x"

val _ = app tpp [
  ("\\x. x /\\ y", concat ["\\", bx, ". ", bx, " /\\ ", fy]),
  ("!x. x /\\ y", concat ["!", bx, ". ", bx, " /\\ ", fy]),
  ("let x = p in x /\\ y",
   concat ["let ",bx, " = ", fp, " in ", bx, " /\\ ", fy]),
  ("let f x = x /\\ p in f x /\\ y",
   concat ["let ",bound "f", " ", bx, " = ", bx, " /\\ ", fp, " in ",
           bound "f", " ", fx, " /\\ ", fy])
]

open testutils
val test = tpp_expected
             |> Lib.with_flag (linewidth,!Globals.linewidth)
             |> unicode_off
             |> raw_backend
val _ = app test [
      {input = "if oless e1 e2 /\\ oless x y /\\ foobabbbbbbb\n\
               \then p /\\ q /\\ r /\\ ppppp xxxx yyyyy\n\
               \else if (e1 = e2) /\\ k1 <> k2\n\
               \then T else if (e1 = e2) /\\ (k1 = k2) /\\ oless t1 t2\n\
               \then T else F",
       testf = K ("Large COND 1"),
       output = "if oless e1 e2 /\\ oless x y /\\ foobabbbbbbb then\n\
                \  p /\\ q /\\ r /\\ ppppp xxxx yyyyy\n\
                \else if (e1 = e2) /\\ k1 <> k2 then T\n\
                \else if (e1 = e2) /\\ (k1 = k2) /\\ oless t1 t2 then T\n\
                \else F"},
      {input = "if oless e1 e2 /\\ oless x y /\\ foobabb\n\
               \then p /\\ q /\\ r /\\ ppppp xxxx\n\
               \else if (e1 = e2) /\\ k1 <> k2\n\
               \then T else if (e1 = e2) /\\ (k1 = k2) /\\ oless t1 t2\n\
               \then T else F",
       testf = K ("Large COND 2"),
       output = "if oless e1 e2 /\\ oless x y /\\ foobabb then\
                \ p /\\ q /\\ r /\\ ppppp xxxx\n\
                \else if (e1 = e2) /\\ k1 <> k2 then T\n\
                \else if (e1 = e2) /\\ (k1 = k2) /\\ oless t1 t2 then T\n\
                \else F"}
]

val _ = temp_add_rule { paren_style = NotEvenIfRand, fixity = Prefix 2200,
                        block_style = (AroundEachPhrase, (PP.CONSISTENT,0)),
                        pp_elements = [TOK "/"], term_name = "div" };
val _ = test {input = "f /x",
              testf = (fn s => "Prefix op without parens: "^s),
              output = "f /x"}

fun bfnprinter gs be sys (ppfns : term_pp_types.ppstream_funs) gravs depth t =
  let
    val (bvar, body) = dest_abs t
  in
    if aconv bvar body then #add_string ppfns "I"
    else if aconv body boolSyntax.T then #add_string ppfns "(K T)"
    else if aconv body boolSyntax.F then #add_string ppfns "(K F)"
    else if aconv body (mk_neg bvar) then #add_string ppfns "neg"
    else raise term_pp_types.UserPP_Failed
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed

val _ = temp_add_user_printer("boolfunction", ``v : bool -> bool``,
                              bfnprinter)

val _ = test {input = "\\x:bool. x",
              testf = (K "Boolean identity with special user printer"),
              output = "I"}
val _ = test {input = "\\x:'a. x",
              testf = (K "Non-boolean identity with special user printer"),
              output = "\\x. x"}
val _ = test {
      input = "\\x:bool. T",
      testf = (K "Constant T with type :bool -> bool w/special user printer"),
      output = "(K T)"
    }
val _ = test {
      input = "\\x:'a. T",
      testf = (K "Constant T with type :'a -> bool w/special user printer"),
      output = "\\x. T"
    }



(* test DiskThms *)
val _ = let
  val _ = tprint "Testing DiskThms"
  val filename = OS.FileSys.tmpName ()
  val _ = DiskThms.write_file filename [("AND_CLAUSES", boolTheory.AND_CLAUSES),
                                        ("OR_CLAUSES", boolTheory.OR_CLAUSES)]
  val readresult = DiskThms.read_file filename
  val ((nm1,th1), (nm2, th2)) =
      case readresult of
        [x,y] => (x,y)
      | _ => die "FAILED"
in
  nm1 = "AND_CLAUSES" andalso nm2 = "OR_CLAUSES" andalso
  aconv (th1 |> concl) (concl boolTheory.AND_CLAUSES) andalso
  aconv (th2 |> concl) (concl boolTheory.OR_CLAUSES) andalso
  (print "OK\n"; true) orelse
  die "FAILED"
end

val _ = let
  val _ = tprint "REWRITE with T (if this appears to hang it has failed)"
  val t = mk_disj(mk_var("p", bool),T)
  val (sgs,vfn) = REWRITE_TAC [TRUTH] ([], t)
in
  if null sgs andalso aconv (concl (vfn [])) t then print "OK\n"
  else die "FAILED"
end

val _ = let
  val _ = tprint "EVERY_CONJ_CONV"
  fun mkb s = mk_var(s, bool)
  val p = mkb "p"
  val q = mkb "q"
  val t = list_mk_conj [T, mk_var("p", bool), mk_var("q",bool)]
  val I = mk_abs(p, p)
  val I_thm = SYM (BETA_CONV (mk_comb(I,q)))
  fun I_CONV t = if aconv t T then ALL_CONV t
                 else REWR_CONV I_thm t
  val result = EVERY_CONJ_CONV I_CONV t
  val expected = mk_conj(mk_comb(I, p), mk_comb(I, q))
in
  if aconv (rhs (concl result)) expected then print "OK\n"
  else die "FAILED"
end

val _ = Process.exit (if List.all substtest tests then Process.success
                      else Process.failure)
