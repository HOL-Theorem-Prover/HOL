open HolKernel Parse boolTheory boolLib

open testutils
val _ = set_trace "Unicode" 0

val _ = tprint "Preterm free variables 1"
val _ = require (check_result null) (Preterm.ptfvs o Parse.Preterm) ‘\x. x’

val _ = tprint "Preterm free variables 2"
val _ = require (check_result null) (Preterm.ptfvs o Parse.Preterm) ‘\x:bool. x’

fun substtest (M, x, N, result) = let
  open testutils
in
  tprint("Testing ["^term_to_string M^"/"^term_to_string x^"] ("^
         term_to_string N^") = "^term_to_string result);
  require (check_result (aconv result)) (Term.subst[x |-> M]) N
end;

val x = mk_var("x", Type.alpha)
val xfun = mk_var("x", Type.alpha --> Type.alpha)
val y = mk_var("y", Type.alpha)
val Id = mk_abs(x,x)
val Idy = mk_abs(y,y)
val P = mk_var("P", Type.alpha --> Type.bool)

val _ = tprint "TG list_mk_forall bug (0)"
val _ = require_msg
          (check_result (aconv (List.foldr mk_abs (mk_comb(P,x)) [x,P])))
          term_to_string
          list_mk_abs ([x,P],mk_comb(P,x))
val _ = tprint "TG list_mk_forall bug (1)"
val _ = require_msg
          (check_result (aconv (List.foldr mk_forall (mk_comb(P,x)) [x,P])))
          term_to_string
          list_mk_forall ([x,P],mk_comb(P,x))
val _ = tprint "TG list_mk_forall bug (2)"
val _ = require_msg
          (check_result (aconv (List.foldr mk_forall (mk_comb(P,x)) [P,x])))
          term_to_string
          list_mk_forall ([P,x],mk_comb(P,x))


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
  if same_const (concl final_th) (mk_const("F", bool)) then die ""
  else OK()
end;

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
  if aconv (concl Falsity) F then die "" else die "Huh???"
end handle ExitOK => OK();

fun cleanup() = let
  fun rm s = FileSys.remove ("scratchTheory." ^ s)
      handle _ => ()
in
  app rm ["sml", "sig", "dat"]
end

exception InternalDie
fun test f x = f x orelse raise InternalDie
fun oldconstants_test() = let
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
  val _ = new_theory "foo"
  val defn1 = new_definition("c", mk_eq(mk_var("c", bool), boolSyntax.T))
  val _ = new_theory "foo"
  val defn2 = new_definition("c", mk_eq(mk_var("c", bool), boolSyntax.T))
  val c1 = lhs (concl defn1)
  val c2 = lhs (concl defn2)
  val _ = test (fn (c1, c2) => Term.compare(c1,c2) <> EQUAL) (c1, c2)
  val _ = test (not o uncurry aconv) (c1, c2)
in
  OK();
  cleanup()
end handle e => (cleanup(); raise e)

val _ = testutils.quietly oldconstants_test ()
    handle InternalDie => die "Internal test failed";

val _ = tprint "Testing functional-pretype 1 (pattern)"
val _ = require (check_result (fn _ => true)) Parse.Term `x <> y ==> x <> y`

val _ = tprint "Testing functional-pretype 2 (simple case)"
val _ = require (check_result (fn _ => true)) (quietly Parse.Term)
                `case x of T => F`

val _ = tprint "Testing functional-pretype 3 (ignored constraint)"
val quiet_parse = quietly (trace ("show_typecheck_errors", 0) Parse.Term)
val _ = shouldfail {testfn = quiet_parse, printresult = term_to_string,
                    printarg = (fn _ => ""),
                    checkexn = is_struct_HOL_ERR "Preterm"}
                   ‘(\x.x) : 'a -> 'b’;

val _ = tprint "Testing parsing of case expressions with function type"
val _ = require_msg
          (check_result (Lib.can (find_term (same_const boolSyntax.bool_case))))
          term_to_string
          Parse.Term
          ‘(case T of T => (\x. x) | F => (~)) y’;

val _ = tprint "Testing parsing of case expressions with leading bar"
val _ = require_msg
          (check_result (Lib.can (find_term (same_const boolSyntax.bool_case))))
          term_to_string
          (trace ("syntax_error", 0) Parse.Term)
          ‘case T of | T => F | F => T’;

val _ = tprint "Testing parsing of _ variables (1)"
val t = case Lib.total Parse.Term `case b of T => F | _ => T` of
          NONE => die ""
        | SOME _ => OK()
val _ = tprint "Testing parsing of _ variables (2)"
val t = case Lib.total Parse.Term `case b of T => F | _1 => T` of
          NONE => die ""
        | SOME _ => OK()
val _ = tprint "Testing independence of case branch vars"
val t = case Lib.total Parse.Term `v (case b of T => F | v => T)` of
          NONE => die ""
        | SOME _ => OK()

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
val num_ty = num_ty
val int_ty = let val () = new_type ("int", 0)
             in
               mk_thy_type{Thy = thy, Tyop = "int", Args = []}
             end
val _ =
    case Lib.total (VALID (HO_MATCH_MP_TAC th)) ([], goal) of
      SOME ([([],subgoal)],_) => if aconv subgoal expected then OK()
                                 else die ""
    | _ => die ""
end; (* local *)

val _ = app testutils.convtest [
  ("COND_CONV(1)", Conv.COND_CONV, “if b then (\x:'a. x) else (\y.y)”,
   “(\a:'a.a)”)
];

val _ = tprint "Testing type-specific Unicode overload 1"
val _ = set_trace "Unicode" 1
val _ = overload_on (UnicodeChars.delta, ``$! :(('a -> 'b)->bool)->bool``)
fun checkparse () = let
  val tm = Lib.with_flag (Globals.notify_on_tyvar_guess, false)
                         Parse.Term
                         `!x. P x`
  val randty =  type_of (rand tm)
in
  if Type.compare(randty, alpha --> bool) <> EQUAL then die ""
  else OK()
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
val _ = quietly new_type ("foo", 0)
val _ = type_abbrev("baz", ``:foo``) handle _ => die ""
val _ = OK()

val _ = tprint "Testing ability to p/print current type grammar"
val _ = require (check_result (fn _ => true)) type_grammar.prettyprint_grammar
                (type_grammar ())


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
  if s <> res then die "" else OK()
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
    PP.pp_to_string 70 (#1 (raw_backend print_from_grammars min_grammars))
                    |> unicode_off
  val s = pfn ty
in
val _ = if s = "('a -> 'b) "^ct()^"$option" then OK()
        else die s
end


val _ = app tpp ["(if P then q else r) s",
                 "(if P then q else r) s t",
                 "f ((if P then q else r) s t u)",
                 "let x = T in x /\\ y",
                 "let x = (let y = T in y /\\ F) in x \\/ z",
                 "(let x = T in \\y. x /\\ y) p",
                 "let x = p and y = x in x /\\ y",
                 "let x = T; y = F in x /\\ y",
                 "let x = T; y = F and z = T in x /\\ y \\/ z",
                 "f ($/\\ p)",
                 "(((p /\\ q) /\\ r) /\\ s) /\\ t",
                 "!x. P (x /\\ y)",
                 "P (!x. Q x)",
                 "\\x. ?y. P x y",
                 "P (\\x. ?y. Q x y)",
                 "(:'a)",
                 "$var$(\\172)"]

val _ = tpp "x = y"
val _ = Lib.with_flag (testutils.linewidth, 10) tpp "xxxxxx =\nyyyyyy"

val _ = temp_overload_on ("RM*", ``\x y. x /\ y``)
val _ = tpp "RM* p q"
val _ = clear_overloads_on "RM*"

val _ = add_rule {term_name = "=",
                  fixity = Infix(NONASSOC, 450),
                  block_style = (AroundSamePrec, (PP.CONSISTENT,0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,2)]}
val _ = Lib.with_flag (testutils.linewidth, 10) tpp "xxxxxx =\n  yyyyyy"
val _ = Lib.with_flag (testutils.linewidth, 30) tpp
                      "fffff verylongarg1\n\
                      \  verylongarg2 verylongarg3";
val _ = Lib.with_flag (testutils.linewidth, 30) tpp
                      "ffff longarg1\n\
                      \  (fff longarg2 longarg3\n\
                      \     longarg4) longarg5\n\
                      \  longarg6 longarg7";

val _ = print "** Tests with Unicode on PP.avoid_unicode both on\n"
val _ = let
  open testutils
  fun md f =
      raw_backend (trace ("Unicode", 1) (trace ("PP.avoid_unicode", 1) f))
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

val _ = print "** Tests with Unicode on\n"
val _ = let
  open testutils
  fun md f = raw_backend $ trace ("Unicode", 1) f
in
  app (md tpp) ["¬¬p", "¬p"]
end


val _ = print "** Tests with pp_dollar_escapes = 0.\n"
val _ = set_trace "pp_dollar_escapes" 0
val _ = app tpp ["(/\\)", "(if)"]
val _ = set_trace "pp_dollar_escapes" 1

val _ = quietly new_type ("foo", 2)
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
  if res = expected then OK()
  else die (testutils.clear ("  Expected >" ^ expected ^ "<; got >"^res^"<"))
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
  ("let f x = (x /\\ p) in f x /\\ y",
   concat ["let ",bound "f", " ", bx, " = (", bx, " /\\ ", fp, ") in ",
           bound "f", " ", fx, " /\\ ", fy]),
  ("!(x:'a)::p (x:'a). q x",
   concat ["!",bx,"::",fp, " ", fx,". ",free "q"," ",bx]),
  ("RES_FORALL (p (x:'a)) (\\x. RES_FORALL (p (x:'a)) (\\y. q x y))",
   concat ["!(",bx,"::",fp," ",fx,") (",bound "y","::",fp," ",bx,"). ",
           free "q", " ", bx, " ", bound "y"])
]

open testutils
val condprinter_test = tpp_expected
             |> Lib.with_flag (linewidth,!Globals.linewidth)
             |> unicode_off
             |> raw_backend
val test = condprinter_test
val condprinter_tests =
    [
      {input = "if oless e1 e2 /\\ oless x y /\\ foobabbbbbbb\n\
               \then p /\\ q /\\ r /\\ ppppp xxxx yyyyy\n\
               \else if (e1:'a) = e2 /\\ (k1:'a) <> k2\n\
               \then T else if e1 = e2 /\\ k1 = k2 /\\ oless t1 t2\n\
               \then T else F",
       testf = K ("Large COND 1"),
       output = "if oless e1 e2 /\\ oless x y /\\ foobabbbbbbb then\n\
                \  p /\\ q /\\ r /\\ ppppp xxxx yyyyy\n\
                \else if e1 = e2 /\\ k1 <> k2 then T\n\
                \else if e1 = e2 /\\ k1 = k2 /\\ oless t1 t2 then T\n\
                \else F"},
      {input = "if oless e1 e2 /\\ oless x y /\\ foobabb\n\
               \then p /\\ q /\\ r /\\ ppppp xxxx\n\
               \else if e1 = e2 /\\ k1 <> k2\n\
               \then T else if e1 = e2 /\\ k1 = k2 /\\ oless t1 t2\n\
               \then T else F",
       testf = K ("Large COND 2"),
       output = "if oless e1 e2 /\\ oless x y /\\ foobabb then\
                \ p /\\ q /\\ r /\\ ppppp xxxx\n\
                \else if e1 = e2 /\\ k1 <> k2 then T\n\
                \else if e1 = e2 /\\ k1 = k2 /\\ oless t1 t2 then T\n\
                \else F"},
      {input = "if really quite a long guard when looked at closely then\n\
               \  let quite_a_long_variable_name = (another_long_name \\/ x);\n\
               \      another_longish_name = (y \\/ z)\n\
               \  in\n\
               \      f x\n\
               \else\n\
               \  g y",
       testf = K "Large then-branch",
       output = "if really quite a long guard when looked at closely then\n\
                \  (let\n\
                \     quite_a_long_variable_name = (another_long_name \\/ x);\
              \\n     another_longish_name = (y \\/ z)\n\
                \   in\n\
                \     f x)\n\
                \else g y"},
      {input = "f\n\
               \  (if really quite a long guard when looked at closely then\n\
               \     a moderately complicated then_branch\n\
               \   else an else_branch)",
       testf = K "Large COND as rand",
       output = "f\n\
                \  (if really quite a long guard when looked at closely then\n\
                \     a moderately complicated then_branch\n\
                \   else an else_branch)"}
  ]
val _ = app condprinter_test condprinter_tests

val _ = let
  open testutils
  val _ = tprint (standard_tpp_message "|- p")
  val res = thm_to_string (ASSUME (mk_var("p", Type.bool)))
in
  if res = " [.] |- p" then OK() else die ""
end

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
    };



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
        | _ => raise InternalDie
in
  if nm1 = "AND_CLAUSES" andalso nm2 = "OR_CLAUSES" andalso
     aconv (th1 |> concl) (concl boolTheory.AND_CLAUSES) andalso
     aconv (th2 |> concl) (concl boolTheory.OR_CLAUSES)
  then
    OK()
  else die ""
end handle InternalDie => die ""

val _ = let
  val _ = tprint "REWRITE with T (if this appears to hang it has failed)"
  val t = mk_disj(mk_var("p", bool),T)
  val (sgs,vfn) = REWRITE_TAC [TRUTH] ([], t)
in
  if null sgs andalso aconv (concl (vfn [])) t then OK()
  else die ""
end;

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
  if aconv (rhs (concl result)) expected then OK()
  else die ""
end;

val _ = let
  fun B i = mk_var("x" ^ Int.toString i, bool)
  fun jump ti i = if i > ti then i - 1 else i
  fun gentest nm unit lmk c = let
    val expected = lmk(List.tabulate(3, B))
    fun test (ai,ti) =
      let
        fun mk i = if i = ai then mk_comb(mk_abs(B 0,B 0), B (jump ti i))
                   else if i = ti then mk_comb(mk_abs(B 1, B 1), unit)
                   else B (jump ti i)
        val t = lmk (List.tabulate(4, mk))
        val _ = tprint (nm ^ " (" ^ Int.toString ai ^ "," ^
                        Int.toString ti ^ ")")
        val res = QCONV (c (TRY_CONV BETA_CONV)) t |> concl |> rhs
    in
      if aconv expected res then OK()
      else die ("got " ^ term_to_string res)
    end
    fun row i = List.tabulate (4, fn j => (i,j))
    val pairs = List.tabulate (4, row) |> List.concat
                              |> filter (fn (i,j) => i <> j)
  in
    List.app test pairs
  end
in
  gentest "EVERY_CONJ_CONV" T list_mk_conj EVERY_CONJ_CONV ;
  gentest "EVERY_DISJ_CONV" F list_mk_disj EVERY_DISJ_CONV
end


val _ = tprint "Testing (foo THENL [...]) when foo solves"
val _ = require (check_result (fn _ => true))
                (ACCEPT_TAC TRUTH THENL [ACCEPT_TAC TRUTH]) ([], ``T``)

val _ = tprint "Testing save_thm rejecting names"
val badnames = ["::", "nil", "true", "false", "ref", "="]
fun test s = (save_thm(s, TRUTH); die ("Failed to reject: "^s))
             handle HOL_ERR _ => ()
val _ = List.app test badnames
val _ = OK()

val _ = let
  val _ = tprint "Testing VALIDATE (1)"
  val th' = Thm.mk_oracle_thm "Testing" ([], ``p' ==> q``) ;
  val th = Thm.mk_oracle_thm "Testing" ([], ``p ==> q``) ;
  val uth' = UNDISCH_ALL th' ;
  val uth = UNDISCH_ALL th ;

  val g = ([], ``p ==> q``) : goal ;
  val ([g'], _) = STRIP_TAC g ;
  val ([], _) = (FIRST (map (VALID o ACCEPT_TAC) [uth', uth])) g' ;
  val ([_], _) = (VALIDATE (FIRST (map ACCEPT_TAC [uth', uth]))) g' ;
  val true = (VALID (FIRST (map ACCEPT_TAC [uth', uth])) g' ; false)
    handle HOL_ERR _ => true ;
in OK()
end handle _ => die ""

fun goal_equal ((asms1, g1), (asms2, g2)) =
  ListPair.allEq (fn p => Term.compare p = EQUAL) (asms1,asms2) andalso
  aconv g1 g2

val _ = let
  val _ = tprint "Testing VALIDATE (2)"
  val g = ([], ``(p ==> q) ==> r``) : goal
  val tac = STRIP_TAC THEN VALIDATE (POP_ASSUM (ASSUME_TAC o UNDISCH))
  val (ngs, vf) = VALID tac g

  val tac1 = (VALIDATE (ASSUME_TAC (ASSUME ``x /\ y``)))
  val tac2 = (SUBGOAL_THEN ``x /\ y`` ASSUME_TAC )

  val (ngs1, _) = VALID tac1 g
  val (ngs2, _) = VALID tac2 g
in
  if ListPair.allEq goal_equal (ngs1, ngs2) then OK()
  else die "final equality"
end handle _ => die ""

val _ = let
  val _ = tprint "Testing structural list-tactics"
  val tac = REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THEN_LT
    EVERY_LT [ (ROTATE_LT 2),
      (SPLIT_LT 2 (REVERSE_LT, ROTATE_LT 1)),
      (HEADGOAL (POP_ASSUM ACCEPT_TAC)),
      (REPEAT_LT (ALLGOALS (POP_ASSUM (fn _ => ALL_TAC))
          THEN_LT HEADGOAL (POP_ASSUM ACCEPT_TAC))) ] ;
  val th = prove (``a ==> b ==> c ==> d ==> a /\ b /\ c /\ d``, tac) ;
in if null (hyp th) then OK() else die ""
end handle _ => die ""

val _ = let
  val _ = tprint "Testing USE_SG_THEN"
  val tac = REPEAT DISCH_TAC THEN CONJ_TAC THEN_LT USE_SG_THEN ASSUME_TAC 1 2
    THENL [POP_ASSUM MATCH_MP_TAC THEN CONJ_TAC, DISJ1_TAC]
    THEN (FIRST_ASSUM ACCEPT_TAC)
  val th = prove (``p ==> q ==> (p /\ q ==> r) ==> r /\ (r \/ s)``, tac) ;
in if null (hyp th) then OK() else die ""
end handle _ => die ""

val _ = let
  val _ = tprint "Testing USE_SG_THEN and VALIDATE_LT"
  val tac = CONJ_TAC THEN REPEAT DISCH_TAC
      THEN_LT EVERY_LT [VALIDATE_LT (USE_SG_THEN ACCEPT_TAC 1 2),
        NTH_GOAL (REPEAT STRIP_TAC) 1 ]
      THEN (POP_ASSUM MATCH_MP_TAC)
      THEN_LT NTH_GOAL CONJ_TAC 2
      THEN (FIRST_ASSUM ACCEPT_TAC)
  val g = ``(p ==> q ==> (p /\ q ==> r) ==> r) /\
    (p ==> q ==> (p ==> r) ==> r)``
  val th = prove (g, tac) ;
in if null (hyp th) then OK() else die ""
end handle _ => die ""

val _ = let
  val _ = tprint "Removing type abbreviation"
  val _ = quietly temp_type_abbrev_pp ("foo", ``:'a -> bool``)
  val s1 = type_to_string ``:bool -> bool``
  val _ = s1 = ":bool foo" orelse raise InternalDie
  val _ = temp_remove_type_abbrev "foo"
  val s2 = type_to_string ``:bool -> bool``
in
  if s2 = ":bool -> bool" then OK() else die ""
end handle InternalDie => die ""

fun nc (s,ty) =
  (quietly new_constant(s,ty); prim_mk_const{Name = s, Thy = current_theory()})

val _ = let
  val _ = tprint "irule 1 (basic match-mp)"
  val P = nc("P", alpha --> beta --> bool)
  val Q = nc("Q", ``:'d -> 'b -> 'c -> bool``)
  val R = nc("R", beta --> mk_vartype "'e" --> bool)
  val f = nc("f", ``:'c -> 'e``)
  val th = mk_thm([],
    ``!x u. ^P u x ==> !y. ^Q w x y ==> ^R x (^f y)``)
  val g = ([] : term list, ``^R a (^f b) : bool``)
  val exsg1 = ``?u. ^P u a`` and exsg2 = ``?w. ^Q w a b``
  val (sgs, vf) = irule th g
  val verdict =
      case sgs of
          [([], sg)] => let val (sg1,sg2) = dest_conj sg
                        in
                          aconv sg1 exsg1 andalso aconv sg2 exsg2
                        end
        | _ => false
in
  if verdict then OK() else die ""
end

val _ = let
  val _ = tprint "irule 2 (shared existential)"
  val g = ([]: term list, ``a:'a = b``)
  val expected = ``?y:'a. (a = y) /\ (y = b)``
  val (sgs, vf) = irule EQ_TRANS g
in
  case sgs of
      [([], sg)] => if aconv sg expected then OK() else die ""
    | _ => die ""
end

val _ = let
  val _ = tprint "irule 3 (thm from goal)"
  val P = nc("P", ``:'a -> bool``)
  val Q = nc("Q", ``:'a -> bool``)
  val g = ([``!x. ^P x ==> ^Q x``], ``^Q (b:'a)``)
  val (sgs, vf) = POP_ASSUM irule g
  val rth = vf (map mk_thm sgs)
  val _ = aconv (concl rth) (#2 g) andalso length (hyp rth) = 1 andalso
          aconv (hd (hyp rth)) (hd (#1 g)) orelse raise InternalDie
in
  case sgs of
      [([], sg)] => if aconv sg ``^P (b:'a)`` then OK()
                    else die ""
    | _ => die ""
end handle InternalDie => die ""

val _ = let
  val _ = tprint "irule 4 (thm from goal, extra vars)"
  val g = ([``!x:'a y:'a. PP x y ==> QQ y (f y:'a)``],
           ``(QQ:'a -> 'a -> bool) a (f a)``)
  val (sgs, vf) = POP_ASSUM irule g
  val rth = vf (map mk_thm sgs)
in
  case sgs of
      [([], sg)] => if aconv sg ``?x:'a. PP x (a:'a)`` then OK()
                    else die ""
    | _ => die ""
end

val _ = hide "P"
val _ = hide "f"
val _ = hide "c"

val _ = let
  open testutils
  val _ = tprint "irule 5 (as match_accept_tac)"
  val g = ``(!x:'a. P x) ==> P a``
in
  require (check_result (aconv g o concl))
          (fn g => prove(g, DISCH_THEN irule))
          g
end

val _ = let
  val _ = tprint "irule 6 (JD)"
  val _ = nc ("IMAGE", ``:('a -> 'b) -> ('a -> bool) -> ('b -> bool)``)
  val tm = ``P x /\ U u ==> T' w ==> S' u w /\ V v ==> IMAGE f s x``
  val thm = mk_thm ([], tm)
  val g = ``IMAGE a b c``
  val (sgs, vf) = irule thm ([], g)
  val r_thm = vf (map mk_thm sgs)
in
  if aconv (concl r_thm) g then OK() else die ""
end

val _ = let
  val _ = tprint "irule 7 (JD)"
  val tm = ``!(f:'a -> 'b) s x u w v.
               P x /\ U u ==> T' w ==> S' u w /\ V v ==> IMAGE f s x``
  val thm = ASSUME tm
  val g = ``IMAGE (a:'a -> 'b) b c``
  val (sgs, vf) = irule thm ([], g)
  val r_thm = vf (map mk_thm sgs)
in
  if aconv (concl r_thm) g then OK() else die ""
end

fun checktactic sgsP rP tac_result =
    case tac_result of
        Exn.Res (sgs, vf) => sgsP sgs andalso
                             (case total vf (map mk_thm sgs) of
                                  NONE => false
                                | SOME th => rP th)
      | Exn.Exn e => false

fun pp_goal (asl,w) =
    let open HOLPP
    in
      HOLPP.block CONSISTENT 2 [
        HOLPP.block INCONSISTENT 0 (
          pr_list pp_term [add_string ",", add_break(1,0)] asl
        ),
        add_string " ?-",
        add_break(1,0),
        pp_term w
      ]
    end

fun pp_sgs gl =
    let open HOLPP in block CONSISTENT 0 (pr_list pp_goal [NL, NL] gl)
    end


fun print_tacresult (sgs, _) =
    PP.pp_to_string 70 pp_sgs sgs

val _ = let
  val _ = tprint "irule - negated conclusion"
  val tm = “!x:bool y:bool. P x /\ ~R x y ==> ~Q x”
  val thm = ASSUME tm
  val g = “~Q (z:bool): bool”
in
  require_msg (checktactic (fn _ => true) (fn th => concl th ~~ g))
              print_tacresult
              (irule thm)
              ([], g)
end

val _ = hide "Q"
val _ = hide "P"

fun pp_goal (asl,g) =
    PP.block PP.CONSISTENT 1 [
      PP.add_string "([",
      PP.block PP.INCONSISTENT 1 (
        PP.pr_list pp_term [PP.add_string ",", PP.add_break(1,0)] asl
      ),
      PP.add_string "],", PP.add_break (1,0),
      pp_term g, PP.add_string ")"
    ]

fun pp_goals gs = PP.block PP.INCONSISTENT 1 (
      PP.add_string "[" ::
      PP.pr_list pp_goal [PP.add_string ",", PP.add_break (1,0)] gs @
      [PP.add_string "]"]
    )

val _ = let
  open mp_then
  val _ = tprint "mp_then + goal_assum 1"
  val asl = [``P (x:'a):bool``, ``R (ARB:'b) (y:'a):bool``]
  val g = (asl, ``?x:'a y:'b. Q x (f y : 'c) /\ R y x``)
  val (res, _) = goal_assum (first_assum o mp_then Any mp_tac) g
  val expected = ``Q (y:'a) (f (ARB:'b) : 'c) : bool``
in
  case res of
      [(asl',g')] =>
      (case Lib.list_compare Term.compare (asl,asl') of
           EQUAL => if aconv expected g' then OK()
                    else die ("Got "^term_to_string g'^
                              "; expected "^term_to_string expected)
         | _ => die ("Got back changed asm list: " ^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals ("^
                Int.toString (length res)^")")
end

val _ = hide "f"
val _ = hide "R"

val _ = let
  val _ = tprint "drule 1"
  val asl = [``P (c:ind):bool``, ``!x:ind. P x ==> ?y:'a. Q x y``]
  val g = (asl, ``?a:ind (b:'a). Q a b``)
  val (res, _) = first_assum drule g
  val expectedg = ``(?y:'a. Q (c:ind) y) ==> ?a b. Q a b``
in
  case res of
      [(asl', g')] =>
      (case Lib.list_compare Term.compare (asl,asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back changed asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals (" ^
                Int.toString (length res))
end;

val _ = let
  val _ = tprint "drule 2"
  val _ = new_type("list", 1)
  val _ = new_constant ("LENGTH", ``:'a list -> num``)
  val _ = new_constant ("zero", ``:num``)
  val _ = new_constant ("some_n", ``:num``)
  val th = mk_thm([], ``!x l:'a list. (<) x (LENGTH l) ==> (<) x some_n``)
  val asl = [``(<) v (LENGTH (m:ind list))``]
  val g = (asl, ``?a:ind (b:'a). Q a b``)
  val (res, _) = drule th g
  val expectedg = ``(<) v some_n ==> ?a:ind b:'a. Q a b``
in
  case res of
      [(asl', g')] =>
      (case Lib.list_compare Term.compare (asl,asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back changed asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals (" ^
                Int.toString (length res))
end;

val _ = let
  val _ = tprint "drule 3"
  val asl = [``~p ==> q``, ``~p``]
  val g = (asl, ``r:bool``)
  val (res, _) = pop_assum drule g
  val expectedg = ``q ==> r``
in
  case res of
      [(asl', g')] =>
      (case Lib.list_compare Term.compare ([``~p``], asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back changed asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals (" ^
                Int.toString (length res))
end;

val _ = let
  open mp_then
  val _ = tprint "mp_then (concl) 1"
  val asl = [``p ==> q``, ``~q``]
  val g = (asl, ``r:bool``)
  val (res, _) = pop_assum (first_assum o mp_then Concl mp_tac) g
  val expectedg = ``(p ==> F) ==> r``
in
  case res of
      [(asl', g')] =>
      (case Lib.list_compare Term.compare ([``~q``], asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back changed asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals (" ^
                Int.toString (length res))
end;

val _ = let
  open mp_then
  val _ = tprint "mp_then (concl) 2"
  val asl = [``p ==> ~q``, ``q:bool``]
  val g = (asl, ``r:bool``)
  val eres = Exn.capture (#1 o pop_assum (first_assum o mp_then Concl mp_tac)) g
  val expectedg = ``(p ==> F) ==> r``
in
  case eres of
      Exn.Res [(asl', g')] =>
      (case Lib.list_compare Term.compare ([``q:bool``], asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back changed asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | Exn.Res res => die ("Tactic returned wrong number of sub-goals (" ^
                          Int.toString (length res))
    | Exn.Exn e => die ("Unexpected exception: " ^ General.exnMessage e)
end;


val _ = let
  open mp_then
  val _ = tprint "mp_then (pat) 1"
  val asl = [``P (x:'a) /\ ~p /\ r ==> ~q``, ``~p:bool``, ``r:bool``]
  val g = (asl, ``r:bool``)
  val (res, _) = pop_assum (first_assum o mp_then (Pat `$~`) mp_tac) g
  val expectedg = ``(P(x:'a) /\ r ==> ~q) ==> r``
in
  case res of
      [(asl', g')] =>
      (case Lib.list_compare Term.compare ([``~p``, ``r:bool``], asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back changed asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals (" ^
                Int.toString (length res))
end;


val _ = let
  open mp_then
  val _ = tprint "mp_then (pat) 2"
  val asl = [``!x. P (x:'a) /\ ~p /\ r ==> ~q``, ``P(c:'a):bool``, ``r:bool``]
  val g = (asl, ``r:bool``)
  val (res, _) =
      pop_assum (first_assum o mp_then (Pat `P (x:'a) : bool`) mp_tac) g
  val expectedg = ``(~p /\ r ==> ~q) ==> r``
in
  case res of
      [(asl', g')] =>
      (case Lib.list_compare Term.compare ([“P(c:'a):bool”, “r:bool”], asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back changed asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals (" ^
                Int.toString (length res))
end;

val _ = let
  open mp_then
  val _ = tprint "mp_then (pat) 3"
  val _ = quietly new_type("list", 1)
  val _ = quietly new_type("ti", 0)
  val _ = hide "foo"
  val _ = nc("EVERY", ``:('a -> bool) -> 'a list -> bool``)
  val asl = [``EVERY (x:'a -> bool) ls``,
             ``!x:ti y. foo x y /\ EVERY y (ls:'a list) ==> gg x``,
             ``foo (a:ti) (x:'a -> bool):bool``, ``bar (x:'a -> bool):bool``]
  val g = (List.rev asl, ``gg (a:ti):bool``)
  val (res, _) =
      first_x_assum (first_assum o mp_then (Pat `EVERY`) mp_tac) g
  val expectedg = ``(!x':ti. foo x' (x:'a -> bool) ==> gg x') ==> gg a``
  val expectedasl = [``bar (x:'a -> bool):bool``,
                     ``foo (a:ti) (x:'a -> bool):bool``,
                     ``EVERY (x:'a -> bool) ls``]
in
  case res of
      [(asl', g')] =>
      (case Lib.list_compare Term.compare (expectedasl, asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back changed asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals (" ^
                Int.toString (length res))
end;

val _ = let
  open mp_then Portable
  val _ = tprint "mp_then (backtracking pat)"
  val gh567_1_def = new_definition("gh567_1_def", “gh567_1 p <=> p /\ F”)
  val gh567_2_def = new_definition("gh567_2_def", “gh567_2 p <=> p /\ T”)
  val _ = temp_overload_on ("gh567", “gh567_1”)
  val _ = temp_overload_on ("gh567", “gh567_2”)
  val tm1 = gh567_1_def |> SPEC_ALL |> concl |> lhs |> rator
  val asl = [“!b. ^tm1 b ==> b”, “^tm1 F”]
  val g = boolSyntax.F
  val tac = first_x_assum (first_x_assum o mp_then (Pat ‘gh567’) assume_tac)
in
  case verdict tac (fn _ => ()) (asl,g) of
      FAIL ((), e) => die ("Got exception: " ^ General.exnMessage e)
    | PASS (sgs, _) =>
      if list_eq (pair_eq (list_eq aconv) aconv) sgs [([F], F)] then
        OK()
      else die ("Wrong subgoals")
end


val _ = let
  val _ = tprint "drule_all 1"
  val asl = [``!x:ind. P x /\ R x ==> ?y:'a. Q x y``,
             ``P (c:ind):bool``, ``R (d:ind):bool``,
             ``P (d:ind):bool``]
  val g = (asl, ``?a:ind (b:'a). Q a b``)
  val (res, _) = first_assum drule_all g
  val expectedg = ``(?y:'a. Q (d:ind) y) ==> ?a b. Q a b``
in
  case res of
      [(asl', g')] =>
      (case Lib.list_compare Term.compare (asl,asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back changed asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals (" ^
                Int.toString (length res))
end;

val _ = let
  val _ = tprint "drule_all 2 (ith implies F)"
  val asl = [“Q (a:ind) (b:'b):bool”,  “P (a:ind):bool”, “R T : bool”,
             “!x:ind. P x ==> !c:'b. Q x c ==> F”]
  val g = (asl, “p /\ q”)
  val eres = Exn.capture (#1 o VALID (first_x_assum drule_all)) g
  val (asl', _) = front_last asl
  val expected = (asl', “F ==> p /\ q”)
in
  case eres of
      Exn.Res res =>
      if ListPair.allEq goal_equal ([expected], res) then OK()
      else die ("Unexpected result:\n  " ^
                PP.pp_to_string 70
                                (fn r => PP.block PP.CONSISTENT 2 [pp_goals r])
                                res
               )
    | Exn.Exn e => die ("Unexpected exception: " ^ General.exnMessage e)
end


val _ = let
  val _ = tprint "dxrule_all 1"
  val imp = ``!x:ind. P x /\ R x ==> ?y:'a. Q x y``
  val asl = [imp, ``P (c:ind):bool``, ``R (d:ind):bool``, ``P (d:ind):bool``]
  val g = (asl, ``?a:ind (b:'a). Q a b``)
  val (res, _) = first_assum dxrule_all g
  val expectedg = ``(?y:'a. Q (d:ind) y) ==> ?a b. Q a b``
  val expected_asl = [imp, ``P (c:ind):bool``]
in
  case res of
      [(asl', g')] =>
      (case Lib.list_compare Term.compare (expected_asl,asl') of
           EQUAL => if aconv g' expectedg then OK()
                    else die ("Got " ^ term_to_string g'^
                              "; expected " ^ term_to_string expectedg)
         | _ => die ("Got back wrong asm list: "^
                     String.concatWith ", " (map term_to_string asl')))
    | _ => die ("Tactic returned wrong number of sub-goals (" ^
                Int.toString (length res))
end;


fun dolvtests(modname,empty,insert,match) = let
  val n = List.foldl (fn ((k,v),acc) => insert (acc,k,v)) empty
                     [(([],``R x y:bool``), 1),
                      (([], ``!s:'a. f s = T``), 2),
                      (([``f:'a -> bool``], ``!s:'a. f s = T``), 3),
                      (([``f:'a -> bool``], ``f (s:'a) = T``), 4)
                     ]
  fun test (nm, pat, expected) =
    let
      open testutils
      val _ = tprint (modname ^ ": " ^ nm)
    in
      require (check_result (equal expected))
              (fn pat => List.map snd (match (n,pat)))
              pat;
      ()
    end
in
  List.app test [("exact", ``f x y : bool``, [1]),
                 ("one extra", ``f a x y : bool``, [1]),
                 ("lvar 1", ``g (z:'a) = T``, [1]),
                 ("lvar 2", ``f (z:'a) = T``, [4,1]),
                 ("quant eq 1", ``!z:'a. g z = T``, [2]),
                 ("quant lv match", ``!z:'a. f z = T``, [3,2])
                ]
end

val _ = dolvtests("LVTermNet", LVTermNet.empty, LVTermNet.insert,
                  LVTermNet.match)
val _ = dolvtests("LVTermNetFunctor",
                  LVTermNetFunctorApplied.PrintMap.empty,
                  LVTermNetFunctorApplied.PrintMap.insert,
                  LVTermNetFunctorApplied.PrintMap.match)

(* set up overloading situation with < and + overloaded to num and int *)
val thy = current_theory()
val ilt = (new_constant("ilt", int_ty --> (int_ty --> bool));
           mk_thy_const{Thy = thy, Name = "ilt",
                        Ty = int_ty --> (int_ty --> bool)})
val _ = overload_on("<", ilt)

val _ = set_fixity "+" (Infixl 500)
val _ = set_fixity "<" (Infix(NONASSOC, 450))

val nplus = (new_constant("nplus", num_ty --> (num_ty --> num_ty));
             mk_thy_const{Thy = thy, Name = "nplus",
                          Ty = num_ty --> (num_ty --> num_ty)})
val _ = overload_on("+", nplus)

val iplus = (new_constant("iplus", int_ty --> (int_ty --> int_ty));
             mk_thy_const{Thy = thy, Name = "iplus",
                          Ty = int_ty --> (int_ty --> int_ty)})
val _ = overload_on("+", iplus)

val _ = tprint "Checking error message on x + y < T parse (w/ints around)"
val ptie = TermParse.preterm (term_grammar()) (type_grammar()) `x + y < T`
val res = let
  open errormonad Preterm
  infix >~ >>
  val op >~ = errormonad.bind
  val checked =
      ptie >~ (fn pt => typecheck_phase1 NONE pt >> overloading_resolution pt)
in
  case checked Pretype.Env.empty of
      Error (OvlNoType(s,_), _) => if s = "<" orelse s = "+" then OK()
                                   else die ""
    | _ => die ""
end

val _ = List.app (ignore o substtest) tests

val _ = print "Testing cond-printer after set_grammar_ancestry\n"
val _ = set_trace "PP.avoid_unicode" 1
val _ = set_grammar_ancestry ["bool"]
val _ = app condprinter_test condprinter_tests

val _ = let
  open Exn
  fun badtac (asl,g) = ([], fn [] => ASSUME ``p:bool`` | _ => raise Fail "")
  val vtac = VALID badtac
  fun checkmsg P f (os, ofn, m) = os = "Tactical" andalso ofn = f andalso P m
  fun checkv P = checkmsg P "VALID"
  fun checkvl P = checkmsg P "VALID_LT"
  val _ = tprint "VALID-checking (normal)"
  val _ = require is_result vtac ([``p:bool``], ``p:bool``)
  val _ = tprint "VALID-checking (bad concl)"
  val expectedmsg1 = "Invalid tactic: theorem has wrong conclusion p"
  val _ = require (check_HOL_ERR (checkv (equal expectedmsg1))) vtac
                  ([``p:bool``, ``q:bool``], ``P:bool``)
  val _ = tprint "VALID-checking (bad hyp)"
  val expectedmsg2 = "Invalid tactic: theorem has bad hypothesis p"
  val _ = require (check_HOL_ERR (checkv (equal expectedmsg2))) vtac
                  ([], ``p:bool``)
in
  ()
end

val _ = let
  val _ = tprint "test of apropos_in, find_in"
  val str = "THM"
  val tm = prim_mk_const{Thy = "bool", Name = "/\\"}
  val find1 = find str
  val list1 = apropos_in tm find1
  val apropos2 = apropos tm
  val list2 = find_in str apropos2
  val true = length list1 = length list2
  (* next test may be implementation dependent *)
  val true = map #1 list1 = map #1 list2
in
  OK()
end handle _ => die "FAILED"

val _ = shouldfail {checkexn = is_struct_HOL_ERR "Parse",
                    printarg = (fn s => "Type parser fails on bool'"),
                    printresult = with_flag (show_types, true) term_to_string,
                    testfn = Parse.Term o single o QUOTE}
                   "!b:bool'. p /\\ b"

(* ?p p. p  with inner variable binding, should swap to ?p q. p
   or something alpha equivalent to that *)
val _ = let
  val v = mk_var("p", bool)
  val u = mk_var("q", bool)
  val t = mk_exists(v, mk_exists(v, v))
  val expected = mk_exists(v, mk_exists (u, v))
in
  convtest("SWAP_EXISTS_CONV with vacuous binding of identical names",
           SWAP_EXISTS_CONV,
           t, expected)
end
