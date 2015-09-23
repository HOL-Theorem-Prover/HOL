open HolKernel boolLib bossLib lcsymtacs finite_mapSyntax
open ASCIInumbersTheory simpleSexpTheory simpleSexpPEGTheory pegexecTheory

val _ = new_theory"simpleSexpParse"

val parse_sexp_def = Define`
  parse_sexp s =
    OPTION_BIND (pegparse sexpPEG s)
      (λ(rest,sx). OPTION_IGNORE_BIND (OPTION_GUARD (rest="")) (SOME sx))`;

(* TODO: all this is taken from cakeml/parsing, and should be made more generic *)

val FDOM_sexpPEG_rules = save_thm("FDOM_sexpPEG_rules",
  ``FDOM sexpPEG.rules``
  |> SIMP_CONV(srw_ss())[sexpPEG_def,finite_mapTheory.FUPDATE_LIST_THM])

val spec0 =
  peg_nt_thm |> Q.GEN`G` |> Q.ISPEC`sexpPEG`
  |> SIMP_RULE (srw_ss()) [FDOM_sexpPEG_rules]
  |> Q.GEN`n`

val mkNT = ``mkNT``

val distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:sexpNT``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  recurse ntlist
end

val rules_t = ``sexpPEG.rules``
fun ty2frag ty = let
  open simpLib
  val {convs,rewrs} = TypeBase.simpls_of ty
in
  merge_ss (rewrites rewrs :: map conv_ss convs)
end
(* can't use srw_ss() as it will attack the bodies of the rules,
   and in particular, will destroy predicates from tok
   constructors of the form
        do ... od = SOME ()
   which matches optionTheory.OPTION_BIND_EQUALS_OPTION, putting
   an existential into our rewrite thereby *)
val rules = SIMP_CONV (bool_ss ++ ty2frag ``:(α,β,γ)peg``)
                      [sexpPEG_def, combinTheory.K_DEF,
                       finite_mapTheory.FUPDATE_LIST_THM] rules_t

val _ = print "Calculating application of sexpPEG rules\n"
val sexppeg_rules_applied = let
  val app0 = finite_mapSyntax.fapply_t
  val theta =
      Type.match_type (type_of app0 |> dom_rng |> #1) (type_of rules_t)
  val app = inst theta app0
  val app_rules = AP_TERM app rules
  val sset = bool_ss ++ ty2frag ``:'a + 'b`` ++ ty2frag ``:sexpNT``
  fun mkrule t =
      AP_THM app_rules ``mkNT ^t``
             |> SIMP_RULE sset
                  [finite_mapTheory.FAPPLY_FUPDATE_THM]
  val ths = TypeBase.constructors_of ``:sexpNT`` |> map mkrule
in
    save_thm("sexppeg_rules_applied", LIST_CONJ ths);
    ths
end

val sexpPEG_exec_thm = save_thm(
  "sexpPEG_exec_thm",
  TypeBase.constructors_of ``:sexpNT``
    |> map (fn t => ISPEC (mk_comb(mkNT, t)) spec0)
    |> map (SIMP_RULE bool_ss (sexppeg_rules_applied @ distinct_ths @
                               [sumTheory.INL_11]))
    |> LIST_CONJ)
val _ = computeLib.add_persistent_funs ["sexpPEG_exec_thm"]
(* -- *)

val escape_string_def = Define`
  escape_string s =
    case s of
    | "" => ""
    | #"\\"::s => "\\\\"++(escape_string s)
    | #"\""::s => "\\\""++(escape_string s)
    | c::s => c::(escape_string s)`;

val print_space_separated_def = Define`
  (print_space_separated [] = "") ∧
  (print_space_separated [x] = x) ∧
  (print_space_separated (x::xs) = x ++ " " ++ print_space_separated xs)`;

val print_sexp_def = tDefine"print_sexp"`
  (print_sexp (SX_SYM s) = s) ∧
  (print_sexp (SX_NUM n) = toString n) ∧
  (print_sexp (SX_STR s) = "\"" ++ escape_string s ++ "\"") ∧
  (print_sexp s =
   case strip_sxcons s of
   | NONE => (case s of SX_CONS a d => "(" ++ print_sexp a ++ "." ++ print_sexp d ++")" | _ => "")
   | SOME [q; s] => if q = SX_SYM "quote" then "'" ++ print_sexp s
                    else "(" ++ print_sexp q ++ " " ++ print_sexp s ++ ")"
   | SOME ls => "(" ++ print_space_separated (MAP print_sexp ls) ++ ")")`
  (WF_REL_TAC`measure sexp_size` >> rw[] >> simp[sexp_size_def] >>
   fs[Once strip_sxcons_def] >> rw[] >> simp[sexp_size_def] >>
   PROVE_TAC[sxMEM_def,sxMEM_sizelt,arithmeticTheory.LESS_IMP_LESS_ADD,listTheory.MEM,
             DECIDE``(a:num) + (b + c) = b + (a + c)``]);

val _ = export_theory()
