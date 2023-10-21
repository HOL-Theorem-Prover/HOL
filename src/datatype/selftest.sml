(* tests for Hol_datatype *)

open HolKernel Parse
open testutils

val _ = Feedback.set_trace "Theory.save_thm_reporting" 0;
val _ = Feedback.set_trace "Theory.allow_rebinds" 1;

fun Hol_datatype q = let
  open TextIO Feedback
  val _ = Datatype.Hol_datatype q
      handle e => (output(stdErr, "Exception raised: "^exn_to_string e);
                   Process.exit Process.failure)
in
  ()
end

val Datatype = Datatype.Datatype

fun primrec_test ty = let
  val rcd = {nchotomy = TypeBase.nchotomy_of ty,
             case_def = TypeBase.case_def_of ty}
  open Prim_rec
in
  (prove_case_elim_thm rcd, prove_case_rand_thm rcd)
end

val _ = Hol_datatype `type1 = one_constructor`

val _ = let
  val _ = tprint "type_to_string immediately after type defn"
  val s = prim_mk_const{Thy = "scratch", Name = "one_constructor"}
                       |> type_of |> Parse.type_to_string
in
  if s = ":type1" then OK()
  else die ("\nFAILED: got \"" ^ String.toString s ^ "\"; not \":type1\"")
end


val _ = Hol_datatype `type2 = ##`;
val _ = Hol_datatype `type3 = /\`;
val _ = Hol_datatype `type4 = /\ | \/ | feh`;
val _ = Hol_datatype `type5 = foo of num | bar of 'a`;

val _ = map primrec_test [``:type1``, ``:type4``, ``:'a type5``]

val _ = Hol_datatype `foo = NIL | CONS of 'a => foo`;
val _ = Hol_datatype `list = NIL | :: of 'a => list`;
val _ = Hol_datatype `void = Void`;
val _ = Hol_datatype `pair = CONST of 'a#'b`;
val _ = Hol_datatype `onetest = OOOO of one`;
val _ = Hol_datatype `tri = Hi | Lo | Fl`;
val _ = Hol_datatype `iso = ISO of 'a`;
val _ = Hol_datatype `ty = C1 of 'a
          | C2
          | C3 of 'a => 'b => ty
          | C4 of ty => 'c => ty => 'a => 'b
          | C5 of ty => ty`;
val _ = primrec_test ``:('a,'b,'c)ty``
val _ = Hol_datatype `bintree = LEAF of 'a | TREE of bintree => bintree`;
val _ = Hol_datatype `typ = C of one => (one#one)
                      => (one -> one -> 'a list)
                      => ('a,one#one,'a list) ty`;
val _ = primrec_test ``:'a typ``
val _ = Hol_datatype `Typ = D of one # (one#one)
                      # (one -> one -> 'a list)
                      # ('a, one#one, 'a list) ty`;
val _ = primrec_test ``:'a Typ``
val _ = Hol_datatype`ftyp = ftypC1 of num => (num -> num) => ftyp
                          | ftypC2 of bool => (num -> bool)`;
val _ = primrec_test ``:ftyp``

val _ = Hol_datatype `
       var = V of num ;

     atexp = var_exp of var
           | let_exp of dec => exp ;

       exp = aexp    of atexp
           | app_exp of exp => atexp
           | fn_exp  of match ;

     match = match  of rule
           | matchl of rule => match ;

      rule = rule of pat => exp ;

       dec = val_dec   of valbind
           | local_dec of dec => dec
           | seq_dec   of dec => dec ;

   valbind = bind  of pat => exp
           | bindl of pat => exp => valbind
           | rec_bind of valbind ;

       pat = wild_pat
           | var_pat of var`;

val state = Type`:ind->bool`;
val nexp  = Type`:^state -> ind`;
val bexp  = Type`:^state -> bool`;

val _ = Hol_datatype `comm = skip
            | :=    of bool list => ^nexp
            | ;;    of comm => comm
            | if    of ^bexp => comm => comm
            | while of ^bexp => comm`;

val _ = Hol_datatype
          `ascii = ASCII of bool=>bool=>bool=>bool=>bool=>bool=>bool=>bool`;

val _ = Hol_datatype`
          small_record = <| fld1 : num -> bool ; fld2 : num |>
`;

val _ = Hol_datatype`squish_record = <|fld1:bool|>`
val _ = Hol_datatype`poly_squish_record = <|fld1:'a->'b|>`
val _ = Datatype.Datatype`parentest1 = C (('a,'b)fun)`

val _ = tprint "Parse polymorphic record literal"
val r = with_flag (Globals.guessing_tyvars, false) Parse.Term
                  `<| fld1 := SUC |>`
val rnd = repeat rand r
val fupd_t = repeat rator r
val (args, _) = strip_fun (type_of fupd_t)
val fty = hd args
val (d,r) = dom_rng fty
val _ = if type_of rnd = ``:(num, num)poly_squish_record`` andalso
           Type.compare(d,r) = EQUAL
        then OK()
        else die "FAILED!"
val _ = tprint "TypeBase.mk_record on polymorphic record"
val _ =
    case Lib.total TypeBase.mk_record
                   (``:(num,num)poly_squish_record``, [("fld1", ``SUC``)]) of
        NONE => die "FAILED!"
      | SOME _ => OK()

val _ = Hol_datatype`K = <| F : 'a -> bool; S : num |>`

val _ = Hol_datatype`
  big_record = <| fld3 : num ; fld4: bool ; fld5 : num -> num;
                  fld6 : bool -> bool ; fld7 : 'a -> num ;
                  fld8 : num -> num ; fld9: bool # num ;
                  fld10 : num + bool ; fld11 : bool option ;
                  fld12 : bool ; fld13 : num |>`

(* Tom Ridge's example from 2009/04/23 *)
val _ = Hol_datatype `
  command2 =
     Skip2
   | Seq2 of bool # command2 # command2
   | IfThenElse2 of bool # num # command2 # command2
   | While2 of (num # num) # bool # command2
`;

(* this version raises a different error *)
val _ = Hol_datatype `
  tr20090423 =
     trSkip2
   | trSeq2 of bool # tr20090423 # tr20090423
   | trIfThenElse2 of bool # num # tr20090423 # tr20090423
   | trWhile2 of (num # num) # bool # tr20090423
`;

(* both of these were fixed by r6750, which explicitly handles the product
   type, and recursions underneath it. *)

(* r6750 does not handle the following correctly though *)
val _ = Hol_datatype`
  fake_pair = FP of 'a => 'b
`;

val _ = add_infix_type {Assoc = RIGHT, Name = "fake_pair",
                        ParseName = SOME "**", Prec = 70}

val _ = Hol_datatype`
  trprime = trpSkip
      | trpSeq of bool ** trprime ** trprime
      | trpIf of bool ** num ** trprime ** trprime
      | trpW of (num ** num) ** bool ** trprime
`;

(* can see it "more directly" with
val spec =
    [(``:'trp``,
      [("trpSkip", []),
       ("trpSeq", [``:bool ** 'trp ** 'trp``]),
       ("trpIf", [``:bool ** num ** 'trp ** 'trp``]),
       ("trpW", [``:(num ** num) ** bool ** 'trp``])])]
val result = ind_types.define_type spec handle e => Raise e;

- note also that switching the order of the trpSeq and trpIf entries in the
  list above makes it work again.  I.e.,

val spec' =
    [(``:'trp``,
      [("trpSkip", []),
       ("trpIf", [``:bool ** num ** 'trp ** 'trp``]),
       ("trpSeq", [``:bool ** 'trp ** 'trp``]),
       ("trpW", [``:(num ** num) ** bool ** 'trp``])])]
val result = ind_types.define_type spec' handle e => Raise e;

- works.

*)

(* Ramana Kumar's example from 2010/08/19 *)
val _ = Hol_datatype`pointer = pnil | pref of 'a`
val _ = Hol_datatype`failure = <| head : 'a pointer; tail : failure pointer |>`

(* Ramana Kumar's examples from 2010/08/25 *)
val _ = Hol_datatype `t1 = c1 of 'a => t1 itself `;
val _ = Hol_datatype `t2 = c2 of t2 t1 itself ` ;

val _ = Hol_datatype `u1 = d1 of 'a itself`;
val _ = Hol_datatype `u2 = d2 of 'a u1 `;
val _ = Hol_datatype `u3 = d3 of u4 u2 u1 ;
                      u4 = d4 of u3 u1 `;

(* Ramana Kumar's TypeNet bug from 2010/08/25 *)
val _ = Hol_datatype `foo = fooC of 'a`
val _ = Hol_datatype `foo = fooC' of num`

(* from uvm-hol, 2016/10/03
     issue is/was lexing of r-paren/semi-colon agglomerations
*)
val _ = Datatype.Datatype `
  uvmhol1 = uvmholC uvmhol2 num (num -> bool);
  uvmhol2 = uvmholD1 num | uvmHOLD2 uvmhol1
`;

val _ = Datatype.Datatype`
  uvmhol3 = <| uvmfld1 : num # (num -> bool); uvmfld2 : bool |>
`;

(* github issue #1140 *)
val _ = tprint "a = aCtr ('a # bool)"
val _ = testutils.quietly Datatype.Datatype‘
  a = aCtr ('a # bool)
’;
val aCtr_t =
    prim_mk_const{Thy = "scratch", Name = "aCtr"}
    handle HOL_ERR _ => (die "constant aCtr doesn't exist"; boolSyntax.T)
val (cty_d,cty_r) = dom_rng $ type_of aCtr_t
val _ = let val {Thy,Tyop,Args} = dest_thy_type cty_d
        in
          if Thy = "pair" andalso Tyop = "prod" andalso length Args = 2 andalso
             is_vartype (hd Args)
          then
            let val {Thy,Tyop,Args} = dest_thy_type cty_r
            in
              if Thy = "scratch" andalso Tyop = "a" andalso
                 length Args = 1 andalso is_vartype (hd Args)
              then
                OK()
              else die "New type has wrong name/type"
            end
          else die ("Argument to aCtr is wrong type: "^type_to_string cty_d)
        end

val _ = tprint "Testing independence of case variables"
val t = Lib.total Parse.Term `case (x:valbind) of
                                bind p e => 3
                              | bindl p' e p => 4
                              | p => 5`
val _ = case t of NONE => (print "FAILED!\n"; Process.exit Process.failure)
                | SOME _ => OK()

val _ = set_trace "Unicode" 0

fun pptest (nm, t, expected) = let
  val _ = tprint ("Pretty-printing of "^nm)
  val s = Parse.term_to_string t
  fun f s = String.translate (fn #" " => UTF8.chr 0x2423 | c => str c) s
in
  if s = expected then OK()
  else die ("FAILED!\n  Expected \""^expected^"\"; got \""^f s^"\"")
end

fun s t = let open HolKernel boolLib
          in
            rhs (concl (QCONV (simpLib.SIMP_CONV (BasicProvers.srw_ss()) []) t))
          end

val _ = Hol_datatype`ovlrcd = <| id : num ; opn : num -> num |>`
val _ = tprint "dest_record on simple literal"
val _ = let
  fun checkid (n,t) = n = "id" andalso aconv t “0”
  fun checkopn (n,t) = n = "opn" andalso aconv t “SUC”
  fun checknops nops =
      case nops of
          [f1, f2] => (checkid f1 andalso checkopn f2) orelse
                      (checkopn f1 andalso checkid f2)
        | _ => false
  fun check (ty,nops) = ty = “:ovlrcd” andalso checknops nops
  fun prnop (n,t) = "(" ^ n ^ ", " ^ term_to_string t ^ ")"
  fun pr (ty,nops) = "(" ^ type_to_string ty ^",[" ^
                     String.concatWith "," (map prnop nops) ^ ")"
in
  require_msg (check_result check) pr TypeBase.dest_record
              “<| id := 0; opn := SUC|>”
end


val _ = overload_on ("ID", ``f.id``)
val _ = overload_on ("inv", ``f.opn``)
val _ = overload_on ("ovlfoo", ``\n r:ovlrcd. opn_fupd (K (K n)) r``)

val _ = type_abbrev ("ms", ``:'a -> num``)
val _ = Hol_datatype`
  polyrcd = <| pfld1 : 'a ms ; pfld2 : 'b -> bool ; pfld3 : num|>
`;

val _ = Datatype.Datatype`
  polyrcd2 = <| p2fld1 : 'a ms ; p2fld2 : 'a # 'b -> bool ; p2fld3 : num |>
`

val _ = List.app pptest
        [("specific upd overload", ``ovlfoo 2 x``, "ovlfoo 2 x"),
         ("field selection", ``r.fld2``, "r.fld2"),
         ("field sel. for fn type", ``r.fld1 x``, "r.fld1 x"),
         ("singleton field update",
          ``r with fld1 := (\x. T)``, "r with fld1 := (\\x. T)"),
         ("multi-field update", ``r with <| fld2 := 3; fld1 := x |>``,
          "r with <|fld2 := 3; fld1 := x|>"),
         ("big field selection", ``r.fld3``, "r.fld3"),
         ("big field selection (simped)", s ``r.fld3``, "r.fld3"),
         ("big field selection (fn type)", ``r.fld7``, "r.fld7"),
         ("big field selection (fn type, simped)", s ``r.fld7``, "r.fld7"),
         ("big singleton update", ``r with fld3 := 4``, "r with fld3 := 4"),
         ("big singleton update (simped)", s ``r with fld3 := 4``,
          "r with fld3 := 4"),
         ("big multi-update", ``r with <| fld3 := 6; fld9 := (T,6)|>``,
          "r with <|fld3 := 6; fld9 := (T,6)|>"),
         ("big multi-update (simped)",
          s ``r with <| fld3 := 6; fld9 := (T,6)|>``,
          "r with <|fld3 := 6; fld9 := (T,6)|>"),
         ("overloaded bare var.fld", ``ID``, "ID"),
         ("overloaded var.fld with args", ``inv x``, "inv x"),
         ("poly simple upd", ``r : ('c,num) polyrcd with pfld1 := K 1``,
            "r with pfld1 := K 1"),
         ("poly simple seln", ``(r : ('c,'d)polyrcd).pfld1``, "r.pfld1"),
         ("bare ('a,'b) polyrcd_pfld1",
             “polyrcd_pfld1 : ('a,'b) polyrcd -> 'a ms”,
             "polyrcd_pfld1"),
         ("bare ('a,'b) polyrcd_pfld1_fupd",
            ``polyrcd_pfld1_fupd :
                ('a ms -> 'a ms) -> ('a,'b) polyrcd -> ('a,'b) polyrcd``,
            "pfld1_fupd"),
         ("bare (num,num) polyrcd_pfld1",
            ``polyrcd_pfld1 : (num,num) polyrcd -> num ms``, "polyrcd_pfld1"),
         ("bare ('c,'d) polyrcd_pfld1",
            ``polyrcd_pfld1 : ('c,'d) polyrcd -> 'c ms``, "polyrcd_pfld1"),
         ("bare ('c,'d) polyrcd_pfld3",
            ``polyrcd_pfld3 : ('c,'d) polyrcd -> num``, "polyrcd_pfld3"),
         ("bare ('c,'d) polyrcd_pfld1_fupd",
            ``polyrcd_pfld1_fupd :
                ('c ms -> 'c ms) -> ('c,'d) polyrcd -> ('c,'d) polyrcd``,
            "pfld1_fupd"),
         ("one-arg polyrcd_pfld1_fupd",
            ``polyrcd_pfld1_fupd f : ('a,'b) polyrcd -> ('a,'b) polyrcd``,
            "pfld1_fupd f")
         ]

val _ = tprint "bare accessor name parses to constant"
val _ = require_msg (check_result is_const) term_to_string Parse.Term
                    ‘polyrcd_pfld1’

val _ = with_flag (Globals.linewidth, 40) pptest
                  ("multiline record 1",
                   ``<|fld1 := a very long expression indeed ;
                       fld2 := also a long expression|>``,
                  "<|fld1 := a very long expression indeed;\n\
                  \  fld2 := also a long expression|>")

val _ = with_flag (Globals.linewidth, 40) pptest
                  ("multiline record 2",
                   ``<|fld3 := a very long expression indeed ;
                       fld4 := also a long expression|>``,
                  "<|fld3 := a very long expression indeed;\n\
                  \  fld4 := also a long expression|>")

val _ = with_flag (Globals.linewidth, 40) pptest
                  ("multiline record 3",
                   “f x =  <|fld3 := a very long expression indeed ;
                             fld4 := also a long expression|>”,
                   "f x =\n\
                   \<|fld3 := a very long expression indeed;\n\
                   \  fld4 := also a long expression|>")

val _ = with_flag (Globals.linewidth, 40) pptest
                  ("multiline record 4",
                   “let x = <|fld3 := a very long expression indeed ;
                             fld4 := also a long expression|> in f x”,
                   "let\n\
                   \  x =\n\
                   \    <|fld3 :=\n\
                   \        a very long expression indeed;\n\
                   \      fld4 := also a long expression|>\n\
                   \in\n\
                   \  f x")

val _ = with_flag (Globals.linewidth, 40) pptest
                  ("multiline record 5",
                   “R P (f x)
                      <|fld3 := a very long expression indeed ;
                             fld4 := also a long expression|>”,
                   "R P (f x)\n\
                   \  <|fld3 :=\n\
                   \      a very long expression indeed;\n\
                   \    fld4 := also a long expression|>")

val _ = app convtest [
      ("EVAL field K-composition", computeLib.CBV_CONV computeLib.the_compset,
       ``<| fld1 updated_by K t1 o K t2 |>``,
       ``<| fld1 := t1 |>``)
    ]


val _ = Feedback.emit_MESG := false

(* a test for Hol_defn that requires a datatype: *)
(* mutrec defs with sums *)
val _ = tprint "Mutrec defn with sums"
val _ = Hol_datatype `foo2 = F1 of unit | F2 of foo2 + num`
val _ = require (check_result (K true)) (Defn.Hol_defn "foo") `
(foo1 (F1 ()) = F1 ()) /\
(foo1 (F2 sf) = F2 (foo2 sf)) /\
(foo2 (INR n) = INL (F1 ())) /\
(foo2 (INL f) = INL (foo1 f))`

val _ = tprint "Non-recursive num"
val _ = Datatype.Datatype `num = C10 num$num | C11 num | C12 scratch$num`;
val (d,r) = dom_rng (type_of ``C10``)
val _ = if Type.compare(d, numSyntax.num) = EQUAL then () else die "FAILED!"
val (d,r) = dom_rng (type_of ``C11``)
val _ = if Type.compare(d, numSyntax.num) <> EQUAL then () else die "FAILED!"
val (d,r) = dom_rng (type_of ``C12``)
val _ = if Type.compare(d, numSyntax.num) <> EQUAL then () else die "FAILED!"
val _ = OK()

val _ = tprint "Datatype and antiquote (should be quick)"
val num = numSyntax.num
val _ = Datatype.Datatype `dtypeAQ = C13 ^num bool | C14 (^num -> bool)`
val _ = OK()

fun doesnt_fail f x = require (check_result (K true)) f x
val _ = tprint "Records with polymorphic fields 1"
val _ = doesnt_fail Parse.Term ‘polyrcd_pfld1_fupd :
             ('c ms -> 'e ms) -> ('c,'d) polyrcd -> ('e,'d)polyrcd’

val _ = tprint "Records with polymorphic fields 2"
val _ = doesnt_fail Parse.Term `polyrcd2_p2fld1_fupd :
             ('a ms -> 'a ms) -> ('a,'b) polyrcd2 -> ('a,'b)polyrcd2`

val _ = tprint "Records with polymorphic fields 3"
val _ = doesnt_fail Parse.Term `polyrcd2_p2fld2_fupd :
             (('a # 'b -> bool) -> ('a # 'c -> bool)) ->
             ('a,'b) polyrcd2 -> ('a,'c)polyrcd2`

val _ = tprint "Records with polymorphic fields 4"
val _ =
  case Lib.total (trace("show_typecheck_errors", 0) Parse.Term)
       `polyrcd2_p2fld1_fupd :
             ('a ms -> 'b ms) -> ('a,'c) polyrcd2 -> ('b,'c)polyrcd2`
  of
    NONE => OK()
  | _ => die "FAILED!";


val _ = tprint "Testing overriding calls in mutual recursive style";
val _ = quiet_warnings (fn () =>
           (Datatype`a2 = A num ; b = B 'a`;
            Datatype`a2 = A num ; b = B 'a `;
            Datatype `foo = Foo`;
            Datatype`a = A ; b = B `;
            Datatype`a2 = A ; b = B `;
            Datatype`a2 = A ; b2 = B `;
            Datatype `foo = Foo`)) () handle _ => die "FAILED!"
val _ = OK()

val _ = tprint "Test for prove_case_elim_thm (20171201)";
val _ = quiet_warnings (fn () =>
          Datatype `pcet20171201 = C20171201 num | D20171201 (num -> bool)`) ()
          handle _ => die "FAILED!"
val _ = OK()

val _ = tprint "Initial test of indirect datatype recursion with basic types";
(* there are more thorough tests of this in the datatypes_basic_test theory *)
val _ = quiet_warnings (fn () =>
           (Datatype `v_rec = V (v_rec + num) | W`)
           ) () handle _ => die "FAILED!"
val _ = quiet_warnings (fn () =>
           (Datatype`a_rec = A ((a_rec # unit # num option # (unit + num)) list) | B unit`)
           ) () handle _ => die "FAILED!"
val _ = OK()

val _ = Process.exit Process.success;
