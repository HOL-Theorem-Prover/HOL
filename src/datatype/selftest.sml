(* tests for Hol_datatype *)

open HolKernel Parse

val _ = Feedback.set_trace "Theory.save_thm_reporting" 0;

fun Hol_datatype q = let
  open TextIO Feedback
  val _ = Datatype.Hol_datatype q
      handle e => (output(stdErr, "Exception raised: "^exn_to_string e);
                   Process.exit Process.failure)
in
  ()
end

val _ = Hol_datatype `type1 = one_constructor`
val _ = Hol_datatype `type2 = ##`;
val _ = Hol_datatype `type3 = /\`;
val _ = Hol_datatype `type4 = /\ | \/ | feh`;
val _ = Hol_datatype `type5 = foo of num | bar of 'a`;


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
val _ = Hol_datatype `bintree = LEAF of 'a | TREE of bintree => bintree`;
val _ = Hol_datatype `typ = C of one => (one#one)
                      => (one -> one -> 'a list)
                      => ('a,one#one,'a list) ty`;
val _ = Hol_datatype `Typ = D of one # (one#one)
                      # (one -> one -> 'a list)
                      # ('a, one#one, 'a list) ty`;

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
val _ = Hol_datatype`K = <| F : 'a -> bool; S : num |>`

val _ = Datatype.big_record_size := 10;
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

fun tprint s = print (StringCvt.padRight #" " 70 s)

val _ = tprint "Testing independence of case variables"
val t = Lib.total Parse.Term `case (x:valbind) of
                                 bind p e -> 3
                              || bindl p' e p -> 4
                              || p -> 5`
val _ = case t of NONE => (print "FAILED!\n"; Process.exit Process.failure)
                | SOME _ => print "OK\n"

val _ = set_trace "Unicode" 0

fun pptest (nm, t, expected) = let
  val _ = tprint ("Testing pretty-printing of "^nm)
  val s = Parse.term_to_string t
in
  if s = expected then print "OK\n"
  else (print "FAILED!\n"; Process.exit Process.failure)
end

fun s t = let open HolKernel boolLib
          in
            rhs (concl (simpLib.SIMP_CONV (BasicProvers.srw_ss()) [] t))
          end

val _ = List.app pptest
        [("field selection", ``r.fld2``, "r.fld2"),
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
          "r with <|fld3 := 6; fld9 := (T,6)|>")
         ]

val _ = Process.exit Process.success;
