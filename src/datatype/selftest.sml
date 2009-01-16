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

val _ = Datatype.big_record_size := 10;
val _ = Hol_datatype`
  big_record = <| fld3 : num ; fld4: bool ; fld5 : num -> num;
                  fld6 : bool -> bool ; fld7 : 'a -> num ;
                  fld8 : num -> num ; fld9: bool # num ;
                  fld10 : num + bool ; fld11 : bool option ;
                  fld12 : bool ; fld13 : num |>`

fun tprint s = print (StringCvt.padRight #" " 70 s)

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
