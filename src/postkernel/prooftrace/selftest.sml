local open ProofTraceParser in end
structure P = ProofTraceParser

fun die s = (print (s ^ "\n"); OS.Process.exit OS.Process.failure)
fun tprint s = print (StringCvt.padRight #" " 60 s)

fun chk msg b = if b then () else raise Fail msg
fun ieq msg n m =
  chk (msg ^ ": expected " ^ Int.toString n ^ ", got " ^ Int.toString m)
      (n = m)
fun seq msg a b = chk (msg ^ ": expected " ^ a ^ ", got " ^ b) (a = b)

fun check name v f =
  (tprint name;
   let val (root, h) = P.parseVector (PolyML.exportSmall v)
   in f h (P.castPtr root); print "OK\n" end
   handle Fail s => die ("FAILED: " ^ s)
        | e => die ("FAILED (exn): " ^ General.exnMessage e))

fun view h w = P.any h (fn w => w) (P.castPtr w)
fun vint msg n h w =
  case view h w of
    P.Int m => ieq msg n m
  | _ => raise Fail (msg ^ ": not an Int")

(* ---------------------------------------------------------------------
   Primitive encodings
   --------------------------------------------------------------------- *)

val () = check "int 0" 0 (fn h => vint "v" 0 h)
val () = check "int 1" 1 (fn h => vint "v" 1 h)
val () = check "int ~1" ~1 (fn h => vint "v" ~1 h)
val () = check "int 2^29" 536870912 (fn h => vint "v" 536870912 h)
val () = check "int ~2^29" ~536870912 (fn h => vint "v" ~536870912 h)
val () = check "bool false" false (fn h => vint "v" 0 h)
val () = check "bool true" true (fn h => vint "v" 1 h)
val () = check "unit" () (fn h => vint "v" 0 h)
val () = check "char" #"A" (fn h => vint "v" 65 h)

val () = List.app
  (fn s => check ("string (len " ^ Int.toString (size s) ^ ")") s
     (fn h => fn r => seq "v" s (P.str h (P.castPtr r))))
  ["", "a", "1234567", "12345678", "123456789",
   CharVector.tabulate (300, fn i => chr (ord #"a" + i mod 26))]

val () = check "tuple2" (11, "ab") (fn h => fn r => let
  val (a, b) = P.tuple2 h (P.int, P.str h) (P.castPtr r)
  in ieq "fst" 11 a; seq "snd" "ab" b end)

val () = check "tuple3" (1, "x", 2) (fn h => fn r => let
  val (a, (b, c)) = P.tuple3 h (P.int, P.str h, P.int) (P.castPtr r)
  in ieq "1" 1 a; seq "2" "x" b; ieq "3" 2 c end)

val () = check "record field order" {B = 10, A = 20, AA = 30, a = 40}
  (fn h => fn r => let
    val (x1, (x2, (x3, x4))) =
      P.tuple4 h (P.int, P.int, P.int, P.int) (P.castPtr r)
  in ieq "A" 20 x1; ieq "B" 10 x2; ieq "a" 40 x3; ieq "AA" 30 x4 end)

val () = check "list []" ([] : int list) (fn h => fn r =>
  ieq "len" 0 (length (P.list h P.int (P.castPtr r))))

val () = check "list [1,2,3]" [1, 2, 3] (fn h => fn r =>
  chk "v" (P.list h P.int (P.castPtr r) = [1, 2, 3]))

val () = check "appList" [4, 5, 6] (fn h => fn r => let
  val acc = ref 0
  val () = P.appList h (fn w => acc := !acc + P.int w) (P.castPtr r)
  in ieq "sum" 15 (!acc) end)

val () = check "option NONE" (NONE : int option) (fn h => fn r =>
  chk "v" (not (isSome (P.option h P.int (P.castPtr r)))))

val () = check "option SOME" (SOME 5) (fn h => fn r =>
  chk "v" (P.option h P.int (P.castPtr r) = SOME 5))

val () = check "HOLset empty" (HOLset.empty Int.compare) (fn h => fn r => let
  val cnt = ref 0
  val () = P.appSet h (fn _ => cnt := !cnt + 1) (P.castPtr r)
  in ieq "count" 0 (!cnt) end)

val () = check "HOLset elements"
  (HOLset.addList (HOLset.empty Int.compare, [5, 1, 9, 3, 7, 2, 8]))
  (fn h => fn r => let
    val sum = ref 0 and cnt = ref 0
    val () = P.appSet h
      (fn w => (sum := !sum + P.int w; cnt := !cnt + 1)) (P.castPtr r)
  in ieq "sum" 35 (!sum); ieq "count" 7 (!cnt) end)

(* ---------------------------------------------------------------------
   Kernel types
   --------------------------------------------------------------------- *)

(* Type.hol_type and Term.term are opaque under the Overlay, so the test
   values are built directly from the underlying Type_dtype/KernelTypes
   constructors; ids live behind opaque KernelSig and are cast. *)
local
  open Type_dtype KernelTypes
  fun mkid thy nm e : id =
    RunCall.unsafeCast {name = {Thy = thy, Name = nm}, epoch = e}
  val alpha = Tyv "'a"
  val bool = Tyapp ((mkid "min" "bool" 3, 0), [])
in
  val ty_alpha = alpha
  val ty_bool = bool
  val ty_fun = Tyapp ((mkid "min" "fun" 4, 2), [alpha, bool])
  val va = Fv ("a", alpha)
  val vb = Fv ("b", alpha)
  val abs_tm = Abs (va, Bv 0)
  val comb_tm = Comb (Abs (va, Bv 0), vb)
  val const_tm = Const (mkid "min" "=" 7, POLY ty_fun)
  val subs_id : term Subst.subs = Subst.id
  val subs1 = Subst.cons (Subst.lift (2, Subst.shift (1, Subst.id)), va)
  val clos_tm = Clos (subs1, va)
end

fun chkty h msg thy nm ep nargs w =
  case P.shType h (P.castPtr w) of
    P.Tyapp (idp, args) => let
      val (t, n, e) = P.ident h idp
      in seq (msg ^ " Thy") thy t; seq (msg ^ " Name") nm n;
         ieq (msg ^ " epoch") ep e;
         ieq (msg ^ " args") nargs (length (P.list h (fn w => w) args))
      end
  | P.Tyv _ => raise Fail (msg ^ ": unexpected Tyv")

val () = check "shType Tyv" ty_alpha (fn h => fn r =>
  case P.shType h (P.castPtr r) of
    P.Tyv s => seq "name" "'a" s
  | _ => raise Fail "not Tyv")

val () = check "shType Tyapp/ident" ty_bool (fn h => fn r =>
  chkty h "bool" "min" "bool" 3 0 r)

val () = check "shType fun" ty_fun
  (fn h => fn r =>
    case P.shType h (P.castPtr r) of
      P.Tyapp (idp, args) => let
        val (thy, nm, e) = P.ident h idp
        val () = seq "Thy" "min" thy
        val () = seq "Name" "fun" nm
        val () = ieq "epoch" 4 e
      in
        case P.list h (fn w => w) args of
          [_, rng] => chkty h "rng" "min" "bool" 3 0 rng
        | _ => raise Fail "fun arity"
      end
    | _ => raise Fail "not Tyapp")

fun fvname h w =
  case P.shTerm h (P.castPtr w) of
    P.Fv (s, _) => s
  | _ => raise Fail "not Fv"

val () = check "shTerm Fv" va (fn h => fn r =>
  case P.shTerm h (P.castPtr r) of
    P.Fv (s, ty) =>
      (seq "name" "a" s;
       case P.shType h ty of
         P.Tyv v => seq "ty" "'a" v
       | _ => raise Fail "Fv type")
  | _ => raise Fail "not Fv")

val () = check "shTerm Abs/Bv" abs_tm (fn h => fn r =>
  case P.shTerm h (P.castPtr r) of
    P.Abs (bv, body) =>
      (seq "bvar" "a" (fvname h bv);
       case P.shTerm h body of
         P.Bv i => ieq "body" 0 i
       | _ => raise Fail "body not Bv")
  | _ => raise Fail "not Abs")

val () = check "shTerm Comb" comb_tm
  (fn h => fn r =>
    case P.shTerm h (P.castPtr r) of
      P.Comb (f, x) =>
        ((case P.shTerm h f of P.Abs _ => ()
                             | _ => raise Fail "rator not Abs");
         seq "rand" "b" (fvname h x))
    | _ => raise Fail "not Comb")

val () = check "shTerm Const/ident" const_tm (fn h => fn r =>
  case P.shTerm h (P.castPtr r) of
    P.Const (idp, ty) => let
      val (thy, nm, e) = P.ident h idp
      in seq "Thy" "min" thy; seq "Name" "=" nm; ieq "epoch" 7 e;
         chkty h "const ty" "min" "fun" 4 2 ty
      end
  | _ => raise Fail "not Const")

val () = check "shSubs Id" subs_id
  (fn h => fn r =>
    case P.shSubs h (P.castPtr r) of
      P.Id => ()
    | _ => raise Fail "not Id")

val () = check "shSubs Cons/Lift/Shift" subs1 (fn h => fn r =>
  case P.shSubs h (P.castPtr r) of
    P.Cons (sp, elt) =>
      (seq "elt" "a" (fvname h elt);
       case P.shSubs h sp of
         P.Lift (n, sp2) =>
           (ieq "Lift" 2 n;
            case P.shSubs h sp2 of
              P.Shift (m, sp3) =>
                (ieq "Shift" 1 m;
                 case P.shSubs h sp3 of
                   P.Id => ()
                 | _ => raise Fail "not Id")
            | _ => raise Fail "not Shift")
       | _ => raise Fail "not Lift")
  | _ => raise Fail "not Cons")

val () = check "shTerm Clos" clos_tm (fn h => fn r =>
  case P.shTerm h (P.castPtr r) of
    P.Clos (sp, tp) =>
      (seq "body" "a" (fvname h tp);
       case P.shSubs h sp of
         P.Cons _ => ()
       | _ => raise Fail "subs not Cons")
  | _ => raise Fail "not Clos")

val () = check "thmId SavedAnon" (Thm.SavedAnon 42) (fn h => fn r =>
  chk "v" (P.thmId h (P.castPtr r) = Thm.SavedAnon 42))
val () = check "thmId SavedName" (Thm.SavedName "foo") (fn h => fn r =>
  chk "v" (P.thmId h (P.castPtr r) = Thm.SavedName "foo"))

(* ---------------------------------------------------------------------
   thminfo
   --------------------------------------------------------------------- *)

val () = check "thminfo private=true"
  ({private = true, loc = RawTheory_dtype.Unknown,
    class = RawTheory_dtype.Thm} : RawTheory_dtype.thminfo)
  (fn h => fn r => chk "private" (#private (P.shThmInfo h (P.castPtr r))))

val () = check "thminfo private=false"
  ({private = false,
    loc = RawTheory_dtype.Located
            {scriptpath = "p", linenum = 3, exact = true},
    class = RawTheory_dtype.Def} : RawTheory_dtype.thminfo)
  (fn h => fn r =>
    chk "private" (not (#private (P.shThmInfo h (P.castPtr r)))))


val () = print "All prooftrace parser selftests passed\n"
