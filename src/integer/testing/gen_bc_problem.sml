open HolKernel boolLib

open intSyntax

val gen = Random.newgen ()

val vars = map (fn s => mk_var(s, int_ty)) ["u", "v", "x", "y", "z"]

fun gen_term v = let
  val c = term_of_int (Arbint.fromInt (Random.range(~20, 21) gen))
in
  mk_mult(c, v)
end

fun gen_lhs() = list_mk_plus (map gen_term vars)

fun gen_rhs() = term_of_int (Arbint.fromInt(Random.range(~100,101) gen))

fun gen_atomic_formula () = let
  val r = Random.random gen
  val opn = if r < 0.33 then mk_eq else mk_less
in
  opn(gen_lhs(), gen_rhs())
end

fun gen_formula () = let
  val r = Random.random gen
in
  if r < 0.65 then gen_atomic_formula()
  else if r < 0.70 then mk_neg (gen_formula())
  else if r < 0.80 then mk_conj (gen_formula(), gen_formula())
  else if r < 0.90 then mk_disj (gen_formula(), gen_formula())
  else mk_imp (gen_formula(), gen_formula())
end

val _ = Globals.show_types := true;
fun gen n = if n <= 0 then ()
            else (Parse.print_term (gen_formula());
                  print "\n\n";
                  gen (n - 1))

fun die s = (TextIO.output(TextIO.stdErr, s);
               TextIO.flushOut TextIO.stdErr;
               Process.exit Process.failure);

val numtoprint =
  case CommandLine.arguments () of
    [] => 10
  | [x] => (let
      val n = valOf (Int.fromString x)
      val _ = n > 0 orelse raise Fail ""
    in
      n
    end handle _ => die "Argument must be one positive integer\n")
  | _ => die "Argument must be one positive integer\n"

val _ = gen numtoprint
