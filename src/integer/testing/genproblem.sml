open HolKernel boolLib

open numSyntax

val gen = Random.newgen ()

val vars = map (fn s => mk_var(s, num)) ["u", "v", "x", "y", "z"]

fun gen_term() = let
  val r = Random.random gen
in
  if r < 0.2 then mk_plus(gen_term(), gen_term())
  else if r < 0.4 then mk_suc(gen_term())
  else if r < 0.6 then zero_tm
  else List.nth(vars, floor ((r - 0.6) / 0.08))
end

fun gen_atomic_formula () = let
  val r = Random.random gen
in
  if r < 0.2 then mk_eq(gen_term(), gen_term())
  else if r < 0.4 then mk_less(gen_term(), gen_term())
  else if r < 0.6 then mk_greater(gen_term(), gen_term())
  else if r < 0.8 then mk_geq(gen_term(), gen_term())
  else mk_leq(gen_term(), gen_term())
end

fun gen_formula () = let
  val r = Random.random gen
in
  if r < 0.75 then gen_atomic_formula()
  else if r < 0.85 then mk_neg (gen_formula())
  else if r < 0.90 then mk_conj (gen_formula(), gen_formula())
  else if r < 0.95 then mk_disj (gen_formula(), gen_formula())
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
