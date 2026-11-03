open HolKernel boolLib testutils;

val _ = new_theory "scratch";

val failures = ref 0;
val _ = diemode := Remember failures;

fun prime_term n =
  mk_comb (prim_mk_const {Thy = "divides", Name = "prime"},
           numSyntax.mk_numeral (Arbnum.fromString n));

fun certificate_test (name, certificates, n) =
  let
    val tm = prime_term n
    val expected = mk_eq (tm, boolSyntax.T)
    val conv = primeCertificateLib.PRIME_CERT_CONV certificates
    fun check th = null (hyp th) andalso aconv (concl th) expected
  in
    tprint name;
    require_msg (check_result check) thm_to_string conv tm
  end;

val _ = List.app certificate_test
  [("Padded certificate candidate",
    [("05", "2", [("2", 2)])], "5"),
   ("Padded built-in factor",
    [("5", "2", [("02", 2)])], "5"),
   ("Padded built-in factor 3",
    [("7", "3", [("2", 1), ("03", 1)])], "7"),
   ("Recursive factor and candidate with different padding",
    [("0011", "2", [("02", 1), ("0005", 1)]),
     ("05", "2", [("2", 2)])], "11"),
   ("Built-in prime 2", [], "2"),
   ("Built-in prime 3", [], "3")];

val _ = tprint "Reject composite certificate with complete factorisation";
val _ = shouldfail
  {testfn = primeCertificateLib.PRIME_CERT_CONV
     [("9", "2", [("2", 3)])],
   printresult = thm_to_string,
   printarg = term_to_string,
   checkexn = fn HOL_ERR _ => true | _ => false}
  (prime_term "9");

val _ = exit_count0 failures;
