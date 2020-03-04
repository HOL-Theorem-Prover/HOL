open HolKernel boolLib simpLib Parse realSimps

open testutils

val s = SIMP_CONV (bossLib.std_ss ++ REAL_REDUCE_ss) []

fun test (problem, result) = let
  val t2s = trace ("Unicode", 0) term_to_string
  val padr = StringCvt.padRight #" "
  val padl = StringCvt.padLeft #" "
  val p_s = padr 30 (t2s problem)
  val r_s = padl 10 (t2s result)
  val _ = tprint (p_s ^ " = " ^ r_s)
  val th = QCONV s problem
  val answer = rhs (concl th)
in
  if aconv answer result then OK()
  else die ("FAILED!\n  Got "^term_to_string answer)
end;

val tests = [(``~~3r``, ``3r``),
             (``3r + 4``, ``7r``),
             (``3 - 4r``, ``~1r``),
             (``abs (~20r)``, ``20r``),
             (``abs (1/6)``, ``1/6``),
             (``abs (~3/6)``, ``1/2``),
             (``abs 0``, ``0``),
             (``3r * 3/4``, ``9/4``),
             (``6/~8``, ``~3/4``),
             (``1/3 + 1/2``, ``5/6``),
             (``1/2 = 0``, ``F``),
             (``0 + 3r``, ``3r``),
             (``3r * 0``, ``0r``),
             (``~0r``, ``0r``),
             (``1r - 0``, ``1r``),
             (``1 / 10 + 0r``, ``1r/10``),
             (``0r + 1 / 10``, ``1r/10``),
             (``1/2 * 0r``, ``0r``),
             (``0r * 1/2``, ``0r``)]

val _ = List.app test tests

val _ = List.app
          (fn (s1,s2) => tpp_expected
                           {testf=standard_tpp_message, input=s1, output=s2})
          [("realinv 2", "2⁻¹"), ("inv (TC R)", "R⁺ ᵀ")]

fun UNCH_test (n,c,t) =
  shouldfail {checkexn = fn Conv.UNCHANGED => true | _ => false,
              printarg = fn t => "UNCHANGED " ^ n ^ ": " ^ term_to_string t,
              printresult = thm_to_string, testfn = c} t
fun nftest (r as (n,c,t1,t2)) =
    let
      fun test (t1,t2) = (Exn.capture c t1, Exn.capture c t2)
      fun check t res =
          case res of
              Exn.Res (Exn.Res rth, Exn.Exn Conv.UNCHANGED) =>
                rhs (concl rth) ~~ t
            | _ => false
      fun pr1 t (Exn.Exn e) = "On first call, unexpected exn: " ^
                                General.exnMessage e
        | pr1 t (Exn.Res th) = if is_eq (concl th) andalso
                                  rhs (concl th) ~~ t
                               then ""
                               else "On first call, unexpected thm:\n  " ^
                                    thm_to_string th
      fun nlnzero "" = "" | nlnzero s = s ^ "\n"
      fun pr2 (Exn.Exn Conv.UNCHANGED) s = s
        | pr2 (Exn.Exn e) s = nlnzero s ^ "On 2nd call, unexpected exn: " ^
                              General.exnMessage e
        | pr2 (Exn.Res th) s = nlnzero s ^ "On 2nd call, unexpected thm:\n  " ^
                               thm_to_string th
      fun pr t (r1,r2) = pr2 r2 (pr1 t r1)
    in
      tprint (n ^ ": " ^ term_to_string t1);
      require_msg (check t2) (pr t2) test (t1,t2)
    end
val simp = SIMP_CONV (BasicProvers.srw_ss()) []
val _ = List.app nftest [
      ("MULCANON01", REALMULCANON, “x:real * y * x”, “x pow 2 * y”),
      ("MULCANON02", REALMULCANON, “x:real * y * x * 2”, “2 * (x pow 2 * y)”),
      ("MULCANON03", REALMULCANON,
       “10 * (x:real) * y * x pow 3 * y * x pow 4 * z * 6”,
       “60 * (x pow 8 * y pow 2 * z)”),
      ("MULCANON04", REALMULCANON, “x * 1r * z”, “x:real * z”),
      ("MULCANON05", REALMULCANON, “x * y * inv x * a”, “a * y * NZ x”),
      ("MULCANON06", REALMULCANON, “b * x pow 2 * y * inv x * a”,
       “a * b * x * y”),
      ("MULCANON07", REALMULCANON, “b * x * y * inv (x pow 2) * 2 * a”,
       “2 * (a * b * inv x * y)”),
      ("MULCANON08", REALMULCANON, “b * x * y * inv (x pow 2) * a * inv x”,
       “a * b * inv x pow 2 * y”),
      ("MULCANON09", REALMULCANON, “x * 2r”, “2r * x”),
      ("MULCANON10", REALMULCANON, “x * 2r * y”, “2r * (x * y)”),
      ("MULCANON11", REALMULCANON, “x * 3 * y * x pow n * z”,
       “3 * (x * y * z * x pow n)”),
      ("MULCANON12", REALMULCANON, “2 pow x * z * 10 * 2 pow n”,
       “10 * (z * 2 pow n * 2 pow x)”),
      ("MULCANON13", REALMULCANON, “-(2 pow x) * z * -10 * 2 pow n”,
       “10 * (z * 2 pow n * 2 pow x)”),
      ("MULCANON14", REALMULCANON, “inv 2 pow x * z * 2 pow x”, “z:real”),
      ("MULCANON15", REALMULCANON, “inv (2 pow x) * z * 3 * 2 pow x”,
       “3 * z:real”),
      ("MULCANON16", REALMULCANON, “inv (2 pow x) * z * 3”,
       “3 * (z * inv 2 pow x)”),
      ("MULCANON17", REALMULCANON, “4 * (inv 2 * z)”, “2r * z”),
      ("MULCANON18", REALMULCANON,
       “2 * (inv 3 * z * 2 * inv 10)”, “(2r/15) * z”),
      ("MULCANON19", REALMULCANON, “2 * (inv 3 * z * 6 * inv 4)”, “z:real”),
      ("MULCANON21", REALMULCANON, “-z * x: real”, “-(x * z:real)”),
      ("MULCANON22", REALMULCANON, “2 * (-inv 3 * z * 6 * inv 4)”, “-z:real”),
      ("MULRELNORM01", simp,
       “z <> 0 ⇒ 2r * z pow 2 * inv yy = 5 * z pow 2 * inv y * a”,
       “z <> 0 ⇒ 2 * inv yy = 5 * (a * inv y)”),
      ("MULRELNORM02", simp, “z * 4 = inv x * 6”, “2 * z = 3 * inv x”),
      ("MULRELNORM03", simp,
       “y <> 0 ==> 2 * inv y pow 2 <= 9 * inv y * z”,
       “y <> 0 ==> 2 <= 9 * (y * z)”),
      ("MULRELNORM04", simp,
       “inv (2 pow x) * inv y pow 2 <= 9 * inv y * inv 2 pow x”,
       “inv y pow 2 <= 9 * inv y”),
      ("MULRELNORM05", simp,
       “y <> 0 ==>
        inv (2 pow x) * inv y pow 2 <= 9 * inv y pow 6 * inv 2 pow x”,
       “y <> 0 ==> y pow 4 <= 9”),
      ("MULRELNORM06", simp,
       “0 < x ==> 3 * x pow 2 <= x”, “0 < x ==> 3 * x <= 1r”),
      ("MULRELNORM07", simp,
       “0 < x ==> 3 * x pow 2 <= inv x”, “0 < x ==> 3 * x pow 3 <= 1r”),
      ("MULRELNORM08", simp, “2 * x <= inv 2 * y * z”, “4r * x <= y * z”),
      ("MULRELNORM09", simp, “0r < x ==> x <= x * y”, “0r < x ==> 1 <= y”),
      ("ADDCANON1", REALADDCANON, “10 + x * 2 + x * y + 6 + x”,
       “3 * x + x * y + 16”)
    ]

val _ = Process.exit Process.success
