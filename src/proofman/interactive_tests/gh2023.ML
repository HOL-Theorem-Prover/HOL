
load "testutils";

local
open HolKernel testutils;
infixr 3 -->;
infix |->;

val bool = Type.bool;
val alpha = Type.alpha;

fun mk_eq ty l r =
  Term.list_mk_comb
    (Term.inst [alpha |-> ty] Term.equality, [l, r]);
in
(* Use primitive reflexivity as a provable replacement for kernel T. *)
fun prove_bad_things () = let
val x = Term.mk_var ("x", bool)
val id = Term.mk_abs (x, x)
val truth_th = Thm.REFL id
val fake_true = Thm.concl truth_th

val _ = Thm.register_T (Thm.REFL fake_true);

(* Register the expected implementation of universal quantification as its
 * own left-hand side. *)
val P = Term.mk_var ("P", alpha --> bool);
val a = Term.mk_var ("a", alpha);
val forall_rhs =
  Term.mk_abs
    (P, mk_eq (alpha --> bool) P (Term.mk_abs (a, fake_true)));

val _ = Thm.register_forall (Thm.REFL forall_rhs);

(* Make the kernel's registered F be fake_true.  The oracle tag on this
 * registration theorem is discarded by register_F. *)
val t = Term.mk_var ("t", bool);
val fake_F_rhs =
  Term.mk_comb
    (Term.inst [alpha |-> bool] forall_rhs,
     Term.mk_abs (t, t));

val fake_F_def =
  Thm.mk_thm ([], mk_eq bool fake_true fake_F_rhs);

val _ = Thm.register_F fake_F_def;

(* CCONTR also consults the registered negation operation. *)
val imp = Term.prim_mk_const {Thy = "min", Name = "==>"};
val neg_rhs =
  Term.mk_abs
    (t, Term.list_mk_comb (imp, [t, fake_true]));

val _ = Thm.register_neg (Thm.REFL neg_rhs);

(* Since truth_th proves the poisoned get_F(), CCONTR now proves any Boolean
 * term without assumptions. *)
val arbitrary = Term.mk_var ("arbitrary", bool);
in
  Thm.CCONTR arbitrary truth_th
end

end (* local *)

val _ = testutils.shouldfail {checkexn = fn _ => true,
                    printarg = fn _ => "\nChecking gh bug 2023",
                    printresult = fn _ => "a theorem",
                    testfn = prove_bad_things} ()
