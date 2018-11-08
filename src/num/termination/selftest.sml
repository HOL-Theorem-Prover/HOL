open HolKernel Parse boolLib
open testutils TotalDefn
val _ = Feedback.emit_MESG := false
val _ = print "\n"
val _ = tprint "Testing mutually recursive function definition"

val f_def = Define`
  (f x = if x = 0 then T else ~g(x - 1)) /\
  (g x = if x = 0 then F else ~f(x - 1))
` handle _ => die "FAILED!"
val _ = OK();

val _ = tprint "Testing definition over literals"

val h_def = Define`
  (h 0 = T) /\ (h 1 = F)
`;

val _ = let
  val cs = strip_conj (concl h_def)
  val _ = length cs = 2 orelse die "FAILED!"
  val _ = List.all (is_const o rhs) cs orelse die "FAILED!"
in
  OK()
end

val _ = tprint "Testing form of derived induction principle"
val fact_def = Define`fact n = if n < 2 then 1 else n * fact(n - 1)`;

val desired_ind =
  ``!P. (!n. (~(n < 2) ==> P (n - 1)) ==> P n) ==> !v. P v``

val _ = if aconv desired_ind (concl (theorem "fact_ind")) then OK()
        else die "FAILED!\n"

val fs_def = DefineSchema`(fs 0 y = z + y) /\ (fs x y = x)`;
val gs_def = DefineSchema`(gs 0 y = x + y) /\ (gs x y = x)`;

val _ = tprint "Testing 0-arg recursive function with lambda"

val f1_def = Define`
  f1 = \x. case x of 0 => 0n | SUC n => f1 n
` handle _ => die "FAILED!"
val _ = OK();

val _ = tprint "Testing 1-arg recursive function with lambda"

val f1_def = Define`
  f2 (y : 'a) = \x. case x of 0 => 0n | SUC n => f2 y n
` handle _ => die "FAILED!"
val _ = OK();

val _ = tprint "Testing 2-arg recursive function with lambda"

val f1_def = Define`
  f3 (y : 'a) (z : 'a) = \x. case x of 0 => 0n | SUC n => f3 y z n
` handle _ => die "FAILED!"
val _ = OK();

val LENGTH_FILTER_SUBSET = Q.prove(
`(!y. P y ==> Q y) ==> !L. LENGTH(FILTER P L) <= LENGTH (FILTER Q L)`,
strip_tac >> Induct THEN rw[] >> metis_tac[]);

val variant_def = tDefine "variant" ‘
  variant x l = if MEM x l then variant (x + 1) l else x
’ (WF_REL_TAC ‘measure (λ(x,l). LENGTH (FILTER ((<=) x) l))’ >>
   Induct >> rw[] >>
   simp [DECIDE “x < SUC y ⇔ x ≤ y”, LENGTH_FILTER_SUBSET])
