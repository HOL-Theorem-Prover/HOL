open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pairTheory sumTheory listTheory;
open prim_recTheory arithmeticTheory combinTheory stringTheory;

open CCSLib CCSTheory CCSSyntax CCSConv;
open StrongEQTheory StrongEQLib StrongLawsTheory;
open WeakEQTheory WeakEQLib WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory;
open CongruenceTheory CoarsestCongrTheory;
open TraceTheory ExpansionTheory ContractionTheory;
open BisimulationUptoTheory UniqueSolutionsTheory;

open testutils;

val _ = srw_ss()
val term_to_string = Portable.with_flag (Globals.linewidth, 3000) term_to_string

fun CCS_TRANS_test (problem, result) = let
  val padr = StringCvt.padRight #" ";
  val padl = StringCvt.padLeft #" ";
  val p_s = padr 30 (term_to_string problem);
  val r_s = padl 10 (term_to_string result);
  val _ = tprint (p_s ^ " = " ^ r_s);
in
  require_msg (check_result (aconv result o concl o #1))
              (term_to_string o concl o #1)
              CCS_TRANS
              problem
end;

val CCS_TRANS_tests =
    [(* test #1 *)
     (``(restr {name "a"}) (label (name "a")..nil || label (coname "a")..nil)``,
“∀u E.
   (ν"a") (In "a"..nil || Out "a"..nil) --u-> E ⇔
   (u = τ) ∧ (E = (ν"a") (nil || nil))”),

     (* test #2 *)
     (``par (prefix (label (name "a")) nil)
            (prefix (label (coname "a")) nil)``,
“∀u E.
   In "a"..nil || Out "a"..nil --u-> E ⇔
   ((u = In "a") ∧ (E = nil || Out "a"..nil) ∨
    (u = Out "a") ∧ (E = In "a"..nil || nil)) ∨
   (u = τ) ∧ (E = nil || nil)”),

     (* test #3 *)
     (``par nil nil``,
“∀u (E :'a CCS). ¬(nil || nil --u-> E)”),

     (* test #4 *)
     (``restr { name "a" } (par nil nil)``,
“∀u E. ¬((ν"a") (nil || nil) --u-> E)”),

     (* test #5 *)
     (``label (name "a")..label (name "b")..nil +
             label (name "b")..label (name "a")..nil``,
“∀u E.
   In "a"..In "b"..nil + In "b"..In "a"..nil --u-> E ⇔
   (u = In "a") ∧ (E = In "b"..nil) ∨ (u = In "b") ∧ (E = In "a"..nil)”),

     (* test #6 *)
     (``(restr {name "a"} (label (name "a")..nil || label (coname "a")..nil)) ||
                (label (name "a")..nil)``,
“∀u E.
   (ν"a") (In "a"..nil || Out "a"..nil) || In "a"..nil --u-> E ⇔
   (u = τ) ∧ (E = (ν"a") (nil || nil) || In "a"..nil) ∨
   (u = In "a") ∧ (E = (ν"a") (In "a"..nil || Out "a"..nil) || nil)”),

     (* test #7 *)
     (``rec "VM" (In "coin"..(In "ask-esp"..rec "VM1" (Out "esp-coffee"..var "VM") +
                              In "ask-am"..rec "VM2" (Out "am-coffee"..var "VM")))``,
“∀u E.
   rec "VM"
     (In "coin"
      ..
      (In "ask-esp"..rec "VM1" (Out "esp-coffee"..var "VM") +
       In "ask-am"..rec "VM2" (Out "am-coffee"..var "VM")))
   --u->
   E ⇔
   (u = In "coin") ∧
   (E =
    In "ask-esp"
    ..
    rec "VM1"
      (Out "esp-coffee"
       ..
       rec "VM"
         (In "coin"
          ..
          (In "ask-esp"..rec "VM1" (Out "esp-coffee"..var "VM") +
           In "ask-am"..rec "VM2" (Out "am-coffee"..var "VM")))) +
    In "ask-am"
    ..
    rec "VM2"
      (Out "am-coffee"
       ..
       rec "VM"
         (In "coin"
          ..
          (In "ask-esp"..rec "VM1" (Out "esp-coffee"..var "VM") +
           In "ask-am"..rec "VM2" (Out "am-coffee"..var "VM")))))”)];

val _ = List.app (ignore o CCS_TRANS_test) CCS_TRANS_tests;

val _ = Process.exit Process.success;
