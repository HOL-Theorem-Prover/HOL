open HolKernel Parse boolLib bossLib;

val _ = new_theory "github416";

val _ = Datatype `exp = Const num num | Downcast num exp`;

val test_def = Define `
  test (e:exp) (map: exp -> num option) : bool =
    case e of
     | Const m n => (case map e of
                      | SOME m' => m = m'
                      | NONE => F)
     | Downcast m e1 => (case map e, map e1 of
                           | SOME m', SOME m1 => (m' = m) /\ test e1 map
                           | _, _ => F)
     | _ => F`;


val test_THM = (store_thm ("test_THM", ``!m e m' m1 map.
  (map (Downcast m e) = SOME m') /\
  (map e = SOME m1) ==>

  (test (Downcast m e) map <=> ((m' = m) /\ test e map))``,

SIMP_TAC (srw_ss()) [Once test_def])) handle HOL_ERR _ => (
  print "Test for github issue #416 failed - FAILURE\n";
  OS.Process.exit OS.Process.failure);

val _ = print "Test-case OK\n";

val _ = export_theory();
