open HolKernel Parse boolLib bossLib;

val _ = new_theory "oneline";

fun is_oneline th = is_eq (concl th)

infix AND
fun (P AND Q) x = P x andalso Q x
val nullhyps = null o hyp
fun defines th1 th2 =
  let val cs = th1 |> concl |> strip_forall |> #2 |> strip_conj
      val c = cs |> hd |> strip_forall |> #2 |> lhs |> strip_comb |> #1
  in
    same_const c (th2 |> concl |> lhs |> strip_comb |> #1)
  end

fun stdcheck th =
  assert (is_oneline AND nullhyps AND defines th) $
         DefnBase.one_line_ify NONE th

Definition ZIP2:
  (ZIP2 ([],[]) z = []) /\
  (ZIP2 (x::xs,y::ys) z = (x,y) :: ZIP2 (xs, ys) (5:num))
Termination
  WF_REL_TAC ‘measure (\p. LENGTH (FST (FST p)) + LENGTH (SND (FST p)))’ >>
  simp[]
End

val oneline_zip2 = DefnBase.one_line_ify NONE ZIP2
val _ = assert
         (fn l => length l = 1 andalso is_disj (hd l))
         (hyp oneline_zip2)
val _ = assert is_oneline oneline_zip2

val _ = stdcheck listTheory.ZIP_def
val _ = assert is_oneline
               (DefnBase.one_line_ify NONE
                (INST_TYPE [gamma |-> alpha, delta |->beta] listTheory.ZIP))

Definition AEVERY_AUX_def:
  (AEVERY_AUX aux P [] <=> T) /\
  (AEVERY_AUX aux P ((x:'a,y:'b)::xs) <=>
     if MEM x aux then AEVERY_AUX aux P xs
     else
       P (x,y) /\ AEVERY_AUX (x::aux) P xs)
End
val _ = stdcheck AEVERY_AUX_def

Definition incomplete_literal:
  incomplete_literal 1 = 10 /\
  incomplete_literal 2 = 11 /\
  incomplete_literal 3 = 30
End

val oneline_incomplete = DefnBase.one_line_ify NONE incomplete_literal
val (theta, _) = match_term
  “incomplete_literal svar =
     case svar of 1 => 10 | 2 => 11 | 3 => 30 | _ => ARB”
  (concl oneline_incomplete)
val _ = length (hyp oneline_incomplete) = 1 andalso
        aconv (hd (hyp oneline_incomplete))
              (subst theta “svar = 1 \/ svar = 2 \/ svar = 3”) orelse
        raise Fail "incomplete_literal test fails"

Definition complete_literal0:
  complete_literal0 1 = 10 /\
  complete_literal0 2 = 12 /\
  complete_literal0 _ = 15
End
val _ = stdcheck complete_literal0

Definition complete_literal1a:
  complete_literal1a [] 1 = 10 /\
  complete_literal1a (3::t) 2 = 16 /\
  complete_literal1a (h::t) 2 = 12 + h /\
  complete_literal1a _ _ = 15
End
val _ = stdcheck complete_literal1a

Definition complete_literal1b:
  complete_literal1b ([], 1) = 10 /\
  complete_literal1b (3::t, 2) = 16 /\
  complete_literal1b (h::t, 2) = 12 + h /\
  complete_literal1b _ = 15
End
val _ = stdcheck complete_literal1b

Definition complete_literal2:
  complete_literal2 (3, [], 2) = 10 /\
  complete_literal2 (5, h::t, x) = 12 + h + x /\
  complete_literal2 _ = 15
End
val _ = stdcheck complete_literal2

Definition ADEL_def:
  (ADEL [] z = []) /\
  (ADEL ((x:'a,y:'b)::xs) z = if x = z then ADEL xs z else (x,y)::ADEL xs z)
End
val _ = stdcheck ADEL_def

Definition bar_def:
  bar = [] : 'a list
End
val _ = stdcheck bar_def

Definition foo1_def:
  foo1 = if bar = []:'a list then []:'a list else []
End
val _ = stdcheck foo1_def

Datatype:
  tt = A1
     | B1 tt
     | C1 (tt option)
     | D1 (tt list)
     | E1 (tt # tt)
End

Definition test_def:
  test A1 = [()] /\
  test (B1 x) = test x ++ [()] /\
  test (C1 NONE) = [] /\
  test (C1 (SOME x)) = test x ++ REVERSE (test x) /\
  test (D1 tts) = (case tts of [] => [(); ()]
                   | (tt :: tts) => test (D1 tts) ++ test tt) /\
  test (E1 (x, y)) = REVERSE (test x) ++ test y
End
val _ = stdcheck test_def

Definition nested_num_in_list:
  nnil [] = 3 /\
  nnil ((_, 4) :: t) = nnil t /\
  nnil (h::t) = SND h + nnil t
End
val _ = stdcheck nested_num_in_list

val _ = export_theory();
