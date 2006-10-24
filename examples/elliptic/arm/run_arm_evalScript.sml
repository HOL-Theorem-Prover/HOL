(* ========================================================================= *)
(* FILE          : run_arm_evalScript.sml                                    *)
(* DESCRIPTION   : Examples using arm_evalLib                                *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005-2006                                                 *)
(* ========================================================================= *)

(* interactive use:
  load "arm_evalLib";
*)

open HolKernel boolLib bossLib;
open Parse arm_evalLib;

val _ = new_theory "run_arm_eval";

(* ------------------------------------------------------------------------- *)

val max = valOf Int.maxInt;
val i2s = int_to_string;
val _ = wordsLib.pp_word_hex();
val _ = overload_on("sp", ``r13``);
val _ = overload_on("lr", ``r14``);
val _ = overload_on("pc", ``r15``);

(* ------------------------------------------------------------------------- *)

(* A rudimentary exception handler *)

val exc_mem = list_assemble empty_memory
  ["0x0: movs pc, #32",
   "label: b label",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #8",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #4"];

(* Initial general purpose register values *)

val reg = set_registers empty_registers
 ``[(pc,0x20w)]: (register # word32) list``;

(* Initial program status register values *)

val psr = set_status_registers empty_psrs
 ``[(CPSR,SET_NZCV (F,F,F,F) (SET_IFMODE F F usr 0w))]: (psr # word32) list``;

(* ------------------------------------------------------------------------- *)

fun hs n = "0x" ^ Arbnum.toHexString n;

local
  open Arbnum
  val twoexp32 = pow(two, fromInt 32)
  fun num2words2 n l =
    if n = zero then l else
      let val (q, r) = divmod(n, twoexp32) in
        num2words2 q ((hs r)::l)
      end
  fun words2num2 [] n = n
    | words2num2 (i::t) n = words2num2 t (fromInt i + (n * twoexp32))
in
  fun num2words s = rev (num2words2 s [])
  fun words2num l = words2num2 (rev l) zero
end;

fun num2wordsn n s =
  let val l = num2words s
      val ll = length l
  in
    if n < ll then
      List.take(l, n)
    else
      l @ List.tabulate(n - ll, fn _ => "0x0")
  end;

fun prefix_hd s [] = [s]
  | prefix_hd s (h::t) = (s ^ h)::t;

fun random_word l =
  words2num (Random.rangelist (0, max) (l, Random.newgen()));

(* ------------------------------------------------------------------------- *)

(*
val _ = wordsLib.mk_word_size (17 * 32);

fun mk_word544 n = wordsSyntax.mk_n2w (numLib.mk_numeral n, ``:i544``);

val a = random_word 17;
val b = random_word 17;

val eval_add17 = save_thm("eval_add17",
  EVAL (wordsSyntax.mk_word_add(mk_word544 a, mk_word544 b)));

val prog = list_assemble
  (assemble exc_mem "../code/add.s")
 (["0x20:\
   \mov sp, #0xA000",
   "mov r0, sp",
   "add r1, r0, #"^i2s(4 * 17),
   "add r2, r1, #"^i2s(4 * 17),
   "bl 0x8000"] @
   (prefix_hd "0xA000: "
    (num2wordsn 17 a)) @
    (num2wordsn 17 b));

val run_add17 = save_thm("run_add17", evaluate(max,prog,reg,psr));
*)

(* ------------------------------------------------------------------------- *)

(*
val p = Arbnum.fromString
  "68647976601306097149819007990813932172694353\
  \00143305409394463459185543183397656052122559\
  \64066145455497729631139148085803712198799971\
  \6643812574028291115057151";

val a = random_word 34;

val eval_srd521 = save_thm("eval_srd521",
  EVAL (numSyntax.mk_mod(numLib.mk_numeral a, numLib.mk_numeral p)));

val prog = list_assemble
  (assemble exc_mem "../code/srd521.s")
 (["0x20:\
   \mov sp, #0xA000",
   "mov r0, sp",
   "add r1, r0, #"^i2s(4 * 34),
   "bl 0x8000"] @
   (prefix_hd "0xA000: "
    (num2wordsn 34 a)));

val run_srd521 = save_thm("run_srd521", evaluate(max,prog,reg,psr));
*)

(* ------------------------------------------------------------------------- *)

(*
val _ = wordsLib.mk_word_size (18 * 32);

fun mk_word576 n = wordsSyntax.mk_n2w (numLib.mk_numeral n, ``:i576``);

val a = random_word 9;
val b = random_word 9;

val eval_mul9 = save_thm("eval_mul9",
  EVAL (wordsSyntax.mk_word_mul(mk_word576 a, mk_word576 b)));

val prog = list_assemble
  (assemble exc_mem "../code/mul9.s")
 (["0x20:\
   \mov sp, #0xA000",
   "mov r0, sp",
   "add r1, r0, #"^i2s(4 * 9),
   "add r2, r1, #"^i2s(4 * 9),
   "bl 0x8000"] @
   (prefix_hd "0xA000: "
    (num2wordsn 9 a)) @
    (num2wordsn 9 b));

val run_mul9 = save_thm("run_mul9", evaluate(max,prog,reg,psr));
*)

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
