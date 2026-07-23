open Parse BasicProvers simpLib testutils

(* tests for diminish applying to constituents that are "built-in" to srw_ss
   from its point of definition *)
val _ = diminish_srw_ss ["COMBIN"]
val _ = shouldfail {checkexn = (fn Conv.UNCHANGED => true | _ => false),
                    printarg = fn _ => "diminish_srw_ss before 'realisation'",
                    printresult = thm_to_string,
                    testfn = SIMP_CONV (quietly srw_ss()) []}
                   “K T (x:'a)”

val _ = shouldfail {checkexn = (fn Conv.UNCHANGED => true | _ => false),
                    printarg = fn _ => "with_simpset_updates removes BETA_CONV",
                    printresult = thm_to_string,
                    testfn = with_simpset_updates
                               (fn ss0 => ss0 -* ["BETA_CONV"])
                               (fn t => SIMP_CONV (srw_ss()) [] t)}
                   “(λx. x /\ p) T”

val _ = convtest ("SIMP_CONV (srw_ss()) [] “p ∧ T”", SIMP_CONV (srw_ss()) [],
                  “p ∧ T”, “p:bool”)

val _ = convtest("above w/simpset_updates removing",
                 BasicProvers.with_simpset_updates
                   (simpLib.remove_simps ["AND_CLAUSES"])
                   (fn x => Conv.QCONV (SIMP_CONV (srw_ss()) []) x),
                   “p ∧ T”, “p ∧ T”)

val _ = convtest("Original again", SIMP_CONV (srw_ss()) [], “p ∧ T”, “p:bool”)

(* ==================================================================
   Regression for issue #2025: Context.restore must not rewind the
   kernelid allocation clock, nor the retire-mutation clock.  Both
   live in process-global Sref counters outside Context.t so that:

     (1) same_const on pre- vs post-restore constants of the same
         name is FALSE (soundness — the exploit constructed ⊢ F by
         collision), and

     (2) symtab_epoch() after a post-restore mutation is strictly
         greater than any value seen before (correctness — the
         ThmSetData / AncestryData / GrammarDeltas memoisation gates
         cannot false-positive after a restore).
   ================================================================== *)

local
  open boolSyntax Drule Term Thm Feedback
in

val _ = tprint "issue #2025 (soundness): Context.restore + redefinition"
val snap = Context.snapshot ()
val c_t = mk_var("issue2025_c", Type.bool)
val c_eq_t = new_definition ("issue2025_A_def", mk_eq (c_t, T))
val () = Context.restore snap
val c_f = mk_var("issue2025_c", Type.bool)
val c_eq_f = new_definition ("issue2025_B_def", mk_eq (c_f, F))
val const_t = lhs (concl c_eq_t)  (* pre-restore Const *)
val const_f = lhs (concl c_eq_f)  (* post-restore Const *)
val () =
    if not (same_const const_t const_f) then OK ()
    else die "same_const holds across Context.restore — exploit re-opened"

val _ = shouldfail {
    checkexn  = fn HOL_ERR _ => true | _ => false,
    printarg  = fn () => "TRANS across a restored constant must fail",
    printresult = thm_to_string,
    testfn    = fn () => TRANS (SYM c_eq_t) c_eq_f} ()

val _ = tprint "issue #2025 (correctness): retire clock is monotonic across restore"
(* Retirement events (Theory.delete_const, delete_type, and the
   internal `remove` triggered by a re-inserting collision) stamp
   retire_epoch from a process-global monotone counter, so
   memoisation gates that key off symtab_epoch cannot false-positive
   after Context.restore. *)
val snap2 = Context.snapshot ()
val _ = new_definition ("issue2025_re_D_def",
                        mk_eq (mk_var("issue2025_re_d", Type.bool), T))
val () = Theory.delete_const "issue2025_re_d"
val e_pre_restore =
    KernelSig.symtab_epoch (Context.termsig (Context.snapshot ()))
val () = Context.restore snap2
val _ = new_definition ("issue2025_re_D_def",
                        mk_eq (mk_var("issue2025_re_d", Type.bool), T))
val () = Theory.delete_const "issue2025_re_d"
val e_post_restore =
    KernelSig.symtab_epoch (Context.termsig (Context.snapshot ()))
val () =
    if e_post_restore > e_pre_restore then OK ()
    else die ("retire epoch not strictly monotone across restore: pre="
              ^ Int.toString e_pre_restore
              ^ " post=" ^ Int.toString e_post_restore)

end (* local *)
