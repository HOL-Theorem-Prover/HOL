(*
 * Foundational type/term, timing and lock helpers shared across the whole
 * Refute stack.
 *
 * This module deliberately depends only on the HOL kernel (Type, Term,
 * Thm), boolSyntax, combinSyntax and the Basis, so it can be loaded by
 * both the substrate layer (compiled for refuteTableZooTheory) and the
 * model-finder layer.
 * Layer-specific utilities live in Refute_ModelFinder_Util, which
 * re-exports these for the model-finder modules' convenience.
 *)

structure Refute_Util :> Refute_Util = struct
  fun same_type left right = Type.compare (left, right) = EQUAL

  val member_type = Lib.op_mem same_type
  val add_type = Lib.op_insert same_type

  (* Shared by callers that need distinct type-variable arguments, e.g.
     [register_codatatype] and [register_generator_family]: each checks
     its own well-formedness and delegates pairwise distinctness here. *)
  fun all_distinct_types tys =
    #2 (List.foldl (fn (ty, (seen, ok)) =>
      if ok andalso not (member_type ty seen) then (ty :: seen, true)
      else (seen, false)) ([], true) tys)

  val aconv_member = Lib.op_mem Term.aconv

  (* Full beta normal form.  Both layers need one -- the generator's
     [infer_fixed_argument] leaves redexes behind when it substitutes a
     closed value for a predicate parameter, and the model finder's
     encoder needs a redex-free term -- and two normalisers that must
     agree wherever a term crosses between them is one too many. *)
  fun beta_normalize term =
    if Term.is_abs term then
      let val (variable, body) = Term.dest_abs term
      in Term.mk_abs (variable, beta_normalize body) end
    else if Term.is_comb term then
      let
        val (function, argument) = Term.dest_comb term
        val function = beta_normalize function
        val argument = beta_normalize argument
      in
        if Term.is_abs function then
          beta_normalize (Term.beta_conv (Term.mk_comb (function, argument)))
        else
          Term.mk_comb (function, argument)
      end
    else
      term

  fun distinct_terms terms =
    List.rev (List.foldl (fn (term, result) =>
      if aconv_member term result then result else term :: result) [] terms)

  (* Left order is preserved; new right elements are appended in order. *)
  fun union_terms left right =
    List.rev (List.foldl (fn (term, result) =>
      if aconv_member term result then result else term :: result)
      (List.rev left) right)

  (* Function update [base(|point -> value|)].  Reconstruction in all three
     layers -- the SML substrate's generated code, narrowing's value
     rebuilder, and the model finder's renderer -- builds one. *)
  fun update_term point value base =
    Term.mk_comb (combinSyntax.mk_update (point, value), base)

  (* Universal closure, binding the free variables in textual order. *)
  fun close_free term =
    boolSyntax.list_mk_forall (Term.free_vars_lr term, term)

  (* A theorem as one closed proposition: hypotheses imply conclusion. *)
  fun theorem_term theorem =
    close_free (boolSyntax.list_mk_imp (Thm.hyp theorem, Thm.concl theorem))

  (* Spin-acquire a lock without blocking with interrupts masked:
     [Timeout.apply] cancels by raising an interrupt, which a masked block
     would never see.  Callers hold the mask of an enclosing
     [Thread_Attributes.uninterruptible] and pass its [restore]; only the
     waiting is unmasked, so the successful acquisition still happens
     masked and the caller installs its cleanup state before any interrupt
     can arrive. *)
  fun acquire_interruptibly restore try_lock =
    let
      fun acquire () =
        if try_lock () then ()
        else
          (restore (fn () => OS.Process.sleep (Time.fromReal 0.01)) ();
           acquire ())
    in
      acquire ()
    end

  (* Milliseconds since [start], for the statistics both the model finder
     and QC report.  A clock or overflow failure reports 0 rather than
     aborting the search it is only instrumenting. *)
  fun elapsed_msec start =
    LargeInt.toInt (Time.toMilliseconds (Time.- (Time.now (), start)))
    handle Interrupt => raise Interrupt | _ => 0

  (* Time left before [deadline], clamped at zero. *)
  fun remaining deadline =
    let val now = Time.now ()
    in if Time.>= (now, deadline) then Time.zeroTime
       else Time.- (deadline, now)
    end

  (* The [n]-element carrier type of refuteTheory. *)
  fun rf_type n =
    Type.mk_thy_type {Thy = "refute", Tyop = "rf" ^ Int.toString n, Args = []}
end
