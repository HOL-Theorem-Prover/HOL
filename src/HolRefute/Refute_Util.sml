(*
 * Foundational type/term, timing and lock helpers shared across the whole
 * Refute stack.
 *
 * This module deliberately depends only on the HOL kernel (Type, Term,
 * List), combinSyntax and the Basis, so it can be loaded by both the
 * substrate layer (compiled for refuteTableZooTheory) and the model-finder
 * layer.
 * Layer-specific utilities live in Refute_ModelFinder_Util, which
 * re-exports these for the model-finder modules' convenience.
 *)

signature REFUTE_UTIL = sig
  val same_type : Type.hol_type -> Type.hol_type -> bool
  val member_type : Type.hol_type -> Type.hol_type list -> bool
  val add_type :
    Type.hol_type -> Type.hol_type list -> Type.hol_type list
  val all_distinct_types : Type.hol_type list -> bool
  val aconv_member : Term.term -> Term.term list -> bool
  val beta_normalize : Term.term -> Term.term
  val distinct_terms : Term.term list -> Term.term list
  val union_terms : Term.term list -> Term.term list -> Term.term list
  val update_term : Term.term -> Term.term -> Term.term -> Term.term
  val acquire_interruptibly :
    ((unit -> unit) -> unit -> unit) -> (unit -> bool) -> unit
  val elapsed_msec : Time.time -> int
end

structure Refute_Util :> REFUTE_UTIL = struct
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
end
