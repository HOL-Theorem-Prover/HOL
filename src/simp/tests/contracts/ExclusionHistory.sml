(* Ordinary-engine exclusion history contracts, called by the normal
   exclusion-contracts target. *)
structure ExclusionHistory =
struct
open HolKernel Parse boolLib simpLib testutils
open LegacyFailures

fun fragment_batch_checks () = let
  val filler = List.tabulate (64, fn i => "keep fragment " ^ Int.toString i)
  val missing = List.tabulate (16, fn i => "missing fragment " ^ Int.toString i)
  val names = "drop first" :: "" :: "drop last" :: "drop first" :: missing
  val order = SOME "drop last" :: NONE :: SOME "" :: map SOME filler @
              [SOME "drop first", SOME "drop last"]
  fun fragment NONE = empty_ssfrag
    | fragment (SOME name) = name_ss name empty_ssfrag
  val frags = map fragment order
  fun names_of fs = map (#name o dest_ssfrag) fs
  val (selected,remaining) = partition_ssfrags names frags
  val _ = check "large fragment partition preserves each side's order"
    (names_of selected = map SOME ["drop last","","drop first","drop last"]
     andalso names_of remaining = NONE :: map SOME filler)
  val ss = mk_simpset frags
  val kept = remove_ssfrags names ss
  val _ = check "large fragment removal includes anonymous and empty names"
    (names_of (ssfrags_of kept) = map SOME (List.rev filler))
in
  check "large missing fragment batch reports UNCHANGED"
    ((remove_ssfrags missing ss; false) handle Conv.UNCHANGED => true)
end

fun run () = let
  val _ = fragment_batch_checks ()
  val dummy = "legacy replay dummy"
  val input = ``replay_legacy_p:bool``
  val rule = ASSUME ``replay_legacy_p:bool = T``
  val fragment = rewrites_with_names
    [({Thy="bool",Name="replay_legacy_rule"},rule)]
  val base = empty_ss ++ name_ss dummy empty_ssfrag
  fun add ss = ss ++ fragment
  fun replay ss = remove_ssfrags [dummy] ss
  fun result label ss expected = let
    val th = during label (fn () => QCONV (SIMP_CONV ss []) input)
    val _ = theorem label th
  in
    check (label ^ " full theorem")
      (aconv (concl th) (mk_eq (input,expected)) andalso
       HOLset.equal (hypset th,
         if aconv expected input then HOLset.empty Term.compare
         else hypset rule))
  end
  val qualified = "bool.replay_legacy_rule"
  val deleted = add base && [Excl qualified,Excl qualified]
  val _ = result "repeated strict deletion direct" deleted input
  val _ = result "repeated strict deletion replay" (replay deleted) input
  val added_later = add (base && [Excl qualified,Excl "unmatched_replay"])
  val _ = result "unmatched deletion before addition direct" added_later ``T``
  val _ = result "unmatched deletion before addition replay"
    (replay added_later) ``T``
  val interleaved = add (add base && [Excl qualified])
  val _ = result "addition after deletion direct" interleaved ``T``
  val _ = result "addition after deletion replay" (replay interleaved) ``T``
  val after = interleaved && [Excl "unmatched_replay",Excl qualified]
  val _ = result "interleaved add delete direct" after input
  val _ = result "interleaved add delete replay" (replay after) input
  val direct = add base -* [qualified,"unmatched_replay",qualified]
  val _ = result "strict operator batch replay" (replay direct) input

  (* This temporary ancestor is absent in the earlier snapshot. Legacy
     strict dotted replay must ask the current ancestry, not use the
     pattern cached at initial application. *)
  val saved = Context.snapshot ()
  fun context_checks () = let
    val thy = "strictHistoryPairedFixture"
    val _ = Theory.link_parents (thy,"selftest") []
    val named = base ++ rewrites_with_names
      [({Thy=thy,Name="replay_legacy_rule"},rule)]
    val name = thy ^ ".replay_legacy_rule"
    val literal = named && [Excl name]
    val operator = named -* [name]
    val present = Context.snapshot ()
    val _ = result "strict dotted deletion with ancestor"
      (replay literal) input
    val _ = Context.restore saved
    fun rejected label ss = let
      val outcome = (replay ss; NONE) handle e => SOME e
      val _ = case outcome of
          SOME e => exception_observations label e
        | NONE => observe (label ^ ".exception") "none"
    in
      check label (case outcome of
          SOME (HOL_ERR err) =>
            String.isSubstring "bad theory name" (Feedback.message_of err)
        | _ => false)
    end
    val _ = rejected "strict Excl replay after context restore" literal
    val _ = rejected "strict operator replay after context restore" operator
    val _ = Context.restore present
    val _ = result "strict replay after restoring ancestor"
      (replay literal) input
  in () end
  val _ = Portable.finally (fn () => Context.restore saved) context_checks ()
in () end
end
