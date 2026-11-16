(* Legacy-only parser/deletion matrix, shared with the pinned harness. *)
structure ExclusionParsing =
struct
open HolKernel Parse boolLib simpLib testutils LegacyFailures

fun run () = let
  val dummy = "parser matrix dummy"
  val atoms = [``parser_a:bool``,``parser_b:bool``,
               ``parser_c:bool``,``parser_d:bool``]
  val rules = map (fn tm => ASSUME (mk_eq (tm,``T``))) atoms
  val ghost = "parser_unknown_ancestor"
  val names = [("bool","parser_stem"),("bool","parser_stem.1"),
               ("bool","parser_stem.2"),(ghost,"dotted.part")]
  val ss = empty_ss ++ name_ss dummy empty_ssfrag ++
    rewrites_with_names
      (ListPair.mapEq (fn ((thy,n),th) => ({Thy=thy,Name=n},th))
         (names,rules))
  fun results label set deleted =
    List.app (fn ((tm,rule),gone) => let
      val th = during label (fn () => QCONV (SIMP_CONV set []) tm)
      val expected = if gone then tm else ``T``
      val _ = theorem label th
    in
      check (label ^ " full theorem")
        (aconv (concl th) (mk_eq (tm,expected)) andalso
         HOLset.equal (hypset th,if gone then HOLset.empty Term.compare
                                else hypset rule))
    end) (ListPair.zip (ListPair.zip (atoms,rules),deleted))
  val none = [false,false,false,false]
  val rows =
    [("parser_stem",[true,true,true,false]),
     (* Named rewrites acquire a .1 compilation suffix. This also
        selects the overlapping source named parser_stem.1. *)
     ("parser_stem.1",[true,true,false,false]),
     ("bool.parser_stem",[true,true,true,false]),
     ("bool.parser_stem.2",[false,false,true,false]),
     (ghost ^ ".dotted.part",[false,false,false,true]),
     ("bool$parser_stem",none), ("parser_stem_tail",none),
     ("parser_stem.",none), (".1",none), ("a..1",none),
     ("",none), ("bool.missing",none), ("missing",none)]
  fun row (name,deleted) = let
    val label = "parse " ^ name
    val literal = during (label ^ " Excl")
      (fn () => ss && [Excl name,Excl name])
    val operator = during (label ^ " -*") (fn () => ss -* [name,name])
  in
    results (label ^ " Excl") literal deleted;
    results (label ^ " -*") operator deleted;
    results (label ^ " Excl replay")
      (remove_ssfrags [dummy] literal) deleted;
    results (label ^ " -* replay")
      (remove_ssfrags [dummy] operator) deleted
  end
  fun bad (name,message) = let
    fun rejected (label,f) = let
      val outcome = during label (fn () => (f (); NONE)
        handle e => SOME e)
      val _ = case outcome of SOME e => exception_observations label e
                            | NONE => observe (label ^ ".exception") "none"
    in
      check label (case outcome of SOME (HOL_ERR err) =>
        Feedback.top_function_of err = "-*" andalso
        Feedback.message_of err = message | _ => false)
    end
  in
    List.app rejected
      [("bad Excl " ^ name,fn () => ignore (ss && [Excl name])),
       ("bad -* " ^ name,fn () => ignore (ss -* [name]))]
  end
  val _ = results "parser setup" ss none
  val _ = List.app row rows

  (* Rewrite suffixes select descendants; dprocs instead use the original
     complete string, even when that string parses as a qualified rule. *)
  val dnames = ["parser_stem","parser_stem.1","parser_stem.10",
                "parser_stem_tail","bool.parser_stem",
                ghost ^ ".dotted.part","bool$parser_stem"]
  val calls = ref ([] : string list)
  fun dproc name = dproc_ss (Traverse.REDUCER
    {name=SOME name,initial=Fail "parser dproc context",
     addcontext=fn (ctxt,_) => ctxt,
     apply=fn _ => fn tm => (calls := name :: !calls; NO_CONV tm)})
  val dset = List.foldl (fn (name,set) => set ++ dproc name)
    (empty_ss ++ name_ss dummy empty_ssfrag) dnames
  fun drow name = let
    fun result (label,set) = let
      val _ = calls := []
      val th = during label (fn () => QCONV (SIMP_CONV set []) (hd atoms))
      (* Preserve actual order as well as the membership assertion below. *)
      val _ = observe (label ^ ".callback-order")
        (String.concatWith ";" (rev (!calls)))
      val observed = Listsort.sort String.compare (!calls)
      val expected = Listsort.sort String.compare
        (List.filter (fn n => n <> name) dnames)
      val _ = observe (label ^ ".callbacks") (String.concatWith ";" observed)
    in
      check label (observed = expected andalso null (hyp th) andalso
        aconv (concl th) (mk_eq (hd atoms,hd atoms)))
    end
    val literal = during ("dproc Excl " ^ name)
      (fn () => dset && [Excl name,Excl name])
    val operator = during ("dproc -* " ^ name)
      (fn () => dset -* [name,name])
  in
    List.app result
      [("dproc exact Excl " ^ name,literal),
       ("dproc exact -* " ^ name,operator),
       ("dproc exact replay " ^ name,remove_ssfrags [dummy] literal)]
  end
  val _ = List.app drow dnames
  val _ = List.app bad
    [(ghost ^ ".parser_stem","bad theory name: " ^ ghost),
     ("dotted.part","bad theory name: dotted"),
     (".parser_stem","bad theory name: "),
     ("a.b.c.d","User key has too many dots")]

  (* A genuine current-theory change, not just a changed ancestry list.
     The first theory is not exported: the second must reject its strict
     two-component names on replay. Restore both naming contexts in turn. *)
  val saved = Context.snapshot ()
  fun theories () = let
    val _ = new_theory "parserMatrixFirst"
    val first = Theory.current_theory ()
    val _ = Theory.link_parents ("parserMatrixAncestor","selftest") []
    val named = empty_ss ++ name_ss dummy empty_ssfrag ++
      rewrites_with_names [({Thy="parserMatrixAncestor",Name="r"},hd rules)]
    val name = "parserMatrixAncestor.r"
    val literal = named && [Excl name]
    val operator = named -* [name]
    val present = Context.snapshot ()
    val _ = Context.restore saved
    val _ = new_theory "parserMatrixSecond"
    val _ = check "parser replay really changed current theory"
      (Theory.current_theory () <> first)
    fun replay (label,set,should_fail) = let
      val outcome = during label (fn () =>
        (ignore (remove_ssfrags [dummy] set); NONE) handle e => SOME e)
      val _ = case outcome of SOME e => exception_observations label e
                            | NONE => ()
    in
      check label (if should_fail then
        case outcome of SOME (HOL_ERR err) =>
          String.isSubstring "bad theory name" (Feedback.message_of err)
        | _ => false else not (isSome outcome))
    end
    val _ = replay ("new theory strict Excl replay",literal,true)
    val _ = replay ("new theory strict -* replay",operator,true)
    val _ = Context.restore present
    val _ = replay ("restored theory Excl replay",literal,false)
    val _ = replay ("restored theory -* replay",operator,false)
  in () end
  val _ = Portable.finally (fn () => Context.restore saved) theories ()
in () end
end
