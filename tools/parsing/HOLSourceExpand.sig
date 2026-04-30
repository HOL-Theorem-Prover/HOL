signature HOLSourceExpand = sig

val mkSemi: HOLSourceAST.dec list -> HOLSourceAST.dec list

val expandDec:
  { fileline: int -> HOLSourceAST.fileline,
    parseError: int * int -> string -> unit,
    quietOpen: bool } ->
  HOLSourceAST.dec -> HOLSourceAST.dec

end

(* ----------------------------------------------------------------------
    Overview
   ----------------------------------------------------------------------

    HOLSourceExpand is the macro-expansion stage of the source
    pipeline: it takes a parsed HOLSourceAST.dec carrying the HOL-
    specific surface forms (Theorem, Definition, Datatype, Inductive /
    CoInductive, Type, Overload, Quote, Theory, Resume, Finalise, the
    #(LINE=)/(FILE=) pragma variants, etc.) and rewrites it into pure
    SML by emitting calls to the HOL kernel and library functions that
    realise each construct.

    Every expansion is returned as a DecExpansion {orig, result}, so
    the original surface span is preserved alongside the synthesised
    declarations.  This lets HOLSourcePrinter print expansions while
    keeping line directives anchored to the original source positions.

    Inputs to expandDec:

      - fileline : int -> fileline
        Resolves a character offset to {file, line, col}.  Used to
        choose between location-tagged versions of the runtime
        helpers, e.g. boolLib.save_thm vs save_thm_at, Q.store_thm vs
        store_thm_at, TotalDefn.qDefine vs located_qDefine, depending
        on whether the source originates in a known file.
      - parseError : int * int -> string -> unit
        Reports any unrecognised or malformed attributes encountered
        during expansion (e.g. unknown keys on [attrs], unsupported
        argument shapes for [smlname], [induction], etc.).
      - quietOpen : bool
        When true, theory-level `open`s are wrapped between
        HOL_Interactive.start_open () and HOL_Interactive.end_open (),
        to suppress chatter from interactive sessions.

    Surface forms and what they expand to:

      Theorem foo[attrs]: q QED
          ~> val foo = Q.store_thm ("foo[attrs]", q, tac)
             (with proof tac wrapped in wrapTac so HOL exceptions
             surface as parse errors)
      Theorem foo[attrs] = e
          ~> val foo = boolLib.save_thm ("foo[attrs]", e)
      Definition foo[attrs]: q [Termination tac] End
          ~> val foo = TotalDefn.qDefine ("foo[attrs]", q, NONE|SOME tac)
             plus a magicBind for the induction theorem (foo_ind / _IND
             / _ind name guessed from foo_def / foo_DEF, overridable by
             [induction=name])
      Datatype: q End  ~>  val _ = bossLib.Datatype q
      [Co]Inductive id: q End
          ~> (id_rules, id_(co)ind, id_cases) = IndDefLib.xHol_reln
             ("id", split_quote); plus per-conjunct save_thm calls for
             each [~name] / [name] DefinitionLabel inside the quote
      Type id [attrs] = e / Overload id[attrs] = e
          ~> val _ = Parse.[temp_]{type_abbrev[_pp]
                                  | [inferior_]overload_on[_by_nametype]}
                       (id, e)
      Quote id [= e]: q End  ~>  val id = e q
      Theory foo[bare] [HOLAncestors / HOLLibs ...]
          ~> Theory.new_theory "foo"; Parse.set_grammar_ancestry [...];
             a sequence of `open`s grouped by qualified-vs-unqualified,
             with structure aliases for each [alias=...] entry, and
             optional HOL_Interactive open-bracketing
      EndTheory  ~>  Theory.export_theory () (with optional
                     Feedback.set_trace "TheoryPP.include_docs" 0
                     before, when [no_sig_docs] was set on Theory)
      Resume label[smlname=x, attrs]: tac QED
          ~> val x = markerLib.resume {label_name, suspension_name} tac
      Finalise id[attrs]
          ~> val id = markerLib.finalise_suspended_thm "id[attrs]"

    Pure-SML decls are walked recursively rather than rewritten:
    DecVal expands its expressions (treating top-level patterns
    specially -- a top-level bare expression DecExp e becomes
    `val it = e`, a non-top one becomes `val _ = e`), DecLocal /
    DecStructure / DecSignature / DecFunctor / DecInclude descend
    into their bodies, etc.  DecMosmlPrimVal becomes a vacuous
    val-binding (Moscow ML's prim_val syntax loses its body).
    DecBad turns into `val _ = raise Fail "malformed"`.

    Expressions go through expandExp.  The notable transformation is
    that SuccessorML "or-patterns" (Or {...}) are detected in
    binding/pattern positions and either expanded into multiple match
    arms (case / fn / handle), or rejected via parseError when they
    appear somewhere multiple arms cannot be synthesised (val
    bindings raise HasOrPat, which is caught and replaced with
    ExpBad).

    Quote handling.  expandQuote start stop toks builds the SML list
    of QUOTE / ANTIQUOTE fragments from the parsed qdecl list,
    handling both literal text spans and ^antiquotations.  For
    Inductive declarations, expandQuoteCore additionally splits the
    quote at DefinitionLabel boundaries so each conjunct can be saved
    under its own name with its own attributes.

    Helpers worth noting:

      - mkSemi : prepends a synthetic DecSemi to the head of a
        declaration list, anchored at the previous declaration's stop
        offset.  Exposed for HOLSourcePrinter to use when threading
        expansions back into the printer's stream.
      - magicBind, valPat, valWild, mkNameAttrs, mkLocString /
        mkLocString' : internal builders for the common output shapes,
        each parametrised by the position of the originating surface
        token so generated decls inherit a sensible source span.

    The result of expandDec preserves the AST shape and never rewrites
    structure : the orig-bearing DecExpansion wrapper is the only
    visible difference, and it carries enough information that
    consumers can choose to display either the original surface text
    or the elaborated SML.
   ---------------------------------------------------------------------- *)
