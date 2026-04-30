signature AttributeSyntax =
sig

  val mk_strsafe : string -> string
  val bslash_escape : char -> string
  val bslash_escape_s : string -> string
  val dest_ml_thm_binding : string -> {keyword: string, name : string,
                                       name_attr_original : string,
                                       attributes : string list}
  val dest_name_attrs : string -> string * string list
  val key_vallist : string list -> (string * string list) list
  val mk_tacmodifier_string : (string * string list) list -> string

  type ('a,'b) gtm =
       {values : string list -> 'b, combine : 'a * 'a -> 'a, null: 'a,
        perkey : string -> 'b -> 'a}
  val gen_mktm : ('a,'b) gtm -> (string * string list) list -> 'a

end

(* ----------------------------------------------------------------------
    Overview
   ----------------------------------------------------------------------

    AttributeSyntax handles the bracketed attribute list that
    decorates the HOL declaration keywords (Theorem, Definition,
    Datatype, Inductive / CoInductive, Type, Overload, Theory,
    Resume, Finalise), the entries of a Theory header
    (HOLAncestors / HOLLibs), and the inline DefinitionLabel
    introducers `[name[attrs]:]` inside Definition / Inductive
    quotations, parsing strings of the shape

      Theorem foo[simp, exclude_simps=A B, exclude_frags=Cong]
      Definition foo[induction=foo_strong_ind]: ... End
      Overload "≤"[notation]

    into their constituent parts and emitting the SML wrapper code
    that realises the tactic-modifying attributes.

    Parsing entry points:

      - dest_ml_thm_binding : string ->
          {keyword, name, name_attr_original, attributes}
        Splits a binding header into the leading keyword (a run of
        alphabetic characters), the bound name, the unparsed
        name+attribute substring (kept verbatim for later
        regeneration), and the list of attribute strings inside the
        square brackets.
      - dest_name_attrs handles the name+brackets portion; it accepts
        either a bare ML identifier or a double-quoted name.  The
        quoted form is used at the call sites that allow names
        containing characters not valid in an SML identifier, such as
        Unicode or symbolic operators (e.g. Type / Overload); inside
        such quotes square brackets are part of the name rather than
        attribute delimiters.  The name is passed through mk_strsafe.
      - key_vallist parses each individual attribute of form
        `key = v1 v2 ...` into a (key, [v1, v2, ...]) pair, splitting
        values on whitespace (not on `|`); attributes without `=` come
        back with an empty value list.

    Emission entry points:

      - mk_tacmodifier_string : (string * string list) list -> string
        Renders an attribute alist as an SML expression of the form

          BasicProvers.with_simpset_updates (f1 o f2 o ... o (fn x => x))

        where each fi corresponds to one (key, vals) pair.  The keys
        `exclude_simps` and `exclude_frags` are renamed to
        `simpLib.remove_simps` / `simpLib.remove_ssfrags`; other keys
        pass through unchanged.  The empty alist returns "".
      - gen_mktm is the generic fold underlying the above: it takes a
        gtm record of {values, combine, null, perkey} callbacks and
        applies them right-fold-style across the alist.  Exposed so
        callers can produce other attribute-driven artefacts with the
        same surface syntax.

    String-safety helpers:

      - mk_strsafe escapes every non-printable character in a string as
        \NNN (three-digit decimal byte).  Used on parsed names so that
        downstream code generation produces lexable ML strings.
      - bslash_escape / bslash_escape_s expose the same \NNN encoding
        for a character or for the first character of a string.
   ---------------------------------------------------------------------- *)
