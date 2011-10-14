(*****************************************************************************)
(* Information and trouble shooting guide for encoding to ACL2.              *)
(*                                                                           *)
(*    Functions are encoded using the translate_..._function functions, and  *)
(*    should be used in order of definition. Eg, if the function f calls the *)
(*    function g, then g should be translated before f. Additionally, if     *)
(*    f takes as argument a type t, then a 'recognition' function must be    *)
(*    generated for t before it can be used. The function,                   *)
(*    flatten_recognizers is used to do this.                                *)
(*                                                                           *)
(* Trouble shooting:                                                         *)
(*    The trace is registered under 'functionEncodeLib.Trace' and exceptions *)
(*    are best viewed using 'translate_... handle e => Raise e'.             *)
(*                                                                           *)
(*    The two common reasons for the encoding process to fail are:           *)
(*        Missing rewrite: A function that is relied upon by the function    *)
(*                         being encoded has not been translated yet.        *)
(*           In the simplest case this may be solved by translating the      *)
(*           missing function, or flattening the recognizer for the required *)
(*           type. If the function may not be translated automatically,      *)
(*           then it may be translated by hand and added using:              *)
(*           functionEncodeLib.add_standard/conditional_rewrite.             *)
(*           Example:                                                        *)
(*               If we translate 'DIVMOD' without previously translating     *)
(*               'findq' we get the error:                                   *)
(*               Exception: No rewrite matched the following:                *)
(*                 Term: nat (findq (1,FST ..., SND ...))                    *)
(*                 Assumptions: [ [.]                                        *)
(*        Rewrite cannot be applied: This is characterised by a rewrite      *)
(*                         *nearly* applying in the trace log.               *)
(*           In some cases this can be solved by provided an extra theorem.  *)
(*           For example, the if the rewrite for DIV fails under the         *)
(*           assumptions:                                                    *)
(*               [|- ~(a = 0), ... ]  ``nat (x DIV a)``                      *)
(*           We can solve this by adding the extra theorem:                  *)
(*               |- ~(a = 0) ==> 0 < a                                       *)
(*           To match the theorem:                                           *)
(*               |- 0 < a ==> (nat (b DIV a) = ...)                          *)
(*                                                                           *)
(*    The translation of under-specified recursive functions (eg. SEG) is    *)
(*    particularly troublesome. All constructors in limits must be given     *)
(*    in a POSITIVE form, eg:                                                *)
(*          ?x y. argument = x :: y   rather than    ~(argument = [])        *)
(*    For a recursive function we must therefore prove two theorem forms.    *)
(*    Firstly, that the limit is correct, and secondly, that it is preserved *)
(*    across recursive calls:                                                *)
(*        1) : |- a + b <= LENGTH c ==> ~((?n. a = SUC n) /\ (c = []))       *)
(*        2) : |- (?d. a = SUC d) /\ (b = 0) /\                              *)
(*    	          (?x y. c = x :: y) /\ a + b <= LENGTH c ==>                *)
(*    	                            PRE a + 0 <= LENGTH (TL c)               *)
(*    Recursive calls are characterised by the limit being applied to        *)
(*    destructed arguments (PRE and TL). For a given type, t, these can be   *)
(*    found by using the function:                                           *)
(*        get_coding_theorem_precise ``:sexp`` t "destructors"               *)
(*                                                                           *)
(*****************************************************************************)

signature acl2encodeLib =
sig
    include Abbrev

(*****************************************************************************)
(* print_all_defs_mbe/standard :                                             *)
(*    Prints all definitions, up until the definition given, to a file.      *)
(*    The _mbe version uses the form:                                        *)
(*        (defun f (x) (declare (xargs :guard P))                            *)
(*                 (must-be-equal (if P body bottom) body))                  *)
(*                                                                           *)
(*    This has the advantage that functions run must faster. However, ACL2   *)
(*    is occasionally unable to prove termination / verify guards. This will *)
(*    hopefully be resolved soon...                                          *)
(*                                                                           *)
(*****************************************************************************)

    val print_all_defs_mbe : string -> thm -> unit
    val print_all_defs_standard : string -> thm -> unit

(*****************************************************************************)
(* set_destructors : thm list -> unit                                        *)
(*    Set the destructors for a given type to the theorems given.            *)
(*    These theorems should be of the form: |- D (C a b c...) = b ...        *)
(*                                                                           *)
(*    This function can be used before or after initialise_type is called.   *)
(*    However, if functions are translated using the destructors then the    *)
(*    destructors provided, eg. D, MUST have been translated beforehand.     *)
(*                                                                           *)
(*****************************************************************************)

    val set_destructors : thm list -> unit

(*****************************************************************************)
(* initialise_type :                                                         *)
(*    Initialises a type so that functions over it can be translated to ACL2 *)
(*    This generates the following functions:                                *)
(*          map, all :                                                       *)
(*               The standard map and all functions, these can be viewed     *)
(*               using: polytypicLib.get_source_function_def hol_type "map"  *)
(*          encode, decode, detect, fix :                                    *)
(*               These functions form the basis of the translation and may   *)
(*               be viewed using:                                            *)
(*               polytypicLib.get_coding_function_def ``:sexp``              *)
(*                                               hol_type "fix"              *)
(*    It also generates a number of theorems for use in the encoding         *)
(*    process, for more information see the function definition itself and   *)
(*    the function encodeLib.encode_type.                                    *)
(*                                                                           *)
(* Usage:                                                                    *)
(*    This function should be used to encode types added via hol_datatype.   *)
(*    Failure to do so may introduce unexpected errors into the translation  *)
(*    process.                                                               *)
(*                                                                           *)
(*****************************************************************************)

    val initialise_type : hol_type -> unit

(*****************************************************************************)
(* translate_simple/conditional/limit_function :                             *)
(*     These functions translate non-polymorphic definitions that do not use *)
(*     finite cartesian products. The encoding process is as follows:        *)
(*         a) Convert to clause form, using                                  *)
(*            functionEncodeLib.clause_to_case                               *)
(*         b) Define an analogue definition using                            *)
(*            functionEncodeLib.mk_analogue_definition                       *)
(*         c) Rewrite the definition using:                                  *)
(*            functionEncodeLib.complete_analogue and                        *)
(*            functionEncodeLib.PROPAGATE_ENCODERS_CONV                      *)
(*                                                                           *)
(* Usage:                                                                    *)
(*    Each function takes an associative list, mapping function constants to *)
(*    names for the translated function. For example:                        *)
(*        [(``LAST``,"last_translated")]                                     *)
(*    Lists are used throughout to support mutually recursive function       *)
(*    definitions.                                                           *)
(*                                                                           *)
(*    The first of these functions should be used for simple definitions     *)
(*    which are fully specified (do not have any missing clauses) and do not *)
(*    rely upon any functions which are not fully specified.                 *)
(*                                                                           *)
(*    The second of these functions should be used when the first fails,     *)
(*    for definitions which rely upon under-specified functions, but which   *)
(*    are themselves fully specified. Examples of such functions are those   *)
(*    relying on DIV, HD, TL etc...                                          *)
(*        The second argument to this function is then a list of helper      *)
(*    theorems. For example, if a call to HD is guarded by '~(x = [])`, then *)
(*    since the rewrite (|- (?a b. l = a::b) ==> (encode (HD l) = ...))      *)
(*    relies upon CONS instead, the theorem:                                 *)
(*        |- ~(x = []) ==> (?a b. x = a :: b)                                *)
(*    should be provided. See the examples in testACL2encoding for more      *)
(*    information.                                                           *)
(*                                                                           *)
(*    The final function should be used for definitions which are under      *)
(*    specified. This takes an additional argument specifying the ranges     *)
(*    under which the function may be translated, eg:                        *)
(*       [(``LAST``,[(``\x. (?a b. x = a :: b)``)])]                         *)
(*    NOTE: The system is designed to work with constructors given           *)
(*          POSITIVELY, eg: ?a b. x = a :: b, rather than, ~(x = []).        *)
(*          This form (with arguments existentially quantified in an LR      *)
(*          fashion) should be used wherever possible.                       *)
(*                                                                           *)
(*****************************************************************************)

    val translate_simple_function
    	: (term * string) list -> thm -> thm
    val translate_conditional_function
    	: (term * string) list -> thm list -> thm -> thm
    val translate_limit_function
    	: (term * string) list ->
	  (term * term list) list -> thm list -> thm -> thm

(*****************************************************************************)
(* translate_simple/conditional/limit_polymorphic_function :                 *)
(*     These functions work in exactly the same way as the non-polymorphic   *)
(*     varieties, except they take one extra argument: a map fusion theorem  *)
(*     for each mutually recursive function involved.                        *)
(*                                                                           *)
(*     For a simple, or conditional, function, only the following form of    *)
(*     theorem need be supplied:                                             *)
(*         |- f (map g x) (map h y) ... = map g h (f x y)                    *)
(*     The 'map' functions are introduced during the encoding of each type,  *)
(*     and may be retrieved using polytypicLib.get_source_function_def. This *)
(*     means that such functions may not be encoded until initialise_type    *)
(*     has been called.                                                      *)
(*                                                                           *)
(*     In the case of a limited function, eg. LAST, the fusion theorem can   *)
(*     only be of the form:                                                  *)
(*         |- (?a b. x = a :: b) ==> (LAST (MAP f x) = f (LAST x))           *)
(*     In this case, we must also supply a fusion theorem for CONS, to the   *)
(*     list of theorems:                                                     *)
(*         |- (?a b. x = a :: b) ==> (?a b. MAP f x = a :: b)                *)
(*     This will be the case with all functions with limit range.            *)
(*                                                                           *)
(*     Note: For functions which are 'partially' polymorphic, eg. they use   *)
(*     a type such as :'a + num, the constant I may be used as the map       *)
(*     function for a ground type (eg. num).                                 *)
(*                                                                           *)
(*****************************************************************************)

    val translate_simple_polymorphic_function
    	: (term * string) list -> (term * thm) list -> thm -> thm
    val translate_conditional_polymorphic_function
    	: (term * string) list -> (term * thm) list -> thm list -> thm -> thm
    val translate_limit_polymorphic_function
    	: (term * string) list ->
	  (term * thm) list -> (term * term list) list -> thm list -> thm -> thm

(*****************************************************************************)
(* translate_simple/conditional/limit/recursive_fcp_function :               *)
(*    These functions are designed to work with functions that use           *)
(*    finite cartesian products or words (see wordsTheory, fcpTheory).       *)
(*                                                                           *)
(*    The encoding process for such functions is subtly different to that    *)
(*    used for standard functions. In this case, a prospective term is found *)
(*    to represent the encoded function, and a function defined to match it  *)
(*    using functions in Defn. This means that in the case of recursive      *)
(*    definitions, two tactics must be supplied. The first to prove that the *)
(*    definition terminates, and the second to prove the propagation theorem.*)
(*                                                                           *)
(*    The first tactic supplied must provide a well-founded relation over    *)
(*    sexp that demonstrates that the function terminates. The tactic:       *)
(*        ENCODE_WF_REL_TAC : term frag list -> tactic                       *)
(*    is designed to act as WF_REL_TAC, except the relation is combined with *)
(*    encoding functions to produce a relation over s-expressions.           *)
(*    This may be used in conjunction with:                                  *)
(*        FULL_CHOOSE_DETECT : tactic                                        *)
(*    Given the assumption '|- detect x' this tactic replaces 'x' with       *)
(*    'encode y'. Also useful, may be the theorems:                          *)
(*        polytypicLib.generate_coding_theorem ``:sexp``                     *)
(*                "encode_decode_map", "encode_decode", "encode_detect"...   *)
(*                                                                           *)
(*****************************************************************************)

    val translate_simple_fcp_function
        : string -> thm -> thm
    val translate_conditional_fcp_function
    	: string -> thm list -> thm -> thm
    val translate_limit_fcp_function
    	: string -> term list -> thm list -> thm -> thm
    val translate_recursive_fcp_function
        : string -> term list -> thm list -> thm ->
  	  thm list -> tactic -> (thm -> thm -> tactic) -> thm

(*****************************************************************************)
(* flatten_[fcp]_recognizers :                                               *)
(*     Creates functions to 'recognise' the type, suitable for export to     *)
(*     ACL2. This *must* be used before attempting to translate functions    *)
(*     that rely on untranslated types.                                      *)
(*                                                                           *)
(* usage:                                                                    *)
(*     Both functions require a 'naming' function to produce names for       *)
(*     recognizers for the types involved. It should be noted that ALL       *)
(*     types in [nested] mutual recursion with the type given will have      *)
(*     functions defined for them.                                           *)
(*                                                                           *)
(*****************************************************************************)

    val flatten_recognizers
    	: (hol_type -> string) -> hol_type -> thm list
    val flatten_fcp_recognizers
    	: (hol_type -> string) -> hol_type -> thm list

(*****************************************************************************)
(* Tactics to assist proof of recursive FCP functions:                       *)
(*                                                                           *)
(* ENCODE_WF_REL_TAC :                                                       *)
(*    Given a goal of the form: ?R. WF R /\ .... and                         *)
(*    a relation 'R', ENCODE_WF_REL_TAC instantiates the existential in the  *)
(*    goal with the term: ``inv_image R encode``.                            *)
(*                                                                           *)
(* FULL_CHOOSE_DETECT_TAC :                                                  *)
(*           A u {detect x} ?- G                                             *)
(*    ------------------------------------- FULL_CHOOSE_DETECT_TAC           *)
(*    A[encode x' / x] ?- G [encode x' / x]                                  *)
(*                                                                           *)
(*****************************************************************************)

    val ENCODE_WF_REL_TAC : term frag list -> tactic
    val FULL_CHOOSE_DETECT_TAC : tactic

(*****************************************************************************)
(* For a ground term:                                                        *)
(*     ONEONE_DECENC_THM t = |- ONEONE (decode_t o encode_t)                 *)
(*     ONEONE_ENC_THM t    = |- ONEONE (encode_t : t -> sexp)                *)
(*                                                                           *)
(*****************************************************************************)

    val ONEONE_DECENC_THM : hol_type -> thm
    val ONEONE_ENC_THM    : hol_type -> thm

    val Raise : exn -> 'a
end