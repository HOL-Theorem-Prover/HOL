signature internal_functions =
sig

  exception HolmakeError of string

  type loc = {file : string, line : int}

  type diags = {info : string -> unit,
                warn : string -> unit,
                die  : string -> unit}

  val default_diags : diags

  val subst : (string * string * string) -> string
  val pcsubst : (string * string) -> string
  val patsubst : (string * string * string) -> string
  val pattern_match : string -> string -> string option
  val tokenize : string -> string list
  val find_unescaped : char list -> Substring.substring -> int option
  val tee : string * string -> string
  val wildcard : string -> string list
  val which : string -> string
  val function_call : diags ->
                      (string *
                       Substring.substring list *
                       (Substring.substring -> string) *
                       loc option) -> string
  val hol2fs : string -> string

end

(*
   [subst (from,to,on)] substitutes to for from in on, replacing all
   occurrences found during a left-to-right scan, and doing the replacements
   as they are found.  (I.e., subst("aa", "b", "aaa") returns "ba", despite
   the fact that "aaa" arguably contains two occurrences of "aa".

   [pcsubst(s,pat)] replaces every unescaped occurrence of "%" in pat with
   s.

   [pattern_match pat obj] attempts to match the pattern pat against
   obj.  A pattern is any string containing at most one unescaped %
   character.  (% and backslash characters can be escaped by preceding
   them with a back-slash character.  Other <back-slash character>
   pairs are left as they are.  This treatment of quoting is not the
   same as GNU make's; it would leave trailing \\ alone.)  %
   characters match any non-empty substring.  The result is NONE, if
   there is no match, or SOME s, where performing pcsubst(s,pat) gives
   back obj.

   If pat doesn't contain a % character, return SOME "", which is otherwise
   impossible, because of the requirement that matches be over non-empty
   strings.

   [patsubst(from,to,on)] tokenizes argument on into a list of
   strings, and then attempts to match pattern from against each.
   Where the pattern matches with SOME stem, that element of the list
   is replaced with pcsubst(stem,to).  Those elements that don't match
   are left alone.  The resulting list is sewn back together with
   single spaces.

   [tokenize s] returns the list of white-space separated components
   in s, but taking heed not to treat back-slash quoted spaces as
   white-space.  It preserves all quoting within the "tokens", meaning
   that spacify (tokenize sl) = sl, except that multiple spaces or
   TABs between tokens in sl will have been compressed into just one
   space on the LHS.

   [find_unescaped clist ss] searches ss for an unescaped occurrence of one
   of the elements clist.  If it returns SOME i, then sub(ss, i) is the
   first such character.  If it returns NONE, then there is no such
   character.

   [wildcard s] treats s as a "shell glob" pattern and matches it
   against files in the current hierarchy (i.e., relative file names
   are assessed against the current directory). The list of all files
   that match are returned. If the pattern doesn't match any files,
   the string is returned as is.

   [function_call diags (fnname, args, eval, loc)] evaluates the internal
   function fnname when applied to arguments args.  These args are not
   evaluated to strings to allow for functions (like if) that don't
   necessarily look at all of their arguments.  Evaluation is provided
   by the eval function.  The optional loc records the file and line at
   which the function call appears, and is used by the GNU make
   compatibility functions info/warning/error to prefix their messages.
   Note that this is the use site rather than the definition site of the
   variable in which the call appears (so immediately-expanded uses get
   the location of the assignment, while deferred uses get the location
   where the variable is mentioned).

   The diags record carries the side-effect targets used by the GNU
   make compatibility functions: $(info) writes to diags.info,
   $(warning) writes to diags.warn.  $(error) still raises
   HolmakeError directly, since callers (notably
   ReadHMF.find_includes0) catch that exception to identify and skip
   bogus Holmakefiles during pre-exec discovery.

   [default_diags] is a diags record whose info/warn write to
   TextIO.stdOut/stdErr and whose die writes to stderr and exits.
   For callers that don't have Holmake's chattiness machinery in
   scope (e.g. genscriptdep, selftests).

   [HolmakeError msg] is raised by $(error ...).  It is caught at
   Holmake's top level rather than going through the generic Fail
   handler so that abort messages keep their bare "file:line: ***"
   prefix.

   [hol2fs s] converts "HOL filename" s to a filename that will actually
   work on the machine.

*)
