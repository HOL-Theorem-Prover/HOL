(* Installs `LSPExtension.dbSearch', which answers the question `M-h M'
   asks in `hol-mode': given some selectors, which theorems match?

   `DB.selectDB' already does the searching, and already combines
   selectors by narrowing rather than widening -- `"ASSOC"' and
   `'arithmetic'' together ask for the theorems of `arithmetic' whose
   names mention ASSOC, not for the union.  What is here is reading the
   quoting the user typed and turning what comes back into something a
   client can lay out.

   Reading the quoting here rather than in each client is deliberate:
   the same thing typed into emacs and into VS Code should ask the same
   question.  How the answers *look* is the client's business, which is
   why a statement travels as a pretty tree rather than as a string. *)

local
  fun unquote s = String.substring (s, 1, String.size s - 2)
  fun wrappedBy c s =
    String.size s >= 2 andalso String.sub (s, 0) = c
    andalso String.sub (s, String.size s - 1) = c

  fun locFile loc =
    case loc of
      DB.Located {scriptpath, ...} =>
        (SOME (holpathdb.subst_pathvars scriptpath) handle _ => NONE)
    | DB.Unknown => NONE
  fun locLine loc =
    case loc of DB.Located {linenum, ...} => linenum | DB.Unknown => 0

  (* A selector as the user wrote it.  Single quotes name a theory,
     double quotes a fragment of a theorem's name, and anything else is
     a term pattern -- parsed here, in the session that has the bound
     file's ancestry loaded and so its grammar, which is the only place
     the user's own notation means what they meant by it.

     A pattern's free variables are wildcards, `DB.selectDB' matching up
     to instantiation, so `f (g x)' finds every theorem with a nested
     application in it. *)
  fun selector s =
    if wrappedBy #"'" s then DB.SelTHY (unquote s)
    else if wrappedBy #"\"" s then DB.SelNM (unquote s)
    else DB.SelTM (Parse.Term [QUOTE s])

  fun take 0 _ = []
    | take _ [] = []
    | take n (x :: xs) = x :: take (n - 1) xs

  fun result ((thy, nm), (th, cls, loc)) : LSPExtension.search_result = {
    name = nm, theory = thy, class = DB_dtype.class_toString cls,
    statement = Hol_pp.pp_thm th,
    file = locFile loc, line = locLine loc}
in

val () = LSPExtension.dbSearch := (fn {selectors, limit} => let
  val given = List.filter (fn s => s <> "") selectors
  in
    if null given then []
    else take limit (List.map result (DB.selectDB (List.map selector given)))
  end
  (* A term pattern that does not parse, or a name search whose regexp
     `DB' rejects, is a question rather than a fault: answer nothing and
     let the user retype it. *)
  handle _ => [])

end
