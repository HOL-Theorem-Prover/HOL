(* getopt.sml
 *
 * COPYRIGHT (c) 1998 Bell Labs, Lucent Technologies.
 *
 * See comments in GetOpt.sml
 *
 *)


structure GetOpt :> GetOpt =
  struct

    datatype 'a arg_order
      = RequireOrder
      | Permute
      | ReturnInOrder of string -> 'a

    datatype 'a arg_descr
      = NoArg of unit -> 'a
      | ReqArg of (string -> 'a) * string
      | OptArg of (string option -> 'a) * string

    type 'a opt_descr = {
        short : string,
        long : string list,
        desc : 'a arg_descr,
        help : string
      }

    datatype 'a opt_kind
      = Opt of 'a
      | NonOpt

    structure SS = Substring
    structure S = String


    (* helper functions *)
    fun sepBy (sep, []) = ""
      | sepBy (sep, x::xs) =
          concat (x::foldr (fn (elem,l) => sep::elem::l) [] xs)

    val breakeq = SS.splitl (fn #"=" => false | _ => true)


    (* formatting of options *)

    fun fmtShort (NoArg _) so = concat ["-", str so]
      | fmtShort (ReqArg (_,ad)) so = concat ["-", str so," ",ad]
      | fmtShort (OptArg (_,ad)) so = concat ["-", str so,"[",ad,"]"]

    fun fmtLong (NoArg _) lo = concat ["--",lo]
      | fmtLong (ReqArg (_,ad)) lo = concat ["--",lo,"=",ad]
      | fmtLong (OptArg (_,ad)) lo = concat ["--",lo,"[=",ad,"]"]

    fun fmtOpt {short=sos, long=los, desc=ad, help=descr} = (
          String.concatWith ", " (map (fmtShort ad) (S.explode sos)),
          String.concatWith ", " (map (fmtLong ad) los),
          descr)

  (* Usage information *)
    fun usageInfo {header, options} = let
          fun unlines l = sepBy ("\n", l)
          val fmtOptions = List.map fmtOpt options
          val (ms1, ms2) = foldl
                (fn ((e1,e2,_), (m1,m2)) => (
                    Int.max (size e1, m1),
                    Int.max (size e2, m2)
                  )) (0,0) fmtOptions
          val indent = StringCvt.padLeft #" " (ms1 + ms2 + 6)
          val pad = StringCvt.padRight #" "
          fun doEntry ((e1, e2, e3), l) = (
                case String.fields (fn #"\n" => true | _ => false) e3
                 of [] => concat["  ", pad ms1 e1, "  ", pad ms2 e2] :: l
                  | [e3] => concat["  ", pad ms1 e1, "  ", pad ms2 e2, "  ", e3] :: l
                  | fst::rest =>
                      concat["  ", pad ms1 e1, "  ", pad ms2 e2, "  ", fst]
                        :: List.foldr (fn (s, l) => (indent "" ^ s) :: l) l rest
                (* end case *))
          val table = List.foldr doEntry [""] fmtOptions
          in
            String.concatWith "\n" (header::table)
          end

    (* entry point of the library
     *)

    fun getOpt {argOrder, options : 'a opt_descr list, errFn} = let
       (* Some error handling functions *)
          fun errAmbig optStr = errFn(usageInfo{
                  header = concat[
                      "option `", optStr, "' is ambiguous; could be one of:"
                    ],
                  options = options
                })
          fun errReq (d, optStr) = errFn(concat[
                  "option `", optStr, "' requires an argument ", d
                ])
          fun errUnrec optStr = errFn(concat[
                  "unrecognized option `", optStr, "'"
                ])
          fun errNoArg optStr = errFn(concat[
                  "option `", optStr, "' does not allow an argument"
                ])
        (* handle long option
         * this is messy because you cannot pattern-match on substrings
         *)
          fun longOpt (subs, rest) = let
                val (opt, arg) = breakeq subs
                val opt' = SS.string opt
                val options = List.filter
                      (fn {long,...} => List.exists (S.isPrefix opt') long)
                        options
                val optStr = "--"^opt'
                fun long (_::(_::_), _, rest') = (
                      errAmbig optStr; (NonOpt, rest'))
                  | long ([NoArg a], x, rest') =
                      if (SS.isEmpty x)
                        then (Opt(a()),rest')
                      else if (SS.isPrefix "=" x)
                        then (errNoArg optStr; (NonOpt, rest'))
                        else raise Fail "long: impossible"
                  | long ([ReqArg(f,d)], x, []) =
                      if (SS.isEmpty x)
                        then (errReq(d, optStr); (NonOpt, []))
                      else if (SS.isPrefix "=" x)
                        then (Opt(f (SS.string (SS.triml 1 x))), [])
                        else raise Fail "long: impossible"
                  | long ([ReqArg(f,d)], x, rest' as (r::rs)) =
                      if (SS.isEmpty x)
                        then (Opt(f r), rs)
                      else if (SS.isPrefix "=" x)
                        then (Opt(f (SS.string (SS.triml 1 x))), rest')
                        else raise Fail "long: impossible"
                  | long ([OptArg(f,_)], x, rest') =
                      if (SS.isEmpty x)
                        then (Opt(f NONE), rest')
                      else if (SS.isPrefix "=" x)
                        then (Opt(f (SOME (SS.string (SS.triml 1 x)))), rest')
                        else raise Fail "long: impossible"
                  | long ([], _, rest') = (
                      errUnrec optStr; (NonOpt, rest'))
                in
                  long (map #desc options, arg, rest)
                end
        (* handle short option.  x is the option character, subs is the
         * rest of the option string, rest is the rest of the command-line
         * options.
         *)
          fun shortOpt (x, subs, rest) = let
                val options =
                      List.filter (fn {short,...} => Char.contains short x) options
                val ads = map #desc options
                val optStr = "-"^(str x)
                in
                  case (ads, rest)
                   of (_::_::_, rest1) => (errAmbig optStr; (NonOpt, rest1))
                    | ((NoArg a)::_, rest') =>
                        if (SS.isEmpty subs)
                          then (Opt(a()), rest')
                          else (Opt(a()), ("-"^(SS.string subs))::rest')
                    | ((ReqArg(f,d))::_, []) =>
                        if (SS.isEmpty subs)
                          then (errReq(d, optStr); (NonOpt, []))
                          else (Opt(f (SS.string subs)), [])
                    | ((ReqArg(f,_))::_, rest' as (r::rs)) =>
                        if (SS.isEmpty subs)
                          then (Opt(f r), rs)
                          else (Opt(f (SS.string subs)), rest')
                    | ((OptArg(f,_))::_, rest') =>
                        if (SS.isEmpty subs)
                          then (Opt(f NONE), rest')
                          else (Opt(f (SOME(SS.string subs))), rest')
                    | ([], rest') => (errUnrec optStr; (NonOpt, rest'))
                  (* end case *)
                end
          fun get ([], opts, nonOpts) = (List.rev opts, List.rev nonOpts)
            | get ("--"::rest, opts, nonOpts) = let
                val nonOpts = List.revAppend(nonOpts, rest)
                in
                  case argOrder
                   of ReturnInOrder f => (List.revAppend(opts, List.map f nonOpts), [])
                    | _ => (List.rev opts, nonOpts)
                  (* end case *)
                end
            | get (arg::rest, opts, nonOpts) = let
                val arg' = SS.full arg
                fun addOpt (Opt opt, rest) = get(rest, opt::opts, nonOpts)
                  | addOpt (NonOpt, rest) = get(rest, opts, arg::nonOpts)
                in
                  if (SS.isPrefix "--" arg')
                    then addOpt(longOpt (SS.triml 2 arg', rest))
                  else if (SS.isPrefix "-" arg') then
                    if SS.size arg' = 1 then
                      (errFn "Malformed option (-)"; get(rest, opts, nonOpts))
                    else
                      addOpt(shortOpt (SS.sub(arg', 1), SS.triml 2 arg', rest))
                  else (case argOrder
                     of RequireOrder => (List.rev opts, List.revAppend(nonOpts, arg::rest))
                      | Permute => get(rest, opts, arg::nonOpts)
                      | ReturnInOrder f => get(rest, f arg :: opts, nonOpts)
                    (* end case *))
                end
          in
            fn args => get(args, [], [])
          end (* getOpt *)

  end
