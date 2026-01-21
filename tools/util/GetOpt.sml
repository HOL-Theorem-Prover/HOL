(* getopt.sml
 *
 * COPYRIGHT (c) 2016 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
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

    val breakAtEq = SS.splitl (fn #"=" => false | _ => true)

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
        (* handle long option; `subs` is the command-line flag (minus the "--" prefix)
         * and `rest` are the rest of the command-line arguments.
         *)
          fun longOpt (subs, rest) = let
                val (opt, arg) = breakAtEq subs
                val opt' = SS.string opt
                val optStr = "--"^opt'
              (* handle the selected options *)
                fun handleLong argDesc = (case (argDesc, rest)
                       of (NoArg act, _) => if (SS.isEmpty arg)
                              then (Opt(act()), rest)
                            else if (SS.isPrefix "=" arg)
                              then (errNoArg optStr; (NonOpt, rest))
                              else raise Fail "longOpt: impossible"
                        | (ReqArg(act, argName), []) => if (SS.isEmpty arg)
                              then (errReq(argName, optStr); (NonOpt, []))
                            else if (SS.isPrefix "=" arg)
                              then (Opt(act (SS.string (SS.triml 1 arg))), [])
                              else raise Fail "longOpt: impossible"
                        | (ReqArg(act, _), r::rs) => if (SS.isEmpty arg)
                              then (Opt(act r), rs)
                            else if (SS.isPrefix "=" arg)
                              then (Opt(act (SS.string (SS.triml 1 arg))), rest)
                              else raise Fail "longOpt: impossible"
                        | (OptArg(act, _), _) => if (SS.isEmpty arg)
                              then (Opt(act NONE), rest)
                            else if (SS.isPrefix "=" arg)
                              then (Opt(act (SOME (SS.string (SS.triml 1 arg)))), rest)
                              else raise Fail "longOpt: impossible"
                      (* end case *))
              (* search the long options for a match; we allow a unique prefix of an
               * option, but an exact match will take precedence.  E.g., if the long options
               * are "--foo", "--foobar", and "--foobaz", then "--foo" will match the first,
               * but "--foob" will be flagged as ambiguous.
               *)
                fun findOption ([], [], NONE) = (errUnrec optStr; (NonOpt, rest))
                  | findOption ([], _, SOME argDesc) = handleLong argDesc
                  | findOption ([], [argDesc], NONE) = handleLong argDesc
                  | findOption ([], _::_::_, NONE) = (errAmbig optStr; (NonOpt, rest))
                  | findOption ((descr : 'a opt_descr)::descrs, prefixMatches, exactMatch) = (
                      case List.filter (S.isPrefix opt') (#long descr)
                       of [] => findOption (descrs, prefixMatches, exactMatch)
                        | flgs => if List.exists (fn flg => (flg = opt')) flgs
                            then if Option.isSome exactMatch
                              then (errAmbig optStr; (NonOpt, rest))
                              else findOption (descrs, prefixMatches, SOME(#desc descr))
                            else findOption (descrs, #desc descr :: prefixMatches, exactMatch)
                      (* end case *))
                in
                  findOption (options, [], NONE)
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
                  else if (SS.isPrefix "-" arg')
                    then addOpt(shortOpt (SS.sub(arg', 1), SS.triml 2 arg', rest))
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
