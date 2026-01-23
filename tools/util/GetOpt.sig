(* getopt-sig.sml
 *
 * COPYRIGHT (c) 1998 Bell Labs, Lucent Technologies.
 *
 * A SML port of GNU's getopt library.
 *
 * This port is derived from Sven Panne's
 * <Sven.Panne@informatik.uni-muenchen.de>
 * implementation of the getopt library in Haskell <http://www.haskell.org>
 *
 * The following comments are lifted from Sven's code:
 *
 *   Two rather obscure features are missing: The Bash 2.0 non-option hack (if
 *   you don't already know it, you probably don't want to hear about it...)
 *   and the recognition of long options with a single dash (e.g. '-help' is
 *   recognised as '--help', as long as there is no short option 'h').
 *
 *   Other differences between GNU's getopt and this implementation:
 *     * To enforce a coherent description of options and arguments, there are
 *       explanation fields in the option/argument descriptor.
 *     * Error messages are now more informative, but no longer POSIX
 *       compliant... :-(
 *
 *
 *
 * A difference with Sven's port: errors now invoke an error callback, rather
 * than returning error strings while continuing processing options.
 * The full generality of the latter does not seem justified.
 *)


signature GetOpt =
  sig

      datatype 'a arg_order
        = RequireOrder
        | Permute
        | ReturnInOrder of string -> 'a
      (* What to do with options following non-options:
       * RequireOrder: no option processing after first non-option
       * Permute: freely intersperse options and non-options
       * ReturnInOrder: wrap non-options into options
       *)

      datatype 'a arg_descr
        = NoArg of unit -> 'a
        | ReqArg of (string -> 'a) * string
        | OptArg of (string option -> 'a) * string
      (* Description of an argument option:
       * NoArg: no argument required
       * ReqArg: option requires an argument; the string is the argument name
       * OptArg: optional argument; the string is the argument name
       *)

      type 'a opt_descr = {
          short : string,
          long : string list,
          desc : 'a arg_descr,
          help : string
        }
      (* Description of a single option *)

      val usageInfo : {
              header : string,
              options : 'a opt_descr list
            } -> string
      (* takes a header string and a list of option descriptions and
       * returns a string explaining the usage information.  A newline will
       * be added following the header, so it should not be newline terminated.
       *)

      val getOpt : {
              argOrder : 'a arg_order,
              options : 'a opt_descr list,
              errFn : string -> unit
            } -> string list -> ('a list * string list)
      (* takes as argument an arg_order to specify the non-options
       * handling, a list of option descriptions, an error callback,
       * and a command line containing the options and arguments,
       * and returns a list of (options, non-options)
       *)

  end
