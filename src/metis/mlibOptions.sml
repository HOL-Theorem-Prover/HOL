(* ========================================================================= *)
(* PROCESSING COMMAND LINE OPTIONS                                           *)
(* Created by Joe Hurd, August 2003                                          *)
(* ========================================================================= *)

structure mlibOptions :> mlibOptions =
struct

infix ##

open mlibUseful;

(* One command line option: names, arguments, description and a processor *)
type opt = {switches : string list, arguments : string list,
            description : string, processor : string * string list -> unit};

(* Option processors may raise an Optionexit exception *)
exception Optionexit of {message : string option, usage : bool, success : bool};

(* Wrappers for option processors *)
local
  fun range NONE NONE = "Z"
    | range (SOME i) NONE = "{n IN Z | " ^ int_to_string i ^ " <= n}"
    | range NONE (SOME j) = "{n IN Z | n <= " ^ int_to_string j ^ "}"
    | range (SOME i) (SOME j) =
    "{n IN Z | " ^ int_to_string i ^ " <= n <= " ^ int_to_string j ^ "}";
  fun o_leq (SOME x) (SOME y) = x <= y | o_leq _ _ = true;
  fun arg_to_int arg omin omax x =
    (case Int.fromString x of
       SOME i =>
       if o_leq omin (SOME i) andalso o_leq (SOME i) omax then i else
         raise Optionexit
           {success = false, usage = false, message =
            SOME (arg ^ " option needs an integer argument in the range "
                  ^ range omin omax ^ " (not " ^ x ^ ")")}
     | NONE =>
       raise Optionexit
         {success = false, usage = false, message =
          SOME (arg ^ " option needs an integer argument (not \"" ^ x ^ "\")")})
    handle Overflow =>
       raise Optionexit
         {success = false, usage = false, message =
          SOME (arg ^ " option suffered integer overflow on argument " ^ x)};
in
  fun int_option (omin,omax) f (s,[x]) = f (s, arg_to_int s omin omax x)
    | int_option (_,_) _ (_,_) = raise ERR "int_option" "must have 1 argument";
end;

local
  fun range NONE NONE = "R"
    | range (SOME i) NONE = "{n IN R | " ^ real_to_string i ^ " <= n}"
    | range NONE (SOME j) = "{n IN R | n <= " ^ real_to_string j ^ "}"
    | range (SOME i) (SOME j) =
    "{n IN R | " ^ real_to_string i ^ " <= n <= " ^ real_to_string j ^ "}";
  fun o_leq (SOME (x:real)) (SOME y) = x <= y | o_leq _ _ = true;
  fun arg_to_real arg omin omax x =
    (case Real.fromString x of
       SOME i =>
       if o_leq omin (SOME i) andalso o_leq (SOME i) omax then i else
         raise Optionexit
           {success = false, usage = false, message =
            SOME (arg ^ " option needs an real argument in the range "
                  ^ range omin omax ^ " (not " ^ x ^ ")")}
     | NONE =>
       raise Optionexit
         {success = false, usage = false, message =
          SOME (arg ^ " option needs an real argument (not \"" ^ x ^ "\")")})
in
  fun real_option (omin,omax) f (s,[x]) = f (s, arg_to_real s omin omax x)
    | real_option _ _ _ = raise ERR "real_option" "must have 1 argument";
end;

(* Basic options useful for all programs *)
val basic_options : opt list =
  [{switches = ["--verbosity"], arguments = ["0..10"],
    description = "the degree of verbosity",
    processor = int_option (SOME 0, SOME 10) (fn (_,i) => trace_level := i)},
(* Don't advertise this
   {switches = ["--secret"], arguments = [],
    description = "process then hide the next option",
    processor = fn _ => raise Fail "basic_options: --secret"},
*)
   {switches = ["--"], arguments = [],
    description = "no more options",
    processor = fn _ => raise Fail "basic_options: --"},
   {switches = ["-?","-h","--help"], arguments = [],
    description = "display all options and exit",
    processor = fn _ => raise Optionexit
    {message = SOME "displaying all options", usage = true, success = true}},
   {switches = ["-v", "--version"], arguments = [],
    description = "display version information",
    processor = fn _ => raise Fail "basic_options: -v, --version"}];

(* All the command line options of a program *)
type allopts = {name : string, version : string, header : string,
                footer : string, options : opt list};

(* Usage information *)
fun version_information ({version, ...} : allopts) = version;

fun usage_information ({name, version, header, footer, options} : allopts) =
  let
    fun list_opts {switches = n, arguments = r, description = s, ...} =
      let
        fun indent (s, "" :: l) = indent (s ^ "  ", l) | indent x = x
        val (res,n) = indent ("  ",n)
        val res = res ^ join ", " n
        val res = foldl (fn (x,y) => y ^ " " ^ x) res r
      in
        [res ^ " ...", " " ^ s]
      end
  in
    header
    ^ align_table {left = true, pad = #"."} (map list_opts options)
    ^ footer
  end;

(* Process the command line options passed to the program *)
fun process_options (alloptions : allopts) =
  let
    val {name, options, ...} = alloptions

    fun escape {message, usage, success} =
      (case message of NONE => () | SOME m => print (name ^ ": " ^ m ^ "\n");
       if usage then print (usage_information alloptions) else ();
       OS.Process.exit
         (if success then OS.Process.success else OS.Process.failure))

    fun version_escape () =
      (print (version_information alloptions);
       raise Optionexit {message = NONE, usage = false, success = true})

    fun find_option x =
      case List.find (fn {switches = n, ...} => mem x n) options of
        NONE => escape {message = SOME ("unknown switch \"" ^ x ^ "\""),
                        usage = true, success = false}
      | SOME {arguments = r, processor = f, ...} => (r,f)

    fun get_args x r xs =
      let
        fun f 1 = "a following argument"
          | f m = int_to_string m ^ " following arguments"
        val m = length r
        val () =
          if m <= length xs then () else
            escape
              {usage = false, success = false, message = SOME
               (x ^ " option needs " ^ f m ^ ": " ^ join " " r)}
      in
        split xs m
      end

    fun process [] = ([], [])
      | process ("--" :: xs) = ([("--",[])], xs)
      | process ("--secret" :: xs) = (tl ## I) (process xs)
      | process ("-v" :: _) = version_escape ()
      | process ("--version" :: _) = version_escape ()
      | process (x :: xs) =
      if x = "" orelse x = "-" orelse hd (explode x) <> #"-" then ([], x :: xs)
      else
        let
          val (r,f) = find_option x
          val (ys,xs) = get_args x r xs
          val () = f (x,ys)
        in
          (cons (x,ys) ## I) (process xs)
        end
  in
    fn l =>
    let
      val () = if null l then version_escape () else ()
      val (a,b) = process l
      val a = foldl (fn ((x,xs),ys) => x :: xs @ ys) [] (rev a)
    in
      (a,b)
    end
    handle Optionexit x => escape x
  end;

end
