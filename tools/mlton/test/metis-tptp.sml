(* ========================================================================= *)
(* THE HOL METIS PROVER APPLIED TO TPTP PROBLEMS                             *)
(* Copyright (c) 2002-2004 Joe Hurd                                          *)
(* ========================================================================= *)

(* Setting the trace level *)

val () = Feedback.set_trace "normalForms" 1;
val () = Feedback.set_trace "metis" 2;

(* Display *)

val () = Globals.show_assums := true;
val () = Globals.show_tags := true;

(* Infix operators *)

infixr ## |-> ::> @> oo -->;

(* Creating nice output *)

fun advertize s =
    print ("\n==" ^ s ^ mlibUseful.nchars #"=" (77 - size s) ^ "\n\n");

fun separator () = print (mlibUseful.nchars #"-" 79 ^ "\n\n");

fun error s = print ("ERROR: " ^ s ^ "\n\n");

(* An exception for prover errors *)

exception METIS_ERR of string;

(* Naming the input problems *)

local
  open mlibUseful;
  fun chop_suffix x s =
    let
      fun ext a b = String.extract (s,a,b)
      val n = size s - size x
    in
      if 0 <= n andalso ext n NONE = x then ext 0 (SOME n) else s
    end
  fun file_name "-" = "standard input"
    | file_name s =
      (chop_suffix ".tptp" o List.last o String.fields (equal #"/")) s;
in
  fun named l = map (fn x => (file_name x, x)) l;
end;

(* Solving problems *)

local
  fun read_file p =
    folTools.tptp_read {filename = p}
    handle mlibParser.Noparse =>
           raise METIS_ERR
             ("couldn't parse file \"" ^ p ^ "\"")
         | e as Io _ =>
           raise METIS_ERR
             ("couldn't read file \"" ^ p ^ "\":\n  " ^ General.exnMessage e);
in
  fun attack (n,p) =
    let
      val () = advertize n
      val () = print ("Problem: " ^ n ^ "\n\n")
      val fm = read_file p
      val () = print (Hol_pp.term_to_string fm ^ "\n\n")
      val th = metisLib.METIS_PROVE [] fm
      val () = print "\nSUCCESSFULLY PROVED\n\n"
      val () = print (Hol_pp.thm_to_string th ^ "\n\n")
    in
      ()
    end
    handle Feedback.HOL_ERR _ => print "\nFAILED TO PROVE\n\n"
         | METIS_ERR s => error s;
end;
    
(* Top level *)

val () = metisTools.limit := {time = NONE, infs = NONE};

val () = app (mlibPortable.time attack) (named (CommandLine.arguments ()));
