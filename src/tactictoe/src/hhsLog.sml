structure hhsLog :> hhsLog =
struct

open HolKernel Abbrev hhsTools

val ERR = mk_HOL_ERR "hhsLog"

(* ----------------------------------------------------------------------
   Simple IO
   ---------------------------------------------------------------------- *)

fun readl path =
  let
    val file = TextIO.openIn path
    fun loop file = case TextIO.inputLine file of
        SOME line => line :: loop file
      | NONE => []
    val l1 = loop file
    fun rm_last_char s = String.substring (s,0,String.size s - 1)
    fun is_empty s = s = ""
    val l2 = map rm_last_char l1 (* removing end line *)
    val l3 = filter (not o is_empty) l2
  in
    (TextIO.closeIn file; l3)
  end

fun append_file path s =
  let val oc = TextIO.openAppend path in
    TextIO.output (oc,s);
    TextIO.closeOut oc
  end

(* ----------------------------------------------------------------------
   Logging results
   ---------------------------------------------------------------------- *)

fun hhs_log file s =
  let
    val oc = TextIO.openAppend (hhs_log_dir ^ "/" ^ file)
    fun os s = TextIO.output (oc,s)
  in
    os (current_theory () ^ " : " ^ s ^ "\n"); TextIO.closeOut oc
  end

fun hhs_print s =
  let
    val oc = TextIO.openAppend (hhs_log_dir ^ "/hhs_print")
    fun os s = TextIO.output (oc,s)
  in
    print (s ^ "\n");
    os (s ^ "\n");
    TextIO.closeOut oc
  end

fun hhs_time name f x =
  let
    val rt = Timer.startRealTimer ()
    val r = f x
    val time = Timer.checkRealTimer rt
  in
    (hhs_print (name ^ ": " ^ Real.toString (Time.toReal time)); r)
  end

fun hhs_add_time f x =
  let
    val rt = Timer.startRealTimer ()
    val r = f x
    val time = Timer.checkRealTimer rt
  in
    (r, Time.toReal time)
  end

end
