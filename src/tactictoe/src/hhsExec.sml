structure hhsExec :> hhsExec = 
struct

open HolKernel Abbrev hhsLog hhsLexer hhsTools

val ERR = mk_HOL_ERR "hhsExec"

(* ----------------------------------------------------------------------
   Finding not loaded signatures used in string-tactics 
   ---------------------------------------------------------------------- *)

(* This code lead to inconsistencies in the files. *)
(*
fun split_sl s pl sl = case sl of
    []     => raise ERR "split_sl" (String.concatWith " " (rev pl))
  | a :: m => if a = s 
              then (rev pl, m) 
              else split_sl s (a :: pl) m 

fun is_quoted s = 
  let val x = hd (explode s) in x = #"`" orelse x = #"\"" end
  handle _ => false

fun is_number s = all Char.isDigit (explode s)

(* either real numbers or already prefixed *)
fun includes_dot s = mem #"." (explode s)

val operator_sml_list =
  ["op", "if", "then", "else", "val", "fun",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr", "andalso", "orelse",
   "and", "datatype", "type", "where", ":", ":>",
   "let", "in", "end", "while", "do",
   "local","=>","case","of","_","|","fn","handle"]

fun is_reserved_sml s =
  is_number s orelse 
  mem s ["[","(",",",")","]","{","}",";"] orelse 
  mem s operator_sml_list orelse
  is_quoted s orelse 
  s = "#" orelse 
  ((hd (explode s) = #"#" andalso hd (tl (explode s)) = #"\"") 
  handle _=> false)

(* all signatures have the form let open in or theory.name *)
fun find_sig sl =
  case sl of
    [] => []
  | "let" :: "open" :: m =>
    let val (al,ml) = split_sl "in" [] m in
      al @ find_sig ml
    end
  | "(" :: "DB.fetch" :: a :: _ :: ")" :: m =>
     if rm_squote a = current_theory () orelse rm_squote a = "-"
     then find_sig m
     else (rm_squote a ^ "Theory") :: find_sig m
  | a :: m =>
    if is_reserved_sml a then find_sig m
    else
    if mem #"." (explode a) andalso 
       not (is_number (hd (String.tokens (fn x => x = #".") a))) 
    then hd (String.tokens (fn x => x = #".") a) :: find_sig m
    else find_sig m

fun sigl_of_stac stac = mk_fast_set String.compare ((find_sig o hhs_lex) stac) 

fun load_sigl stac = app load (sigl_of_stac stac)
*)
(* ----------------------------------------------------------------------
   Execute strings as sml code
   ---------------------------------------------------------------------- *)
fun exec_sml file s =
  let
    val path = hhs_code_dir ^ "/" ^ file
    val oc = TextIO.openOut path
    fun os s = TextIO.output (oc,s)
  in
    os ("val _ = (" ^ s ^ ")");
    TextIO.closeOut oc;
    ((QUse.use path; true) handle _ => (hhs_log file s; false))
  end

(* ----------------------------------------------------------------------
   Tests
   ---------------------------------------------------------------------- *)

fun is_thm s =
  exec_sml "is_thm" ("Thm.dest_thm (" ^ s ^ ")")

fun is_tactic s =
  exec_sml "is_tactic" ("Tactical.VALID (" ^ s ^ ")")

val hhs_bool = ref false
  
fun is_pointer_eq s1 s2 =
  let 
    val b = exec_sml "is_pointer_eq" 
      ("hhsExec.hhs_bool := PolyML.pointerEq (" ^ s1 ^ "," ^ s2 ^ ")")
  in
    b andalso (!hhs_bool)
  end

(* ----------------------------------------------------------------------
   Read tactics
   ---------------------------------------------------------------------- *)

val MY_TAC: tactic = fn (g: goal) => ([g], hd)
val hhs_tactic = ref (MY_TAC) (* doesn't matter what the tactic is *)
val hhs_tacticl = ref []

fun valid_tactic_of_sml s =
  let 
    (* val _ = load_sigl s *)
    val b = 
    exec_sml "tactic_of_sml" 
    ("hhsExec.hhs_tactic := Tactical.VALID ( " ^ s ^ " )")
  in
    if b then !hhs_tactic else raise ERR "tactic_of_sml" s
  end

fun valid_tacticl_of_sml sl =
  let 
    fun mk_valid s = "Tactical.VALID ( " ^ s ^ " )"
    val valid_sl = map mk_valid sl
    val b = 
      exec_sml "tacticl_of_sml" 
      ("hhsExec.hhs_tacticl := [" ^ String.concatWith ", " valid_sl 
       ^ "]")
  in
    if b then !hhs_tacticl else raise ERR "tacticl_of_sml" ""
  end


(* ----------------------------------------------------------------------
   Read theorem names
   ---------------------------------------------------------------------- *)

val hhs_thm = ref ""

fun thmname_of_sml thm_sml =
  let val b = 
    exec_sml "rec_thm" 
    ("hhsExec.hhs_thm := hhsGen.name_of_thm " ^ "(" ^ thm_sml ^ ")")
  in
    if b then !hhs_thm else raise ERR " _loop" "thm"
  end

end (* struct *)
