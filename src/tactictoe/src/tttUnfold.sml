(* ======================================================================== *)
(* FILE          : tttUnfold.sml                                            *)
(* DESCRIPTION   : Partial unfolding of SML code.                           *)
(*                 Produces SML strings re-usable in different context.     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck           *)
(* DATE          : 2017                                                     *)
(* ======================================================================== *)

structure tttUnfold :> tttUnfold =
struct

open HolKernel Abbrev boolLib aiLib
  smlLexer smlInfix smlOpen smlExecute smlParallel
  tttManifest mlTacticData tttSetup

val ERR = mk_HOL_ERR "tttUnfold"

fun load_sigobj () = with_tactictoe_cache aiLib.load_sigobj

(* -----------------------------------------------------------------------
   Program representation and stack
   ----------------------------------------------------------------------- *)

datatype stack =
    Protect
  | Watch
  | Undecided
  | Replace      of string list
  | SReplace     of string list
  | Structure    of string
  | SValue       of string
  | SConstructor of string
  | SException   of string

fun protect x = (x, Protect)
fun watch x   = (x, Watch)
fun undecided x = (x, Undecided)

datatype sketch =
    Pattern  of string * sketch list * string * sketch list
  | Open     of string list
  | Infix    of (string * infixity_t) list
  | Code     of string * stack
  | Start    of string
  | End
  | In

(* ------------------------------------------------------------------------
   Global references
   ------------------------------------------------------------------------ *)

val (infix_glob : (string * infixity_t) list ref) = ref []
val open_cache = ref []
val ttt_unfold_cthy = ref "scratch"

(* ------------------------------------------------------------------------
   Test starting parentheses
   ------------------------------------------------------------------------ *)

fun hd_code_par2 m =
  (hd m = Code ("(",Protect) orelse hd m = Code ("{",Protect))
  handle _ => false

fun hd_code_par m =
  hd m = Code ("(",Protect) handle _ => false

(* ------------------------------------------------------------------------
   Program extraction
   ------------------------------------------------------------------------ *)

fun stringl_of_infix (a,b) = case b of
    Inf_left n  => ["infix" ,int_to_string n,a]
  | Inf_right n => ["infixr",int_to_string n,a]

fun original_program p = case p of
    [] => []
  | Open sl :: m    => ("open" :: sl) @ original_program m
  | Infix l :: m    => List.concat (map stringl_of_infix l) @ original_program m
  | In :: m         => "in" :: original_program m
  | Start s :: m    => s :: original_program m
  | End :: m        => "end" :: original_program m
  | Code (a,_) :: m   => a :: original_program m
  | Pattern (s,head,sep,body) :: m =>
    s :: original_program head @ [sep] @ original_program body @
    original_program m

fun bbody_of n p = case p of
    [] => []
  | Open _ :: m     => bbody_of n m
  | Infix _ :: m    => bbody_of n m
  | In :: m         => bbody_of (n-1) m
  | Start _ :: m    =>
    (if n = 0 then [Code ("(",Protect)] else []) @ bbody_of (n+1) m
  | End :: m        =>
    (if n = 0 then [Code (")",Protect)] else []) @ bbody_of n m
  | Code x :: m =>
    (if n = 0 then Code x :: bbody_of n m else bbody_of n m)
  | Pattern (s,head,sep,body) :: m  =>
    (
    if n = 0 then
    (
     if mem s ["val","fun"]
     then bbody_of n m
     else Pattern(s,bbody_of n head,sep,bbody_of n body) ::
          bbody_of n m
    )
    else bbody_of n m
    )

fun bare_body p = bbody_of 0 p

(* after unfolding *)
fun singleton s = [s]
fun mlquote_singleton s = [mlquote s]

fun record_fetch s sl =
  ["tttRecord.fetch", mlquote s, mlquote (String.concatWith " " sl)]

fun replace_code1 st = case st of
    (_,Replace sl)  => sl
  | (_,SReplace sl) => sl
  | (s,Protect)     => singleton s
  | (s,Watch)       => (debug ("replace_code1: " ^ s); singleton s)
  | _               => raise ERR "replace_code1" ""

fun replace_code2 st = case st of
    (s,Replace sl) =>
    (
    if (length sl = 1 andalso mem #"." (explode (hd sl)))
       handle _ => false
    then mlquote_singleton (String.concatWith " " sl)
    else singleton (String.concatWith " " (record_fetch s sl))
    )
  | (s,SReplace sl) => mlquote_singleton (String.concatWith " " sl)
  | (s,Protect)     => mlquote_singleton s
  | (s,Watch)       => (debug ("replace_code2: " ^ s);
                       singleton (String.concatWith " " (record_fetch s []))
                       )
  | _               => raise ERR "replace_code2" ""

(* forget "op" in a body that does not contain definitions *)
fun replace_program f g p = case p of
    [] => []
  | Code ("op",Protect) :: Code (_,SReplace sl) :: m =>
    List.concat (map g sl) @ replace_program f g m
  | Code ("op",Protect) :: Code (_,Replace sl) :: m =>
    List.concat (map g sl) @ replace_program f g m
  | Code ("op",Protect) :: Code (s,_) :: m =>
    (
    if mem #"." (explode s)
    then g s @ replace_program f g m
    else g "op" @ g s @ replace_program f g m
    )
  | Code st :: m => f st @ replace_program f g m
  | Pattern (s,head,sep,body) :: m =>
    (
    if mem s ["val","fun"]
    then replace_program f g m
    else g s @ replace_program f g head @ g sep @
         replace_program f g body @ replace_program f g m
    )
  | _ => raise ERR "replace_program" ""

fun replace_program1 p = replace_program replace_code1 singleton p
fun replace_program2 p = replace_program replace_code2 mlquote_singleton p

(* ------------------------------------------------------------------------
   Profiling
   ------------------------------------------------------------------------ *)

val open_time = ref 0.0
val replace_special_time = ref 0.0
val replace_id_time = ref 0.0

(* ------------------------------------------------------------------------
   Poly/ML 5.7 rlwrap poly
   val l = map (fn (a,b) => a) (#allVal (PolyML.globalNameSpace) ());
   ------------------------------------------------------------------------ *)

val basis = String.tokens Char.isSpace
(
"Size trunc ignore Empty Span :: Chr length LESS round vector EQUAL app " ^
"~ Subscript NONE ceil getOpt str substring use o explode foldr foldl ^ " ^
"exnMessage Option SOME tl Overflow null @ > = < ref Fail div nil before " ^
"real print ord / - rev + * implode map ! size isSome Div mod GREATER " ^
"Match " ^
"false abs <> exnName Domain Bind true >= valOf <= not := hd chr concat floor"
);

(* ------------------------------------------------------------------------
   Rebuild store_thm calls
   ------------------------------------------------------------------------ *)

fun rm_squote s =
  if String.sub (s,0) = #"\"" andalso String.sub (s,String.size s - 1) = #"\""
  then String.substring (s, 1, String.size s - 2)
  else raise ERR "rm_squote" s

fun rm_last_char s = String.substring (s, 0, String.size s - 1)

fun rm_bbra bbra charl =
  case charl of
      [] => []
  | #"[" :: m => rm_bbra true m
  | #"]" :: m => rm_bbra false m
  | a :: m => if bbra then rm_bbra true m else a :: rm_bbra false m

fun rm_bbra_str s = implode (rm_bbra false (explode s))

(* ------------------------------------------------------------------------
   Record global values as string for further references
   ------------------------------------------------------------------------ *)

fun is_endtype opar s =
  opar <= 0 andalso
  mem s [
   "end", "in", "val", "fun", "=",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr",
   "and", "datatype", "type", "local", ";", ")","]","}"
   ]

(* Leaking of identifiers between patterns *)
fun is_endval opar s =
  opar <= 0 andalso
  mem s [
   "end", "in", "val", "fun",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr",
   "and", "datatype", "type", "local",
   ";", ")","]","}"
   ]

fun split_endval_aux test opar acc sl =
  if sl = [] then (rev acc, []) else
  let val (a,m) = (hd sl, tl sl) in
    if test opar a
      then (rev acc, sl)
    else if mem a ["(","{","[","let"]
      then split_endval_aux test (opar + 1) (a :: acc) m
    else if mem a [")","}","]","end"]
      then split_endval_aux test (opar - 1) (a :: acc) m
    else split_endval_aux test opar (a :: acc) m
  end

fun split_endval sl = split_endval_aux is_endval 0 [] sl
fun split_endtype sl = split_endval_aux is_endtype 0 [] sl

(* ------------------------------------------------------------------------
   Extract pattern and identifiers.
   ------------------------------------------------------------------------ *)

fun extract_pattern s sl =
  let
    val (head,l2) = split_level s sl
    handle _ => raise ERR "extract_pattern"
                (s ^ ": " ^ (String.concatWith " " sl))
    val (body,cont) = split_endval l2
  in
    (head,body,cont)
  end

fun extract_open_aux libl sl = case sl of
    [] => (rev libl,[])
  | a :: m =>
    if is_reserved a
    then (rev libl,sl)
    else extract_open_aux (a :: libl) m

fun extract_open sl = extract_open_aux [] sl

fun extract_infix inf_constr l =
  if l = [] then raise ERR "extract_infix" "" else
  let
    val (a,m) = (hd l,tl l)
    val (n,sl) = if is_number a then (string_to_int a, m) else (0,l)
    val (body,cont) = extract_open sl
    fun f n s = (s, inf_constr n)
  in
    (map (f n) body, cont)
  end

(* ------------------------------------------------------------------------
   Watching and replacing some special values:
   functions calling save_thm
   functions making definitions
   functions affecting the proof state (i.e. export_rewrites)
   ----------------------------------------------------------------------- *)

val store_thm_list =
  ["store_thm","maybe_thm","Store_thm","asm_store_thm"]

(* Theorem/Proof/QED blocks are expanded by HOLSource to calls of
   Q.store_thm_at.  These calls produce theorem values just like
   store_thm, but have a curried source-location argument, so they need
   separate parsing below. *)
val store_thm_at_list = ["store_thm_at"]

val name_thm_list =
  ["save_thm","new_specification",
  "new_definition","new_infixr_definition","new_infixl_definition",
  "new_type_definition"]

val prove_list = ["prove","TAC_PROOF"]


val watch_list_init = watched_store_operations

val watch_dict = dnew String.compare (map (fn x => (x,())) watch_list_init)

(* ------------------------------------------------------------------------
   Extract calls
   ------------------------------------------------------------------------ *)

fun split_codelevel_aux i s pl program = case program of
    []     => raise ERR "split_codelevel_aux"
      (s ^ " : " ^ (String.concatWith " " (original_program program)))
  | Code (a,tag) :: m =>
    if a = s andalso i <= 0
      then (rev pl, m)
    else if mem a ["let","local","struct","(","[","{"]
      then split_codelevel_aux (i + 1) s (Code (a,tag) :: pl) m
    else if mem a ["end",")","]","}"]
      then split_codelevel_aux (i - 1) s (Code (a,tag) :: pl) m
    else split_codelevel_aux i s (Code (a,tag) :: pl) m
  | x :: m => (split_codelevel_aux i s (x :: pl) m)

fun split_codelevel s sl =
  split_codelevel_aux 0 s [] sl
  handle HOL_ERR _ =>
   raise ERR "split_codelevel"
      (s ^ " : " ^ (String.concatWith " " (original_program sl)))

fun rpt_split_codelevel s sl =
  let val (a,b) = split_codelevel s sl handle _ => (sl,[]) in
    if null b then [a] else a :: rpt_split_codelevel s b
  end

fun original_code x = case x of
    Code (y,_) => y
  | _ => raise ERR "original_code" ""

fun extract_store_thm sl =
  let
    val (body,cont) = split_codelevel ")" sl
    val (namel,l0)  = split_codelevel "," body
    val (term,qtac) = split_codelevel "," l0
    val name = original_code (last namel)
  in
    if is_quoted name
    then SOME (rm_squote name, namel, term, qtac, cont)
    else NONE
  end
  handle HOL_ERR _ =>
    (
    print_endline ("Warning: extract_store_thm: " ^
      (String.concatWith " "(map original_code (first_n 10 sl))));
    NONE
    )

(* For the modern Theorem/Proof/QED syntax, sketch_wrap feeds HOL's
   source-expander output, which desugars each Theorem block to
     val id = Q.store_thm_at (loc) ("name[attrs]", term, tac)
   where tac = fn HOLSourceExpand.goal_dummy => <user-tactic>
                 HOLSourceExpand.goal_dummy
   (the expander wraps the user's tactic via wrapTac).  The store_thm
   recognizer above does not see `store_thm_at` and cannot parse the
   curried (loc)(args) shape, so such scripts record zero proofs.
   extract_store_thm_at handles the curried form and unwraps the
   goal-lambda so the recorded tactic is the user's tactic. *)

(* take_group: given a sketch list starting with "(" (or "[" / "{"),
   return the tokens inside that one balanced group (without the outer
   delimiters) and the rest. *)
fun take_group_aux d pl [] = raise ERR "take_group" "unbalanced"
  | take_group_aux d pl (x :: m) =
    case x of
      Code (a,_) =>
        if mem a ["(","[","{"] then take_group_aux (d + 1) (x :: pl) m
        else if mem a [")","]","}"] then
          if d <= 1 then (rev pl, m) else take_group_aux (d - 1) (x :: pl) m
        else take_group_aux d (x :: pl) m
    | _ => take_group_aux d (x :: pl) m

fun take_group (Code(a,_) :: m) =
      if a = "(" orelse a = "[" orelse a = "{" then take_group_aux 1 [] m
      else raise ERR "take_group" ("expected (, got " ^ a)
  | take_group _ = raise ERR "take_group" "not a paren"

(* unwrap_fn: drop the `fn goal_dummy => <tac> goal_dummy` wrapper that
   HOLSourceExpand.wrapTac produces, returning the user's tactic (sketch list).
   The sketcher renders `fn X => BODY` as
   Pattern ("fn", [X], "=>", sketched BODY), so match on Pattern. *)
fun drop_goalarg_sketch sk =
  case rev sk of
    Code (name,_) :: rest =>
      if name = HOLSourceExpand.goal_dummy then rev rest else sk
  | _ => sk

fun unwrap_fn sk =
  case sk of
    Pattern ("fn", _, "=>", body) :: _ =>
      (case body of
         Code ("(",_) :: _ => #1 (take_group body)
       | _ => drop_goalarg_sketch body)
  | _ => sk

(* Match the attribute grammar used by the theorem store itself, so recorder
   keys agree with DB.fetch for every supported theorem name. *)
fun theorem_name s = #1 (AttributeSyntax.dest_name_attrs s)

fun extract_store_thm_at sl =
  let
    (* sl is the content inside the first paren (the opening "(" was
       dropped by `tl m` in the recognizer), i.e. the loc group content
       followed by the args group:  <loc> ) ( <args> ) <rest> *)
    val (locg, rest1) = split_codelevel ")" sl
    val (argsg, cont) = take_group rest1
    val (namel, l0)  = split_codelevel "," argsg
    val (term, qtacw) = split_codelevel "," l0
    val qtac = unwrap_fn qtacw
    val name = original_code (last namel)
  in
    if is_quoted name
    then SOME (rm_squote name, locg, namel, term, qtac, cont)
    else NONE
  end
  handle HOL_ERR _ =>
    (
    print_endline ("Warning: extract_store_thm_at: " ^
      (String.concatWith " "(map original_code (first_n 10 sl))));
    NONE
    )

fun extract_prove sl =
  let
    val (body,cont) = split_codelevel ")" sl
    val (term,qtac) = split_codelevel "," body
  in
    SOME (term,qtac,cont)
  end

fun extract_thmname sl =
  let
    val (body,cont) = split_codelevel ")" sl
    val (namel,_) = split_codelevel "," body
    val name = original_code (last namel)
  in
    if is_quoted name
    then SOME (rm_bbra_str (rm_squote name),cont)
    else NONE
  end
  handle _ => NONE

fun extract_recordname sl =
  let
    val (body,cont) = split_codelevel "}" sl
    val ll0 = rpt_split_codelevel "," body
    val ll1 = map (split_codelevel "=") ll0
    val name = original_code (last (assoc [Code ("name",Protect)] ll1))
  in
    if is_quoted name
    then SOME (rm_bbra_str (rm_squote name),cont)
    else NONE
  end
  handle _ => NONE

(* ------------------------------------------------------------------------
   Extract a program sketch
   ------------------------------------------------------------------------ *)

fun concat_with el ll = case ll of
    []     => []
  | [l]    => l
  | l :: m => l @ [el] @ concat_with el m

val bval = ref true
val bfun = ref true

fun sketch sl = case sl of
    [] => []
  | "datatype" :: m =>
    let val (body,cont) = split_endval m in
      map (Code o protect) ("datatype" :: body) @ sketch cont
    end
  | "type" :: m =>
    let val (body,cont) = split_endval m in
      map (Code o protect) ("type" :: body) @ sketch cont
    end
  | ":" :: m =>
    let val (body,cont) = split_endtype m in
      map (Code o protect) (":" :: body) @ sketch cont
    end
  | "open"   :: m =>
    let val (libl,cont) = extract_open m in Open libl :: sketch cont end
  | "infix" :: m =>
    let val (infl,cont) = extract_infix Inf_left m in
      Infix infl :: sketch cont
    end
  | "infixr" :: m =>
    let val (infl,cont) = extract_infix Inf_right m in
      Infix infl :: sketch cont
    end
  | "val" :: m    => (bval := true; sketch_pattern "val" "=" m)
  | "fun" :: m    =>
    (bval := false; bfun := true; sketch_pattern_bfun "fun" "=" true m)
  | "and" :: m    => if !bval
                     then sketch_pattern "val" "=" m
                     else sketch_pattern_bfun "fun" "=" true m
    (* todo: support for mutually recursive functions *)
  | "fn"  :: m    => sketch_pattern_bfun "fn" "=>" false m
  | "|"   :: m    =>
    let val in_fun = !bfun in
      sketch_pattern_bfun "|" (if in_fun then "=" else "=>") in_fun m
    end
  | "of"  :: m    => sketch_pattern_bfun "of" "=>" false m
  | "handle" :: m => sketch_pattern_bfun "handle" "=>" false m
  | "local" :: m  => Start "local" :: sketch m
  | "let" :: m    => Start "let" :: sketch m
  | "structure" :: a :: "=" :: "struct" :: m =>
    let val (body,cont) = split_level "end" m in
      if String.isSuffix "Theory" a orelse String.isSuffix "Script" a
      then sketch body @ [Code (";",Protect)] @ sketch cont
      else map (fn x => Code (x,Protect))
             (["structure",a,"=","struct"] @ body @ ["end"]) @
           sketch cont
    end
  | "in" :: m     => In  :: sketch m
  | "end" :: m    => End :: sketch m
  | "{" :: m      => Code ("{",Protect) :: sketch_record m
  | a :: m        => Code (a,Undecided) :: sketch m
and sketch_pattern s sep m =
  let
    val (head,body,cont) = extract_pattern sep m
      handle _ => extract_pattern "=" m
    val new_body = sketch body
  in
    Pattern (s, map (Code o undecided) head, sep, new_body) :: sketch cont
  end
and sketch_pattern_bfun s sep body_bfun m =
  let
    val old_bfun = !bfun
    val (head,body,cont) = extract_pattern sep m
      handle _ => extract_pattern "=" m
    val _ = bfun := body_bfun
    val new_body = sketch body
    val _ = bfun := old_bfun
  in
    Pattern (s, map (Code o undecided) head, sep, new_body) :: sketch cont
  end
and sketch_record m =
  let
    val (record,cont) = split_level "}" m
    val entryl = rpt_split_level "," record
    fun f entry =
      let val (head,body) = split_level "=" entry
         handle _ =>
         raise ERR "sketch_record" (String.concatWith " " (first_n 10 m))
      in
        map (Code o protect) head @ [Code ("=",Protect)] @ sketch body
      end
    val l = map f entryl
  in
    concat_with (Code (",",Protect)) l @ [Code ("}",Protect)] @ sketch cont
  end

(* ------------------------------------------------------------------------
   Stack
   ------------------------------------------------------------------------ *)

val push_time = ref 0.0

fun hd_err s x = hd x handle Empty => raise ERR s ""

fun push_stackv_aux in_flag (k,v) stack =
  if in_flag <= 0
  then dadd k v (hd_err "push" stack) :: tl stack
  else hd_err "push" stack :: push_stackv_aux (in_flag - 1) (k,v) (tl stack)

fun push_stackvl_aux in_flag stackvl stack =
  if in_flag <= 0
  then daddl stackvl (hd_err "push" stack) :: tl stack
  else hd_err "push" stack :: push_stackvl_aux (in_flag - 1) stackvl (tl stack)

fun push_stackv in_flag (k,v) stack =
  total_time push_time (push_stackv_aux in_flag (k,v)) stack

fun push_stackvl in_flag stackvl stack =
  total_time push_time (push_stackvl_aux in_flag stackvl) stack

fun stack_find stack id = case stack of
    []        => NONE
  | dict :: m => (SOME (dfind id dict) handle _ => stack_find m id)

fun replace_struct stack id =
  case stack_find stack id of
    SOME (Structure full_id) => [full_id]
  | _ =>
    (if mem #"." (explode id) then ()
     else debug ("warning: replace_struct: " ^ id); [id])

fun stack_find stack id = case stack of
    []        => NONE
  | dict :: m => (SOME (dfind id dict) handle _ => stack_find m id)

fun replace_id stack id =
  case stack_find stack id of
    SOME Protect    => SReplace [id]
  | SOME (Replace sl) => Replace sl
  | SOME (SValue full_id) => SReplace [full_id]
  | SOME (SConstructor full_id) => SReplace [full_id]
  | SOME (SException full_id) => SReplace [full_id]
  | SOME (Structure full_id) => SReplace [full_id]
  | _ =>
    (if mem #"." (explode id) then () else debug ("id: " ^ id);
    SReplace [id])

fun let_in_end s head body id =
  ["let",s] @ head @ ["="] @ body @ ["in",id,"end"]

val n_store_thm = ref 0

fun smart_concat_aux sep n l = case l of
    [] => ""
  | [a] => if n <= 0 orelse n + String.size a <= 75
           then a
           else "\n" ^ a
  | a :: m =>
    if n <= 0 orelse n + String.size a <= 75
    then a ^ sep ^ smart_concat_aux sep (String.size a + n) m
    else "\n" ^ a ^ sep ^ smart_concat_aux sep (String.size a) m

fun smart_concat sep l = smart_concat_aux sep 0 l

fun ppstring_stac qtac =
  let
    val tac2 = replace_program2 (bare_body qtac)
    val tac3 = "[ " ^ smart_concat ", " tac2 ^ " ]"
  in
    String.concatWith " " ["(","String.concatWith",mlquote " ","\n",tac3,")"]
  end

(* ------------------------------------------------------------------------
   Final modifications of the scripts
   ------------------------------------------------------------------------ *)

(* todo: remove this flag at a minor computation cost *)
val is_thm_flag = ref false

(* The tokens that replace a proof's tactic in the rewritten script: bind
   the original tactic, build the recording wrapper around it, and hand
   both to record_proof, which replays the wrapper and falls back to the
   original tactic if it fails.  Shared by the store_thm_at, store_thm and
   prove branches below, which differ only in what precedes the tactic. *)
fun record_wrapper name qtac =
  let
    val tac1 = original_program qtac
    val lflag_name = if mem "let" tac1 then "true" else "false"
    val tac2 = ppstring_stac qtac
  in
    ["let","val","tactictoe_tac1","="] @ tac1 @
    ["val","tactictoe_tac2","=","(","tttRecord.app_wrap_proof",
     mlquote name,"\n",tac2,"handle","_","=>","tactictoe_tac1",")"] @
    ["in","tttRecord.record_proof",mlquote name,lflag_name,
     "tactictoe_tac2","tactictoe_tac1","end"]
  end

fun modified_program (h,d) p =
  let fun continue m' = modified_program (h,d) m' in
  case p of
    [] => []
  | Open sl :: m    => ["open"] @ sl @ continue m
  | Infix l :: m    => List.concat (map stringl_of_infix l) @ continue m
  | In :: m         => "in" :: continue m
  | Start s :: m    => s :: continue m
  | End :: m        => "end" :: continue m
  | Pattern (s,head,sep,body) :: m =>
    let
      val _ = if d = 0 then is_thm_flag := false else ()
      val head' = modified_program (true, d+1) head
      val body' = modified_program ((s <> "val") orelse h, d+1) body
      val semicolon =
        if d = 0 andalso !is_thm_flag then
       ["; val _ = tttRecord.ttt_before_save_state ()",
        "; val _ = tttRecord.ttt_save_state ()",
        "; val _ = tttRecord.ttt_after_save_state ();"]
        else []
    in
      semicolon @ [s] @ head' @ [sep] @ body' @ continue m
    end
  | Code (a,_) :: m =>
    (
    if mem (drop_sig a) ["export_theory"] then continue m
    else if h orelse d > 1 then a :: continue m
    else if drop_sig a = "store_thm_at" andalso hd_code_par m
      then
      case extract_store_thm_at (tl m) of
        NONE => a :: continue m
      | SOME (name,locg,namel,term,qtac,cont) =>
        let
          val _ = is_thm_flag := true
          val _ = incr n_store_thm
        in
          [a,"("] @ original_program locg @ [")","("] @
          original_program namel @ [","] @ original_program term @ [","] @
          record_wrapper (theorem_name name) qtac @ [")"]
          @ continue cont
        end
    else if mem (drop_sig a) store_thm_list andalso hd_code_par m
      then
      case extract_store_thm (tl m) of
        NONE => a :: continue m
      | SOME (name,namel,term,qtac,cont) =>
        let
          val _ = is_thm_flag := true
          val _ = incr n_store_thm
        in
          [a,"("] @ original_program namel @ [","] @
          original_program term @ [","] @
          record_wrapper (theorem_name name) qtac @ [")"]
          @ continue cont
        end
    else if mem (drop_sig a) prove_list andalso hd_code_par m
      then
      case extract_prove (tl m) of
        NONE => a :: continue m
      | SOME (term,qtac,cont) =>
        let
          val _ = is_thm_flag := true
          val name = "tactictoe_prove_" ^ (int_to_string (!n_store_thm))
          val _ = incr n_store_thm
        in
          [a,"("] @ original_program term @ [","] @
          record_wrapper name qtac @ [")"]
          @ continue cont
        end
    else a :: continue m
    )
  end

(* ------------------------------------------------------------------------
   Stack continued
   ------------------------------------------------------------------------ *)

fun stackvl_of_value idl head body =
  let
    val body_sl = replace_program1 body
    handle _ =>
    raise ERR "value body" (String.concatWith " " (original_program body))
    val head_sl = replace_program1 head
    handle _ => raise ERR "value head" (String.concatWith " " idl)
  in
    if length head_sl = 1 andalso length body_sl = 1
      then map (fn x => (x, Replace body_sl)) idl
    else if length head_sl = 1
      then map (fn x => (x, Replace (["("] @ body_sl @ [")"]))) idl
    else
      map (fn x => (x, Replace (let_in_end "val" head_sl body_sl x))) idl
  end

fun stackvl_of_function idl head body =
  let
    val id = hd idl handle _ => raise ERR "stackv_of_function" ""
    val body_sl = replace_program1 body
    handle _ => raise ERR "function body" (String.concatWith " " idl)
    val head_sl = replace_program1 head
    handle _ => raise ERR "function head" (String.concatWith " " idl)
  in
    [(id, Replace (let_in_end "fun" head_sl body_sl id))]
  end

fun open_struct_aux stack s'=
  let
    val s = case replace_struct stack s' of
              [a] => a
            | _   => raise ERR "open_struct" ""
    fun decrease f l = case l of
      []     => [f []]
    | _ :: m => f l :: decrease f m
  in
    if mem s (map fst (!open_cache))
    then assoc s (!open_cache)
    else
      let
        val l0 = String.tokens (fn x => x = #".") s
        val (l1,l2,l3,l4) = view_struct_cached s
          handle Interrupt => raise Interrupt
               | OpenStruct (s,e) =>
                   raise ERR "open_struct"
                     ("could not analyse open structure " ^ s ^ ": " ^
                      General.exnMessage e)
        fun f constr a =
          let fun g l =
            (String.concatWith "." (l @ [a]), constr (s ^ "." ^ a))
          in
            decrease g l0
          end
        val rl =
          List.concat (map (f SValue) l1) @
          List.concat (map (f SConstructor) l2) @
          List.concat (map (f SException) l3) @
          List.concat (map (f Structure) l4)
      in
        (open_cache := (s,rl) :: !open_cache; rl)
      end
  end

fun open_struct stack s = total_time open_time (open_struct_aux stack) s

fun open_structure s = open_struct_aux [] s

(* ------------------------------------------------------------------------
   Functions for which we know how to extract the name of the theorem from
   its arguments.
   ------------------------------------------------------------------------ *)

fun is_store_thm_at x = mem (drop_sig x) store_thm_at_list
fun is_watch_name x = mem (drop_sig x) (store_thm_list @ name_thm_list)

fun mk_fetch b =
  map (Code o protect)
    ["(","DB.fetch",mlquote (!ttt_unfold_cthy),mlquote b,")"]

fun replace_fetch l = case l of
    [] => []
  | Code(a,Watch) :: m =>
    (
    if is_store_thm_at a andalso hd_code_par m
    then
      case extract_store_thm_at (tl m) of
        SOME (name,_,_,_,_,cont) =>
        mk_fetch (theorem_name name) @ replace_fetch cont
      | NONE => Code(a,Watch) :: replace_fetch m
    else if is_watch_name a andalso hd_code_par2 m
    then
      let val x =
        if hd_code_par m
          then extract_thmname (tl m)
          else extract_recordname (tl m)
      in
        case x of
          SOME (name,cont) =>
          let val new_name =
            if a = "new_type_definition" then name ^ "_TY_DEF" else name
          in
            mk_fetch new_name @ replace_fetch cont
          end
        | NONE => Code(a,Watch) :: replace_fetch m
      end
    else Code(a,Watch) :: replace_fetch m
    )
  | a :: m => a :: replace_fetch m

(* ------------------------------------------------------------------------
   Unfold the program.
   ------------------------------------------------------------------------ *)

fun protect_infix infixity l =
  let val (s1,s2) = infix_pair infixity in
    if length l = 1
    then [s1] @ l @ [s2]
    else [s1,"("] @ l @ [")",s2]
  end

fun is_watch stack id =
  let fun is_watch_local stack id =
    case stack_find stack id of
      SOME Watch => true
    | _          => false
  in
    dmem (drop_sig id) watch_dict orelse is_watch_local stack id
  end

fun is_watch_tag x = case x of
    Code (_,Watch) => true
  | _ => false

fun decide_head stack head = case head of
    [] => ([],[])
  | Code (a,Undecided) :: m =>
    let
      val (new_head,idl) = decide_head stack m
      val (new_tag,new_idl) =
        if is_reserved a then (Protect,[]) else
        case stack_find stack a of
          SOME (SException x) => (SReplace [x],[])
        | SOME (SConstructor x) => (SReplace [x],[])
        | _ => (Protect,[a])
    in
      (Code (a,new_tag) :: new_head, new_idl @ idl)
    end
  | _ => raise ERR "decide_head" ""

fun dest_replace x = case x of
    Replace sl => sl
  | SReplace sl => sl
  | _ => raise ERR "dest_replace" ""

fun unfold in_flag stack program = case program of
    [] => []
  | Pattern (s,head,sep,body) :: m =>
    let
      val (new_head,idl) = decide_head stack head
      val lstack =
        if s = "val"
        then dempty String.compare :: stack
        else dnew String.compare (map protect idl) :: stack
      val new_body = unfold 0 lstack body
      val special_body = (* replace_spec *) new_body
      val fetch_body = replace_fetch (bare_body special_body)
      val stackvl =
        if mem s ["val","fun"]
        then
          if exists is_watch_tag fetch_body
          then map watch idl
          else
            if s = "val"
            then stackvl_of_value idl new_head fetch_body
            else stackvl_of_function idl new_head fetch_body
        else []
    in
      Pattern (s,new_head,sep,special_body) ::
      unfold in_flag (push_stackvl in_flag stackvl stack) m
    end
  | Open sl :: m =>
    let
      val stackvl = List.concat (map (open_struct stack) sl) in
        Open sl :: unfold in_flag (push_stackvl in_flag stackvl stack) m
    end
  | Infix vl :: m =>
    (infix_glob := vl @ (!infix_glob); Infix vl :: unfold in_flag stack m)
  | In :: m => In :: unfold (in_flag + 1) stack m
  | Start s :: m =>
    Start s :: unfold in_flag (dempty String.compare :: stack) m
  | End :: m    => End :: unfold (in_flag - 1) (tl stack) m
  | Code ("op",_) :: Code (id,Undecided) :: m =>
    let val new_code =
      if is_reserved id then Code (id,Protect)
      else if is_watch stack id then Code (id,Watch)
      else if mem id (map fst (!infix_glob))
        then Code (id, SReplace (dest_replace (replace_id stack id)))
        else Code (id, replace_id stack id)
    in
      Code ("op",Protect) :: new_code :: unfold in_flag stack m
    end
  | Code (id,Undecided) :: m =>
    let val new_code =
      if is_reserved id then Code (id,Protect)
      else if is_watch stack id then Code (id,Watch)
      else if mem id (map fst (!infix_glob)) then
        let
          val infixity = assoc id (!infix_glob)
          val replacel = dest_replace (replace_id stack id)
        in
          Code (id, SReplace (protect_infix infixity replacel))
        end
      else Code (id, replace_id stack id)
    in
      new_code :: unfold in_flag stack m
    end
  | x :: m => x :: unfold in_flag stack m

(* ------------------------------------------------------------------------
   Main call
   ------------------------------------------------------------------------ *)

fun extract_thy file =
  let
    val suffix = last (String.tokens (fn x => x = #"/") file)
    val cthy = String.substring (suffix, 0,
      String.size suffix - String.size "Script.sml")
  in
    cthy
  end

fun os oc s = TextIO.output (oc, s)
fun osn oc s = TextIO.output (oc, s ^ "\n")

fun is_break s =
  mem s [
   "end", "in", "val", "fun",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr",
   "and", "datatype", "type", "local","let",";"]

fun print_sl oc sl = case sl of
    []     => ()
  | a :: m => (if is_break a then os oc ("\n" ^ a) else os oc (" " ^ a);
               print_sl oc m)

fun write_sl file sl =
  let val oc = TextIO.openOut file in
    print_sl oc sl;
    TextIO.closeOut oc
  end

fun string_of_bool flag = if flag then "true" else "false"

fun reflect_flag oc s x =
  osn oc ("val _ = " ^ s ^ " := " ^ string_of_bool (!x));

fun reflect_time oc s x =
  osn oc ("val _ = " ^ s ^ " := " ^ Real.toString (!x));

val metis_theories =
  ["sat", "marker", "combin", "min", "bool", "normalForms"]

fun output_header oc cthy =
  (
  app (osn oc)
  [
  "(* =================================================================== *)",
  "(* This file was modifed by TacticToe.                                 *)",
  "(* =================================================================== *)"
  ];
  (* infix operators *)
  app (os oc) (bare_readl infix_file);
  (* debugging *)
  reflect_flag oc "aiLib.debug_flag" debug_flag;
  (* cache root *)
  osn oc ("val _ = tttSetup.set_tactictoe_cache_dir " ^
          mlquote (tactictoe_dir_of ()));
  (* recording *)
  reflect_flag oc "tttSetup.record_flag" record_flag;
  reflect_flag oc "tttSetup.record_prove_flag" record_prove_flag;
  reflect_flag oc "tttSetup.record_let_flag" record_let_flag;
  reflect_flag oc "tttSetup.ttt_ex_flag" ttt_ex_flag;
  reflect_flag oc "tttSetup.record_savestate_flag" record_savestate_flag;
  reflect_flag oc "tttSetup.record_ortho_flag" record_ortho_flag;
  reflect_flag oc "tttSetup.export_thmdata_flag" export_thmdata_flag;
  reflect_flag oc "tttSetup.learn_abstract_term" learn_abstract_term;
  reflect_time oc "tttSetup.record_tactic_time" record_tactic_time;
  reflect_time oc "tttSetup.record_proof_time" record_proof_time;
  reflect_time oc "tttSetup.learn_tactic_time" learn_tactic_time;
  (* search *)
  reflect_time oc "tttSetup.ttt_search_time" ttt_search_time;
  reflect_time oc "tttSetup.ttt_tactic_time" ttt_tactic_time;
  osn oc ("val _ = mlTacticData.ttt_tacdata_file_override := SOME " ^
          mlquote (current_tacdata_file cthy));
  (* hook *)
  osn oc ("val _ = tttRecord.start_record_thy " ^ mlquote cthy)
  )

fun output_foot oc cthy =
  osn oc ("\nval _ = tttRecord.end_record_thy " ^ mlquote cthy)

fun start_unfold_thy cthy =
  (
  debug ("start_unfold_thy: " ^ cthy);
  ttt_unfold_cthy := cthy;
  (* statistics *)
  n_store_thm := 0; open_time := 0.0; replace_special_time := 0.0;
  replace_id_time := 0.0; push_time := 0.0;
  (* initial stack *)
  infix_glob := overlay_infixity;
  (* cache *)
  open_cache := []
  )

fun end_unfold_thy () =
  let
    val n = !n_store_thm
    fun f s r = debug (s ^ ": " ^ Real.toString (!r))
  in
    print_endline (int_to_string n ^ " proofs recognized");
    debug (int_to_string n ^ " proofs recognized");
    f "Push" push_time;
    f "Open" open_time;
    f "Replace special" replace_special_time;
    f "Replace id" replace_id_time
  end

fun rm_spaces s =
  let fun f c = if mem c [#"\n",#"\t",#"\r"] then #" " else c in
    implode (map f (explode s))
  end

fun sketch_wrap thy file =
  let
    val s1 = HOLSource.inputFile {quietOpen = false, print = K()} file
    val s2 = rm_spaces (rm_comment s1)
    val sl = partial_sml_lexer s2
    val lexdir = tactictoe_dir_of () ^ "/log/lexer"
    val _ = app mkDir_err [OS.Path.dir lexdir, lexdir]
    val _ = write_sl (lexdir ^ "/" ^ thy) sl
  in
    sketch sl
  end

fun unfold_wrap p = unfold 0 [dnew String.compare (map protect basis)] p

(* ------------------------------------------------------------------------
   Rewriting script
   ------------------------------------------------------------------------ *)

fun tttsml_of file =
  tactictoe_scratch_dir_of () ^ "/scripts/" ^ OS.Path.base file ^ "_ttt.sml"

fun print_program cthy fileorg sl =
  let
    val _ = debug ("print_program: " ^ fileorg)
    val fileout = tttsml_of fileorg
    val scriptdir = tactictoe_dir_of () ^ "/log/scripts"
    val _ = app mkDir_err [OS.Path.dir fileout, OS.Path.dir scriptdir,
                            scriptdir]
    val oc = TextIO.openOut fileout
    fun script_save () =
      let
        val cmd = String.concatWith " "
          ["cp", shell_quote fileout, shell_quote (scriptdir ^ "/" ^ cthy)]
      in
        cmd_in_dir (tactictoe_dir_of ()) cmd
      end
  in
    output_header oc cthy;
    print_sl oc sl;
    output_foot oc cthy;
    TextIO.closeOut oc;
    script_save ()
  end

fun rewrite_script thy fileorg =
  let
    val _ = start_unfold_thy thy
    val _ = debug ("sketch_wrap: " ^ fileorg)
    val p0 = sketch_wrap thy fileorg
    val _ = debug "unfold_wrap"
    val p2 = unfold_wrap p0
    val _ = debug "modified_program"
    val _ = is_thm_flag := false
    val sl5 = modified_program (false,0) p2
  in
    print_program thy fileorg sl5;
    end_unfold_thy ()
  end

fun full_path dir = OS.FileSys.fullPath dir handle _ => dir

fun record_context_includes scriptorg =
  let
    val scriptdir = OS.Path.dir scriptorg
    val loaded_dirs = map snd (Binarymap.listItems (fileDirMap ()))
    (* dedup before resolving: fileDirMap has one entry per loaded file,
       so the same handful of directories repeats thousands of times *)
    val dirs = mk_sameorder_set String.compare
      (scriptdir :: loaded_dirs @ !loadPath)
  in
    mk_sameorder_set String.compare (map full_path dirs)
  end

type record_context =
  {scriptorg : string, dirorg : string, includes : string list}

fun mk_record_context thy =
  let
    val scriptorg = find_script thy
    val dirorg = OS.Path.dir scriptorg
  in
    {scriptorg = scriptorg, dirorg = dirorg,
     includes = record_context_includes scriptorg}
  end

fun ttt_rewrite_thy_in_context thy
    ({scriptorg,dirorg,includes} : record_context) =
  let
    val _ = print_endline ("ttt_rewrite_thy: " ^ thy ^ "\n  " ^ scriptorg)
    fun rewrite_with_context script =
      with_flag (smlOpen.openscript_run_dir, SOME dirorg)
        (with_flag (smlOpen.openscript_includes, includes)
           (rewrite_script thy)) script
    val (_,t) = add_time rewrite_with_context scriptorg
  in
    print_endline ("ttt_rewrite_thy time: " ^ rts_round 4 t)
  end

fun ttt_rewrite_thy thy =
  if mem thy ["bool","min"] then () else
    ttt_rewrite_thy_in_context thy (mk_record_context thy)

(* -------------------------------------------------------------------------
   Recording (includes rewriting)
   ------------------------------------------------------------------------ *)

fun record_thy_raw thy = with_tactictoe_cache (fn () =>
  if mem thy ["min","bool"] then () else
  let
    val context as {scriptorg,dirorg,...} = mk_record_context thy
    val _ = ttt_rewrite_thy_in_context thy context
    (* The manifest may still resolve this identity to an older recording.
       Remove it so only output produced by this child can satisfy the check. *)
    val attempt_file = current_tacdata_file thy
    val _ = remove_file attempt_file
    val _ = print_endline ("ttt_record_thy: " ^ thy ^ "\n  " ^ scriptorg)
    val (_,t) = add_time
      (smlExecScripts.exec_tttrecord_in_dir dirorg)
      (tttsml_of scriptorg)
  in
    print_endline ("ttt_record_thy time: " ^ rts_round 4 t);
    if not (exists_file attempt_file)
    then (print_endline "ttt_record_thy: failed";
          raise ERR "ttt_record_thy" thy)
    else ()
  end)

fun ttt_clean_temp () =
  (
  clean_dir (tactictoe_scratch_dir_of () ^ "/sml_inspection/open");
  clean_dir (tactictoe_scratch_dir_of () ^ "/sml_inspection/buildheap");
  clean_dir (tactictoe_dir_of () ^ "/info");
  clean_dir (tactictoe_scratch_dir_of () ^ "/scripts")
  )

fun ttt_clean_record () =
  (ttt_clean_temp (); clean_dir (tacdata_dir ()))

fun ttt_clean_savestate () =
  (ttt_clean_temp (); clean_dir (tactictoe_dir_of () ^ "/savestate"))

(* record_thy_raw may raise on a theory the rewriter cannot handle
   (upstream limitations in tttUnfold's script rewriting).  Savestate
   recording is not manifest-managed, so wrap each raw call: skip the
   theory, log why, and continue. *)
fun try_record_thy thy =
  record_thy_raw thy
  handle Interrupt => raise Interrupt
       | e =>
    print_endline ("ttt_record_thy: skipped " ^ thy ^ ": " ^ exnMessage e)

(* used to record savestates with record_flag := false *)
fun ttt_record_savestate () =
  let
    val _ = ttt_clean_savestate ()
    val thyl1 = ttt_ancestry (current_theory ())
    val ((),t) = add_time (app try_record_thy) thyl1
  in
    print_endline ("ttt_record time: " ^ rts_round 4 t)
  end

(* -------------------------------------------------------------------------
   Manifest-based recording

   tttManifest owns the on-disk format and the identity of a theory's
   tactic data.  What lives here is the recording policy: which theories
   are stale and why, how to lock them, and in which order (and how many
   at a time) to record them.
   ------------------------------------------------------------------------ *)

datatype record_scope =
    CurrentAncestry
  | Ancestry of string
  | Theories of string list

type record_config =
  { scope        : record_scope,
    parallel     : int,
    force        : bool,
    dry_run      : bool,
    max_lock_age : Time.time }

datatype record_option =
    Scope of record_scope
  | Parallel of int
  | Force of bool
  | DryRun of bool
  | MaxLockAge of Time.time

datatype reason =
    Source_changed
  | Ancestor_recorded of string
  | Manifest_incompatible
  | Tacdata_version_changed
  | Tactictoe_version_changed
  | Missing_data
  | Missing_manifest_line
  | Tampered_data
  | Forced

type record_worker_param =
  { force : bool, max_lock_age_seconds : int,
    tacdata_version : int, tactictoe_version : int,
    src_hashes : (string * string) list, recorded_stale : string list }

fun reason_to_string reason = case reason of
    Source_changed => "source hash changed"
  | Ancestor_recorded dep => "ancestor was recorded this run: " ^ dep
  | Manifest_incompatible => "manifest format changed or manifest missing"
  | Tacdata_version_changed => "tactic-data format version changed"
  | Tactictoe_version_changed => "TacticToe version changed"
  | Missing_data => "tactic data file is missing or failed"
  | Missing_manifest_line => "manifest line is missing"
  | Tampered_data => "data hash differs from manifest"
  | Forced => "forced"

val default_record_config =
  { scope = CurrentAncestry, parallel = 1, force = false, dry_run = false,
    max_lock_age = Time.fromSeconds 7200 }

fun mk_config (scope,parallel,force,dry_run,max_lock_age) : record_config =
  {scope = scope, parallel = parallel, force = force, dry_run = dry_run,
   max_lock_age = max_lock_age}

fun apply_record_option opt ({scope,parallel,force,dry_run,max_lock_age}
    : record_config) =
  case opt of
    Scope x      => mk_config (x,parallel,force,dry_run,max_lock_age)
  | Parallel x   => mk_config (scope,Int.max (1,x),force,dry_run,max_lock_age)
  | Force x      => mk_config (scope,parallel,x,dry_run,max_lock_age)
  | DryRun x     => mk_config (scope,parallel,force,x,max_lock_age)
  | MaxLockAge x => mk_config (scope,parallel,force,dry_run,x)

val record_parallel_dir = ref ""
fun record_parallel_dir_of () =
  if !record_parallel_dir = ""
  then tactictoe_scratch_dir_of () ^ "/parallel/ttt_record"
  else !record_parallel_dir

fun theories_of_scope scope =
  let
    val thyl = case scope of
        CurrentAncestry => ancestry (current_theory ())
      | Ancestry thy => ancestry thy
      | Theories thyl0 => thyl0 @ List.concat (map ancestry thyl0)
  in
    filter (fn x => not (mem x ["min","bool"]))
      (sort_thyl (mk_sameorder_set String.compare thyl))
  end

(* -------------------------------------------------------------------------
   Per-theory locks
   ------------------------------------------------------------------------ *)

fun locks_dir () = tacdata_dir () ^ "/.locks"

(* unique_tmp_suffix is only an owner token: it is not a portable decimal PID.
   Consequently stale detection is deliberately age-based and never removes a
   young lock merely because its token cannot be used for process liveness. *)
fun lock_stale max_lock_age lock =
  let
    val age = Time.- (Time.now (), OS.FileSys.modTime lock)
      handle _ => Time.zeroTime
  in
    Time.compare (age,max_lock_age) = GREATER
  end

fun release_lock lock =
  (remove_file (lock ^ "/holder");
   OS.FileSys.rmDir lock handle _ => remove_file lock handle _ => ())

fun acquire_lock max_lock_age name =
  let
    val _ = app mkDir_err [tacdata_dir (), locks_dir ()]
    val lock = locks_dir () ^ "/" ^ name ^ ".lock"
    fun create () =
      ((HOLFileSys.mkDir lock;
        writel (lock ^ "/holder")
          [Portable.unique_tmp_suffix (), Time.toString (Time.now ())];
        SOME lock)
       handle _ => NONE)
  in
    case create () of
      SOME l => SOME l
    | NONE =>
        if exists_file lock andalso lock_stale max_lock_age lock
        then (release_lock lock; create ())
        else NONE
  end

fun with_manifest_lock max_lock_age f =
  let
    fun loop 0 = raise ERR "with_manifest_lock" "MANIFEST lock held"
      | loop n =
        case acquire_lock max_lock_age "MANIFEST" of
          NONE => (OS.Process.sleep (Time.fromSeconds 1); loop (n - 1))
        | SOME lock =>
            (let val r = f () in release_lock lock; r end
             handle e => (release_lock lock; raise e))
  in
    loop 60
  end

fun update_manifest_entry max_lock_age prov entry =
  with_manifest_lock max_lock_age (fn () =>
    let
      val entries = case read_manifest () of
          NONE => []
        | SOME m => #entries m
    in
      write_manifest prov (update_entry entry entries)
    end)

(* -------------------------------------------------------------------------
   Staleness

   A scan indexes the manifest and the source hashes so that the ancestor
   walk below is a dictionary lookup per ancestor rather than a linear
   scan (and a re-hash) of every theory in scope.
   ------------------------------------------------------------------------ *)

type scan =
  { force : bool,
    prov : provenance,
    man : manifest option,
    src : (string,string) Redblackmap.dict,
    (* entries of the manifest, grouped by theory *)
    entries : (string, entry list) Redblackmap.dict,
    (* theories whose current source has no matching manifest entry *)
    changed : string HOLset.set }

fun src_hash_of (sc : scan) thy =
  SOME (dfind thy (#src sc)) handle NotFound => NONE

fun entries_of (sc : scan) thy = dfind thy (#entries sc) handle NotFound => []

fun lookup_entry (sc : scan) thy =
  case src_hash_of sc thy of
    NONE => NONE
  | SOME src => List.find (entry_matches (#prov sc) src thy) (entries_of sc thy)

fun mk_scan force prov man src_hashes work =
  let
    val src = dnew String.compare src_hashes
    val entries = case man of NONE => [] | SOME m => #entries m
    fun add (e : entry, d) =
      dadd (#thy e) (e :: (dfind (#thy e) d handle NotFound => [])) d
    val index = foldl add (dempty String.compare) entries
    val sc0 = {force = force, prov = prov, man = man, src = src,
               entries = index, changed = HOLset.empty String.compare}
    val changed = HOLset.addList (HOLset.empty String.compare,
      filter (fn thy => not (isSome (lookup_entry sc0 thy))) work)
  in
    {force = force, prov = prov, man = man, src = src, entries = index,
     changed = changed}
  end

fun stale_reason (sc : scan) stale_set thy =
  if #force sc then SOME Forced else
  case #man sc of
    NONE => SOME Manifest_incompatible
  | SOME m =>
    if #tacdata_version m <> #tacdata_version (#prov sc)
    then SOME Tacdata_version_changed
    else if #tactictoe_version m <> #tactictoe_version (#prov sc)
    then SOME Tactictoe_version_changed
    else
    case lookup_entry sc thy of
      (* no entry for the current identity: either the theory was never
         recorded, or its source has moved on from what was recorded *)
      NONE => if null (entries_of sc thy)
              then SOME Missing_manifest_line
              else SOME Source_changed
    | SOME e =>
      let
        val data_file = entry_file e
        val ancestors = ttt_ancestry thy
        fun recorded_this_run dep = mem dep stale_set
        fun source_moved dep = HOLset.member (#changed sc, dep)
      in
        if #failed e then SOME Missing_data
        else if not (exists_file data_file) then SOME Missing_data
        else if sha1_file data_file <> #data_hash e then SOME Tampered_data
        else
          case List.find recorded_this_run ancestors of
            SOME dep => SOME (Ancestor_recorded dep)
          | NONE =>
            case List.find source_moved ancestors of
              SOME dep => SOME (Ancestor_recorded dep)
            | NONE => NONE
      end

type record_plan =
  { provenance : provenance,
    source_hashes : (string * string) list,
    stale : (string * reason) list,
    up_to_date : string list }

fun compute_record_plan force scope : record_plan =
  let
    val prov = current_provenance ()
    val man = read_manifest ()
    val work = theories_of_scope scope
    val src_hashes = map (fn thy => (thy, source_hash thy)) work
    val sc = mk_scan force prov man src_hashes work
    fun step (thy,(stale,up,stale_names)) =
      case stale_reason sc stale_names thy of
        NONE => (stale, thy :: up, stale_names)
      | SOME r => ((thy,r) :: stale, up, thy :: stale_names)
    val (stale,up,_) = foldl step ([],[],[]) work
  in
    {provenance = prov, source_hashes = src_hashes,
     stale = rev stale, up_to_date = rev up}
  end

fun ttt_record_plan scope =
  let val p = compute_record_plan false scope in
    {stale = #stale p, up_to_date = #up_to_date p}
  end

(* -------------------------------------------------------------------------
   Recording one theory
   ------------------------------------------------------------------------ *)

fun record_one (cfg : record_config) prov src_hashes recorded_stale thy =
  let val {force,max_lock_age,...} = cfg in
    case acquire_lock max_lock_age thy of
      NONE =>
        let val msg = "skipped: " ^ thy ^ "  reason: held by another process"
        in print_endline msg; (false,msg) end
    | SOME lock =>
      (let
        (* another process may have recorded this theory, or one of its
           ancestors, since the plan was made: re-read the manifest.  The
           source hashes cannot have changed, so reuse them. *)
        val work = map fst src_hashes
        val sc = mk_scan force prov (read_manifest ()) src_hashes work
      in
        case stale_reason sc recorded_stale thy of
          NONE =>
            let val msg = "up-to-date after lock: " ^ thy in
              print_endline msg; release_lock lock; (true,msg)
            end
        | SOME r =>
          ((print_endline
              ("recording: " ^ thy ^ "  reason: " ^ reason_to_string r);
            record_thy_raw thy;
            let
              val file = current_tacdata_file thy
              val _ = if exists_file file then () else
                raise ERR "record_one" ("missing data after recording " ^ thy)
              val data_hash = sha1_file file
              val src_hash = source_hash thy
              val entry = success_entry prov thy data_hash src_hash
              val msg = "recorded: " ^ thy ^
                "  data=" ^ data_hash ^ "  src=" ^ src_hash
            in
              update_manifest_entry max_lock_age prov entry;
              print_endline msg;
              release_lock lock; (true,msg)
            end)
           handle Interrupt => raise Interrupt
                | e =>
             let
               val src_hash = source_hash thy handle _ => ""
               val entry = failed_entry prov thy src_hash
               val msg = "failed: " ^ thy ^ "  " ^ exnMessage e
             in
               print_endline msg;
               update_manifest_entry max_lock_age prov entry handle _ => ();
               release_lock lock; (false,msg)
             end)
      end
      handle e => (release_lock lock; raise e))
  end

(* -------------------------------------------------------------------------
   Parallel workers
   ------------------------------------------------------------------------ *)

fun worker_value key sl =
  let fun keyed line = case String.tokens Char.isSpace line of
      k :: _ => k = key
    | _ => false
  in
    case List.find keyed sl of
      SOME line =>
        (case String.tokens Char.isSpace line of
           [_,v] => v
         | _ => raise ERR "worker_value" key)
    | NONE => raise ERR "worker_value" key
  end

(* a source hash is empty when the script is not on disk; "-" keeps the
   line shape intact for the reader *)
fun worker_encode s = if s = "" then "-" else s
fun worker_decode s = if s = "-" then "" else s

fun write_worker_param file (p : record_worker_param) =
  let
    fun src_line (thy,h) = String.concatWith " " ["src",thy,worker_encode h]
    fun stale_line thy = "stale " ^ thy
  in
    writel file
      (["force " ^ bts (#force p),
        "max_lock_age_seconds " ^ its (#max_lock_age_seconds p),
        "tacdata_version " ^ its (#tacdata_version p),
        "tactictoe_version " ^ its (#tactictoe_version p)] @
       map src_line (#src_hashes p) @ map stale_line (#recorded_stale p))
  end

fun read_worker_param file =
  let
    val sl = readl file
    fun src line = case String.tokens Char.isSpace line of
        ["src",thy,h] => SOME (thy, worker_decode h)
      | _ => NONE
    fun stale line = case String.tokens Char.isSpace line of
        ["stale",thy] => SOME thy
      | _ => NONE
  in
    { force = string_to_bool (worker_value "force" sl),
      max_lock_age_seconds =
        string_to_int (worker_value "max_lock_age_seconds" sl),
      tacdata_version = string_to_int (worker_value "tacdata_version" sl),
      tactictoe_version = string_to_int (worker_value "tactictoe_version" sl),
      src_hashes = List.mapPartial src sl,
      recorded_stale = List.mapPartial stale sl }
  end

fun record_worker (p : record_worker_param) thy =
  let
    val cfg = mk_config (Theories [], 1, #force p, false,
      Time.fromSeconds (Int.toLarge (#max_lock_age_seconds p)))
    val prov = {tacdata_version = #tacdata_version p,
                tactictoe_version = #tactictoe_version p}
    val _ = load (thy ^ "Theory")
      handle Interrupt => raise Interrupt | _ => ()
    val (ok,msg) =
      record_one cfg prov (#src_hashes p) (#recorded_stale p) thy
  in
    (if ok then "ok " else "fail ") ^ thy ^ "  " ^ msg
  end
  handle Interrupt => raise Interrupt
       | e => "fail " ^ thy ^ "  " ^ exnMessage e

fun record_extspec () =
  let
    val loaded_dirs = map snd (Binarymap.listItems (fileDirMap ()))
    val includes = mk_sameorder_set String.compare
      (map full_path
        (HOLDIR ^ "/src/tactictoe/src" :: loaded_dirs @ !loadPath))
    fun set_bool name r = name ^ " := " ^ bts (!r)
    fun set_real name r = name ^ " := " ^ Real.toString (!r)
    val globals =
      ["tttUnfold.record_parallel_dir := " ^
         mlquote (record_parallel_dir_of ()),
       "aiLib.tactictoe_cache_dir := " ^ mlquote (!tactictoe_cache_dir),
       set_bool "aiLib.debug_flag" debug_flag,
       set_bool "tttSetup.record_flag" record_flag,
       set_bool "tttSetup.record_prove_flag" record_prove_flag,
       set_bool "tttSetup.record_let_flag" record_let_flag,
       set_bool "tttSetup.record_ortho_flag" record_ortho_flag,
       set_bool "tttSetup.ttt_ex_flag" ttt_ex_flag,
       set_bool "tttSetup.record_savestate_flag" record_savestate_flag,
       set_bool "tttSetup.export_thmdata_flag" export_thmdata_flag,
       set_bool "tttSetup.learn_abstract_term" learn_abstract_term,
       set_real "tttSetup.record_tactic_time" record_tactic_time,
       set_real "tttSetup.record_proof_time" record_proof_time,
       set_real "tttSetup.learn_tactic_time" learn_tactic_time,
       set_real "tttSetup.ttt_search_time" ttt_search_time,
       set_real "tttSetup.ttt_tactic_time" ttt_tactic_time]
  in
  {
  self_dir = String.concatWith " " includes,
  self = "(tttUnfold.record_extspec ())",
  parallel_dir = record_parallel_dir_of (),
  reflect_globals = "(" ^ String.concatWith "; " globals ^ ")",
  function = record_worker,
  write_param = write_worker_param,
  read_param = read_worker_param,
  write_arg = (fn file => fn thy => writel file [thy]),
  read_arg = (fn file => hd (readl file)),
  write_result = (fn file => fn s => writel file [s]),
  read_result = (fn file => hd (readl_rm file))
  }
  end

(* -------------------------------------------------------------------------
   Driver
   ------------------------------------------------------------------------ *)

fun ttt_record_cfg (cfg : record_config) =
  let
    val {scope,parallel,force,dry_run,max_lock_age} = cfg
    val plan = compute_record_plan force scope
    val stale = #stale plan
    val up = #up_to_date plan
    val _ = app (fn thy => print_endline ("up-to-date: " ^ thy)) up
    val _ = app (fn (thy,r) => print_endline
      ("stale: " ^ thy ^ "  reason: " ^ reason_to_string r)) stale
  in
    if dry_run then
      print_endline ("ttt_record dry-run: " ^ its (length stale) ^
        " stale, " ^ its (length up) ^ " up-to-date")
    else
      let
        val prov = #provenance plan
        val src_hashes = #source_hashes plan
        val stale_names = map fst stale
        val _ = if parallel <= 1 then () else
          (mkDir_err (tactictoe_scratch_dir_of () ^ "/parallel");
           record_parallel_dir :=
             tactictoe_scratch_dir_of () ^ "/parallel/ttt_record_" ^
             Portable.unique_tmp_suffix ())
        (* the stale theories form a DAG; record them in dependency
           batches so that a theory is only started once every stale
           ancestor of it has been recorded *)
        val stale_set = HOLset.addList (HOLset.empty String.compare,
          stale_names)
        fun stale_deps thy = filter (fn d => HOLset.member (stale_set,d))
          (ttt_ancestry thy)
        val deps = dnew String.compare
          (map (fn thy => (thy, stale_deps thy)) stale_names)
        fun deps_of thy = dfind thy deps handle NotFound => []
        fun make_batches done pending =
          if null pending then [] else
          let
            fun ready thy = all (fn d => HOLset.member (done,d)) (deps_of thy)
            val (readyl,later) = List.partition ready pending
          in
            if null readyl
            then raise ERR "ttt_record_cfg" "dependency cycle"
            else readyl :: make_batches (HOLset.addList (done,readyl)) later
          end
        val batches = make_batches (HOLset.empty String.compare) stale_names
        fun worker_param done =
          { force = force,
            max_lock_age_seconds = IntInf.toInt (Time.toSeconds max_lock_age)
              handle _ => 7200,
            tacdata_version = #tacdata_version prov,
            tactictoe_version = #tactictoe_version prov,
            src_hashes = src_hashes,
            recorded_stale = done }
        fun outcome_ok s = String.isPrefix "ok " s
        fun serial_record done thy =
          let val (ok,msg) = record_one cfg prov src_hashes done thy in
            (if ok then "ok " else "fail ") ^ thy ^ "  " ^ msg
          end
        fun run_parallel done batch =
          let val ncore = Int.min (parallel, length batch) in
            if ncore <= 1 then map (serial_record done) batch else
            let
              val results = parmap_queue_extern ncore
                (record_extspec ()) (worker_param done) batch
                handle Interrupt => raise Interrupt
                     | e =>
                       let
                         val msg = "external worker failure: " ^ exnMessage e
                         val _ = print_endline ("parallel failure: " ^ msg)
                       in
                         map (fn thy => "fail " ^ thy ^ "  " ^ msg) batch
                       end
            in
              app (fn s => print_endline ("parallel result: " ^ s)) results;
              results
            end
          end
        fun run_batch batch (done,failed) =
          let
            fun failed_dep thy = List.find (fn d => mem d failed)
              (ttt_ancestry thy)
            val (runnable,skipped) =
              List.partition (not o isSome o failed_dep) batch
            fun print_skip thy =
              print_endline ("skipped: " ^ thy ^
                "  reason: failed ancestor " ^ valOf (failed_dep thy))
            val _ = app print_skip skipped
            val results =
              if null runnable then [] else run_parallel done runnable
            val pairs = combine (runnable,results)
            val successes = map fst (filter (outcome_ok o snd) pairs)
            val failures = map fst (filter (not o outcome_ok o snd) pairs)
          in
            (done @ successes, failed @ skipped @ failures)
          end
        val ((),t) = add_time (fn () =>
          ignore (foldl (fn (batch,acc) => run_batch batch acc)
            ([],[]) batches)) ()
      in
        print_endline ("ttt_record time: " ^ rts_round 4 t)
      end
  end

fun ttt_record_opts opts =
  ttt_record_cfg
    (foldl (fn (opt,cfg) => apply_record_option opt cfg)
       default_record_config opts)

fun ttt_record () = ttt_record_cfg default_record_config

fun ttt_record_thy thy =
  if mem thy ["min","bool"] then () else
  (ttt_record_opts [Scope (Theories [thy])];
   let val plan = compute_record_plan false (Theories [thy]) in
     if mem thy (#up_to_date plan) then ()
     else raise ERR "ttt_record_thy" thy
   end)


end (* struct *)
