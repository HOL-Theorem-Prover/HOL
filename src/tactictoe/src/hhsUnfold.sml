(* ========================================================================== *)
(* FILE          : hhsUnfold.sml                                              *)
(* DESCRIPTION   : Partial unfolding of SML code.                             *)
(*                 Produces SML strings re-usable in different context.       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsUnfold :> hhsUnfold =
struct

(* Constructors and recursive functions are not supported *)

open HolKernel Abbrev boolLib hhsLexer hhsTools hhsInfix hhsExec hhsOpen

val ERR = mk_HOL_ERR "hhsUnfold"

datatype stack_t =
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
  
datatype sketch_t =
    Pattern  of string * sketch_t list * string * sketch_t list
  | Open     of string list
  | Infix    of (string * infixity_t) list
  | Code     of string * stack_t
  | Start    of string
  | End
  | SEnd    
  | In

val extract_err_glob = ref (tactictoe_dir ^ "/extract_err_here")
fun print_error s = append_file (!extract_err_glob) (s ^ "\n")
fun print_warning s = append_file ((!extract_err_glob) ^ "_warning") (s ^ "\n")

val (infix_glob : (string * infixity_t) list ref) = ref []
val open_cache = ref []
val cthy_stack_dict = ref (dempty String.compare)
val cthy_glob = ref ""
val name_number = ref 0
fun incr x = x := (!x) + 1

fun hd_code_par2 m = 
  (hd m = Code ("(",Protect) orelse hd m = Code ("{",Protect)) 
  handle _ => false
fun hd_code_par m = 
  hd m = Code ("(",Protect) handle _ => false

(* --------------------------------------------------------------------------
   Program extraction
   -------------------------------------------------------------------------- *)

fun stringl_of_infix (a,b) = case b of
    Inf_left n  => ["infix" ,int_to_string n,a] 
  | Inf_right n => ["infixr",int_to_string n,a] 

fun original_program p = case p of
    [] => []
  | Open sl :: m    => ("open" :: sl) @ original_program m
  | Infix l :: m    => List.concat (map stringl_of_infix l) @ original_program m
  | In :: m           => "in" :: original_program m 
  | Start s :: m      => s :: original_program m
  | End :: m          => "end" :: original_program m
  | SEnd :: m => "end" :: original_program m
  | Code (a,_) :: m   => a :: original_program m
  | Pattern (s,head,sep,body) :: m => 
    s :: original_program head @ [sep] @ original_program body @ 
    original_program m

fun bbody_of n p = case p of
    [] => []
  | Open _ :: m     => bbody_of n m 
  | Infix _ :: m    => bbody_of n m
  | In :: m         => bbody_of (n-1) m 
  | Start "structure" :: m => bbody_of (n+1) m
  | SEnd :: m => bbody_of (n-1) m
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
fun replace_code1 st = case st of
    (_,Replace sl) => sl
  | (_,SReplace sl) => sl
  | (s,Protect)    => singleton s
  | (s,Watch)      => (print_error ("replace_code: " ^ s); singleton s)
  | _              => raise ERR "replace_code" "should not happen"

fun mlquotecat s = [mlquote s, "^",mlquote " ","^"] 
fun replace_code2 st = case st of
    (s,Replace sl) => 
    (
    if length sl = 1 andalso mem #"." (explode (hd sl)) 
    then mlquotecat (String.concatWith " " sl)
    else 
    ["(","hhsOnline.fetch_thm",mlquote s,
     mlquote (String.concatWith " " sl),")","^",mlquote " ","^"]
    )
  | (s,SReplace sl) => mlquotecat (String.concatWith " " sl)
  | (s,Protect)    => mlquotecat s
  | (s,Watch)      => 
    (
    print_error ("replace_code2: " ^ s); 
    ["(","hhsOnline.fetch_thm",mlquote s,mlquote "",")","^",mlquote " ","^"]
    )
  | _              => raise ERR "replace_code2" "should not happen"

(* forget "op" in a body that does not contains definitions *)
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
    else g s @ replace_program f g head @ g sep @ replace_program f g body @ 
         replace_program f g m
    )
  | _ => raise ERR "replace_program" ""

fun replace_program1 p = replace_program replace_code1 singleton p
fun replace_program2 p = replace_program replace_code2 mlquotecat p

(* --------------------------------------------------------------------------
   Profiling
   -------------------------------------------------------------------------- *)

val open_time = ref 0.0
val replace_special_time = ref 0.0
val replace_id_time = ref 0.0

(* --------------------------------------------------------------------------
   Reserved tokens
   -------------------------------------------------------------------------- *)

val reserved_dict =
  dnew String.compare
  (map (fn x => (x,()))
  ["op", "if", "then", "else", "val", "fun",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr", "andalso", "orelse",
   "and", "datatype", "type", "where", ":", ";" , ":>",
   "let", "in", "end", "while", "do",
   "local","=>","case","of","_","|","fn","handle","raise","#",
   "[","(",",",")","]","{","}"])

fun is_string s = String.sub (s,0) = #"\"" handle _ => false
fun is_number s = Char.isDigit (String.sub (s,0)) handle _ => false
fun is_chardef s = String.substring (s,0,2) = "#\"" handle _ => false

val is_reserved_time = ref 0.0

fun is_reserved_aux s =
  dmem s reserved_dict orelse
  is_number s orelse is_string s orelse is_chardef s

fun is_reserved s = total_time is_reserved_time is_reserved_aux s

(* --------------------------------------------------------------------------
   Default PolyML values:
   val l = map (fn (a,b) => a) (#allVal (PolyML.globalNameSpace) ());
   -------------------------------------------------------------------------- *)

val basis = String.tokens Char.isSpace 
(
"Size trunc ignore Empty Span :: Chr length LESS round vector EQUAL app " ^
"~ Subscript NONE ceil getOpt str substring use o explode foldr foldl ^ " ^ 
"exnMessage Option SOME tl Overflow null @ > = < ref Fail div nil before " ^ 
"real print ord / - rev + * implode map ! size isSome Div mod GREATER Match " ^ 
"false abs <> exnName Domain Bind true >= valOf <= not := hd chr concat floor"
);

(* --------------------------------------------------------------------------
   Rebuild store_thm calls
   -------------------------------------------------------------------------- *)

fun unquote s =
  if String.sub (s,0) = #"\"" andalso String.sub (s,String.size s - 1) = #"\""
  then String.substring (s, 1, String.size s - 2)
  else raise ERR "unquote" s

fun rm_last_char s = String.substring (s, 0, String.size s - 1)

fun rm_bbra bbra charl =
  case charl of
      [] => []
  | #"[" :: m => rm_bbra true m
  | #"]" :: m => rm_bbra false m
  | a :: m => if bbra then rm_bbra true m else a :: rm_bbra false m

fun rm_bbra_str s = implode (rm_bbra false (explode s))

(* --------------------------------------------------------------------------
   Record global values as string for further references
   -------------------------------------------------------------------------- *)

fun is_endtype opar s =
  opar <= 0 andalso
  mem s [
   "end", "in", "val", "fun", "=",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr",
   "and", "datatype", "type", "local", ";", ")","]","}"
   ]

fun is_break s =
  mem s [
   "end", "in", "val", "fun",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr",
   "and", "datatype", "type", "local","let",";"]

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


(* --------------------------------------------------------------------------
   Extract pattern and identifiers
   -------------------------------------------------------------------------- *)

fun extract_pattern s sl =
  let 
    val (head,l2) = split_level s sl 
    handle _ => raise ERR "extract_pattern" (String.concatWith " " sl)
    val (body,cont) = split_endval l2
  in
    (head,body,cont)
  end

(* --------------------------------------------------------------------------
   Extract open calls
   -------------------------------------------------------------------------- *)

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

(* ---------------------------------------------------------------------------
   Watching and replacing some special values:
   functions calling save_thm (* not in Script *)
   functions making a definitions
   functions with side effects (export_rewrites) which can be unfolded.
   -------------------------------------------------------------------------- *)

fun drop_sig s = last (String.tokens (fn x => x = #".") s)
fun sig_of s = hd (String.tokens (fn x => x = #".") s)

val store_thm_list =
  ["store_thm","maybe_thm","Store_thm","asm_store_thm"]

val name_thm_list =
  ["save_thm","new_specification",
  "new_definition","new_infixr_definition","new_infixl_definition",
  "new_type_definition"]

val prove_list = ["prove","TAC_PROOF"]


val watch_list_init = 
  store_thm_list @
  name_thm_list @
  ["tprove"] @
  ["store_definition",
   "zDefine","qDefine","bDefine","tDefine","xDefine","dDefine",
   "export_rewrites"] @
  ["save_defn","defnDefine","primDefine","tDefine","xDefine","Define",
   "multiDefine","apiDefine","apiDefineq","std_apiDefine","std_apiDefineq",
   "xDefineSchema","DefineSchema"] @
  ["mk_fp_encoding"] @
  ["Hol_reln","xHol_reln","Hol_mono_reln","add_mono_thm","export_mono",
   "add_rule_induction","export_rule_induction"] @
  ["Hol_coreln","xHol_coreln","Hol_mono_coreln","new_coinductive_definition"] @
  ["new_list_rec_definition"] @
  ["define_new_type_bijections"] @
  ["new_binder_definition"] @
  ["new_recursive_definition","define_case_constant"] @
  ["define_equivalence_type"] @
  ["define_quotient_type","define_quotient_lifted_function",
   "define_quotient_types_rule","define_quotient_types_full",
   "define_quotient_types_full_rule","define_quotient_types_std",
   "define_quotient_types_std_rule","define_equivalence_type",
   "define_subset_types","define_subset_types_rule"]
  
  
val watch_dict = dnew String.compare (map (fn x => (x,())) watch_list_init)

(* --------------------------------------------------------------------------
   Extract calls  
   -------------------------------------------------------------------------- *)

fun split_codelevel_aux i s pl program = case program of
    []     => raise ERR "split_codelevel_aux" s
  | Code (a,tag) :: m => 
    if a = s andalso i <= 0
      then (rev pl, m) 
    else if mem a ["let","local","struct","(","[","{"]
      then split_codelevel_aux (i + 1) s (Code (a,tag) :: pl) m
    else if mem a ["end",")","]","}"]
      then split_codelevel_aux (i - 1) s (Code (a,tag) :: pl) m
    else split_codelevel_aux i s (Code (a,tag) :: pl) m
  | _ => raise ERR "split_codelevel_aux" s
  
fun split_codelevel s sl = split_codelevel_aux 0 s [] sl

fun rpt_split_codelevel s sl = 
  let val (a,b) = split_codelevel s sl handle _ => (sl,[]) 
  in
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
    if is_string name 
    then SOME (rm_bbra_str (unquote name), namel, term, qtac, cont)
    else NONE
  end
  handle _ => NONE

fun extract_prove sl =
  let  
    val (body,cont) = split_codelevel ")" sl
    val (term,qtac) = split_codelevel "," body
  in
    SOME (term, qtac, cont)
  end
  handle _ => NONE

fun extract_thmname sl =
  let  
    val (body,cont) = split_codelevel ")" sl
    val (namel,_) = split_codelevel "," body
    val name = original_code (last namel)
  in
    if is_string name 
    then SOME (rm_bbra_str (unquote name),cont)
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
    if is_string name 
    then SOME (rm_bbra_str (unquote name),cont)
    else NONE
  end
  handle _ => NONE

(* --------------------------------------------------------------------------
   Extract a program sketch
   -------------------------------------------------------------------------- *)

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
  | "fun" :: m    => (bval := false; bfun := true; sketch_pattern "fun" "=" m)
  | "and" :: m    => if !bval 
                     then sketch_pattern "val" "=" m
                     else sketch_pattern "fun" "=" m (* todo *)
  | "fn"  :: m    => (bfun := false; sketch_pattern "fn" "=>" m)
  | "|"   :: m    => sketch_pattern "|" (if !bfun then "=" else "=>") m
  | "of"  :: m    => (bfun := false; sketch_pattern "of" "=>" m)
  | "handle" :: m => (bfun := false; sketch_pattern "handle" "=>" m)
  | "local" :: m  => Start "local" :: sketch m
  | "let" :: m    => Start "let" :: sketch m
  | "structure" :: m => (* removing structures *)
    let 
      val (l,cont) = split_level "end" m
      val (head,body) = split_level "=" l
    in
      sketch body @ [Code(";",Protect)] @ sketch cont
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

(* --------------------------------------------------------------------------
   Stack
   -------------------------------------------------------------------------- *)

val push_time = ref 0.0

fun push_stackv_aux in_flag (k,v) stack = 
  if in_flag <= 0 
  then dadd k v (hd stack) :: tl stack
  else hd stack :: push_stackv_aux (in_flag - 1) (k,v) (tl stack)
  
fun push_stackvl_aux in_flag stackvl stack = 
  if in_flag <= 0 
  then daddl stackvl (hd stack) :: tl stack
  else hd stack :: push_stackvl_aux (in_flag - 1) stackvl (tl stack)

fun push_stackv in_flag (k,v) stack =
  total_time push_time (push_stackv_aux in_flag (k,v)) stack

fun push_stackvl in_flag stackvl stack = 
  total_time push_time (push_stackvl_aux in_flag stackvl) stack



fun stack_find stack id = case stack of
    []        => NONE
  | dict :: m => (SOME (dfind id dict) handle _ => stack_find m id)
  
(* todo: shouldn't mix names of structures and values in the same stack 
   because some structures are overwritten.
*)  
fun replace_struct stack id =
  case stack_find stack id of
    SOME (Structure full_id) => [full_id]
  | _ => 
    (if mem #"." (explode id) 
     then () 
     else print_warning ("structure: " ^ id); [id])



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
    (if mem #"." (explode id) then () else print_error ("id: " ^ id); 
    SReplace [id])

fun let_in_end s head body id =
  ["let",s] @ head @ ["="] @ body @ ["in",id,"end"] 

val n_store_thm = ref 0
fun modified_program p = case p of
    [] => []
  | Open sl :: m    => ("open" :: sl) @ [";"] @ modified_program m
  | Infix l :: m    => List.concat (map stringl_of_infix l) @ modified_program m
  | In :: m         => "in" :: modified_program m 
  | Start s :: m    => s :: modified_program m
  | End :: m        => "end" :: modified_program m
  | SEnd :: m       => "end" :: modified_program m
  | Code (a,_) :: m =>
    (
    if mem (drop_sig a) store_thm_list
       andalso
       hd_code_par m
    then
      case extract_store_thm (tl m) of
        NONE => a :: modified_program m
      | SOME (name, namel, term, qtac, cont) =>
        let 
          val _ = incr n_store_thm
          val tac1 = original_program qtac
          val tac2 = replace_program2 (bare_body qtac) 
            handle _ => 
            raise ERR "modified_program" (String.concatWith " " tac1)
          val stac2 = String.concatWith " " (tac2 @ [mlquote ""])
        in
          [a,"("] @ 
            original_program namel @ 
          [","] @
            original_program term @ 
          [","] @
            ["let","val","tactictoe_tac1","="] @ tac1 @
            ["val","tactictoe_tac2","=","hhsPrerecord.hhs_prerecord",
             mlquote name,"(",stac2,")"] @
            ["val","_","=","hhsRecord.record_theorems", 
             mlquote (current_theory ())] @
            ["in","tactictoe_tac2","ORELSE","tactictoe_tac1","end"] @
          [")"]
          @ modified_program cont
        end
    else a :: modified_program m
    )
  | Pattern (s,head,sep,body) :: m => 
    s :: modified_program head @ [sep] @ modified_program body @ 
    (if mem s ["val","fun"] then [";"] else []) @
    modified_program m

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
        val open_dir = tactictoe_dir ^ "/open/" ^ s 
        val _ = OS.FileSys.mkDir open_dir handle _ => ()
        val (l1,l2,l3) = 
          ((readl (open_dir ^ "/values"),
           readl (open_dir ^ "/constructors"),
           readl (open_dir ^ "/exceptions"))
           handle Io _ => all_values s)
        val l4 = readl (open_dir ^ "/structures") 
           handle Io _ => all_structures s
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

fun open_struct stack s' = total_time open_time (open_struct_aux stack) s'
          
(* ---------------------------------------------------------------------------
   Recording proofs and theorems produced by prove, tprove and 
   TAC_PROOF by replacing them with a call to store_thm.
   -------------------------------------------------------------------------- *)

fun mk_prove qflag term tac =
  let 
    val name = "tactictoe_thm_" ^ int_to_string (!name_number)
    val _    = incr name_number
    val head = Code ("boolLib.store_thm", Watch)
    val tm   = if qflag 
               then map (Code o protect) ["Parse.Term","("] @ term @ 
                    map (Code o protect) [")"] 
               else term
    val body = 
      [Code ("(",Protect),Code (mlquote name,Protect),Code (",",Protect)] @
      tm @
      [Code (",",Protect)] @
      tac @
      [Code (")",Protect)]
  in
    head :: body
  end
  
fun replace_err sl = 
  print_error ("replace_spec: " ^ String.concatWith " " (first_n 10 sl))

fun replace_spec sl = case sl of
    [] => []
  | Code (s, Watch) :: m =>
    if mem (drop_sig s) prove_list andalso hd_code_par m
    then 
      (
      case extract_prove (tl m) of
        NONE => (replace_err (original_program sl); 
                 Code (s, Watch) :: replace_spec m)
      | SOME (term,tac,cont) => 
        mk_prove (sig_of s = "Q") term tac @ replace_spec cont
      )
    else Code (s, Watch) :: replace_spec m
  | a :: m => a :: replace_spec m
  
(* ---------------------------------------------------------------------------
   Functions for which we know how to extract the name of the theorem from
   its arguments.
   -------------------------------------------------------------------------- *)  



fun is_watch_name x = mem (drop_sig x) (store_thm_list @ name_thm_list)

fun mk_fetch b = 
  map (Code o protect) ["(","DB.fetch",mlquote (!cthy_glob),mlquote b,")"]

fun replace_fetch l = case l of
    [] => []
  | Code(a,Watch) :: m =>
    (
    if is_watch_name a andalso hd_code_par2 m
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
  
(* --------------------------------------------------------------------------
   Unfold the program.
   -------------------------------------------------------------------------- *)
  
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

fun fetch_theorems idl =
  let
    fun rep_fetch id = 
      Replace ["(","DB.fetch",mlquote (!cthy_glob),mlquote id,")"]
    val dict = !cthy_stack_dict
    fun f id = 
      if dmem id dict then (id,rep_fetch id)
      else if dmem (id ^ "_def") dict then (id,rep_fetch (id ^ "_def"))
      else if dmem (id ^ "_DEF") dict then (id,rep_fetch (id ^ "_DEF"))
      else (print_error ("watch: " ^ id); (id,Watch))
  in
    mapfilter f idl
  end

fun dest_replace x = 
  case x of 
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
          then 
            if s = "fun" 
            then map watch [hd idl]
            else fetch_theorems idl
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
  | SEnd :: m  => SEnd :: unfold in_flag (tl stack) m
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
  
(* ---------------------------------------------------------------------------
   Main call
   -------------------------------------------------------------------------- *)

fun change_dir1 file =
  if String.isPrefix HOLDIR file then 
    let 
      val suffix = last (String.tokens (fn x => x = #"/") file)
      val cthy = String.substring (suffix, 0, 
        String.size suffix - String.size "Script.sml")
    in
      (tactictoe_dir ^ "/theories/" ^ suffix, cthy) 
    end
  else raise ERR "change_dir1" file

fun change_dir2 file =
  if String.isPrefix HOLDIR file then 
    let 
      val name = String.extract (file, String.size HOLDIR, NONE)
      val hol_par = String.concatWith "/" 
        (butlast (String.tokens (fn x => x = #"/") file))
    in
      (hol_par ^ "/HOL_COPY" ^ name)
    end
  else raise ERR "change_dir" file

val oc = ref TextIO.stdOut
fun os s = TextIO.output (!oc, s)

fun rm_endline s =
  let fun f c = if c = #"\n" then #" " else c in implode (map f (explode s)) end

fun print_sl sl = case sl of
    []     => () 
  | a :: m => (if is_break a then os ("\n" ^ a) else os (" " ^ a); 
               print_sl m)
               
val infix_decl = tactictoe_dir ^ "/src/infix_file.sml"

fun output_header cthy = 
  (
  app os (bare_readl infix_decl);
  os ("open hhsOnline;\n");
  os ("\nval _ = hhsRecord.start_thy " ^ mlquote cthy)
  )

val export_file = tactictoe_dir ^ "/exported"

fun output_foot cthy file = 
  (
  os ("\nval _ = hhsRecord.end_thy " ^ mlquote cthy);
  os ("\n;" ^
      "\nlet val oc = " ^
      "\n  TextIO.openAppend " ^ mlquote export_file ^ 
      "\nin" ^
      "\n  TextIO.output (oc, " ^ mlquote file ^ " ^ \"\\n\")" ^
      "\nend;")
  )

fun clean_unfold cthy =
  let
    val log_dir = tactictoe_dir ^ "/record_log/" ^ cthy
    val _ = OS.FileSys.mkDir log_dir handle _ => ()
    val _ = extract_err_glob := log_dir ^ "/unfold"
  in
    erase_file (!extract_err_glob)
  end

fun start_unfold_thy cthy =
  (
  n_store_thm := 0;
  name_number := 0;
  clean_unfold cthy;
  cthy_glob := cthy;
  infix_glob := overlay_infixity;
  cthy_stack_dict := dnew String.compare (open_struct [] (cthy ^ "Theory"));
  open_cache := [];
  open_time := 0.0; 
  replace_special_time := 0.0;
  replace_id_time := 0.0;
  is_reserved_time := 0.0;
  push_time := 0.0
  )

fun end_unfold_thy cthy n =
  let
    val file = tactictoe_dir ^ "/record_log/" ^ cthy ^ "/unfold_summary"
    val _ = erase_file file
    fun g s r = append_endline file (s ^ ": " ^ Real.toString r)
    val _ = append_endline file (int_to_string n ^ " proofs extracted")
    val _ = print (int_to_string n ^ " proofs extracted\n")
    val _  = g "  Push" (!push_time)
    val _  = g "  Is reserved" (!is_reserved_time)
    val _  = g "  Open" (!open_time)
    val _  = g "  Replace special" (!replace_special_time)
    val _  = g "  Replace id" (!replace_id_time)
  in
    ()
  end

fun hhs_rewrite file = 
  let val (_,cthy) = change_dir1 file in
    if cthy = "bool" then () 
    else
      let
        val _ = print (cthy ^ "\n")
        val _ = start_unfold_thy cthy
        val file_out = change_dir2 file
        val sl = readl file
        val s1 = rm_endline (rm_comment (String.concatWith " " sl))
        val s2 = hhsQuote.quoteString s1
        val sl3 = hhs_lex s2
        val p0 = sketch sl3
        val basis_dict = dnew String.compare (map protect basis)
        val p2 = unfold 0 [basis_dict] p0
        val sl5 = modified_program p2
      in
        oc := TextIO.openOut file_out;
        output_header cthy;
        print_sl sl5;
        output_foot cthy file;
        TextIO.closeOut (!oc);
        end_unfold_thy cthy (!n_store_thm)
      end
  end

fun all_files () =
  let 
    val sigdir = HOLDIR ^ "/sigobj"
    val file = tactictoe_dir ^ "/code/theory_list"
    val cmd0 = "cd " ^ sigdir
    val cmd1 = "readlink -f $(find -regex \".*[^/]Theory.sig\") > " ^ file
    val cmd2 = "sed -i 's/Theory.sig/Script.sml/g' " ^ file
  in
    ignore (OS.Process.system (cmd0 ^ "; " ^ cmd1 ^ "; " ^ cmd2));
    readl file
  end

end (* struct *)

(* ---------------------------------------------------------------------------
  
  
  (* Start *)
  rlwrap hol
  load "hhsUnfold";
  hhsTools.erase_file (hhsTools.tactictoe_dir ^ "/exported");
  open hhsUnfold;
  val l = all_files ();
  app hhs_rewrite l;
  
  (* Restart *)
  load "hhsUnfold";
  open hhsUnfold;
  val l = all_files ();
  val exported = hhsTools.readl (hhsTools.tactictoe_dir ^ "/exported");
  val non_exported = filter (fn x => not (mem x exported)) l;
  app hhs_rewrite non_exported;
  
  todo:
  - structures
  - recursive function
  - detection of state-modifying tactics: warning.
  - types (g:goal).
  - pattern matching. (* case *)                        
  --------------------------------------------------------------------------- *)
