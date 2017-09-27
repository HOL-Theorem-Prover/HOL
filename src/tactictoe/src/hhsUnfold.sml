(* ========================================================================== *)
(* FILE          : hhsUnfold.sml                                              *)
(* DESCRIPTION   : Partial unfolding of SML code.                             *)
(*                 Produces SML strings re-usable in different context.       *)
(*                 Recursive functions are not supported yet.                 *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsUnfold :> hhsUnfold =
struct

open HolKernel Abbrev boolLib hhsLexer hhsTools hhsInfix hhsOpen

val ERR = mk_HOL_ERR "hhsUnfold"

(* --------------------------------------------------------------------------
   Debugging
   -------------------------------------------------------------------------- *)

val hhs_unfold_dir = tactictoe_dir ^ "/unfold_log"
val hhs_scripts_dir = tactictoe_dir ^ "/scripts"
val loadl_glob = ref [] (* not usable: missing a.b *)

(* --------------------------------------------------------------------------
   Program representation and stack
   -------------------------------------------------------------------------- *)

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
  | In

val (infix_glob : (string * infixity_t) list ref) = ref []
val open_cache = ref []

fun hd_code_par2 m = 
  (hd m = Code ("(",Protect) orelse hd m = Code ("{",Protect)) 
  handle _ => false
fun hd_code_par m = 
  (hd m = Code ("(",Protect) handle _ => false)

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
  ["hhsRecord.fetch", mlquote s, mlquote (String.concatWith " " sl)]

fun replace_code1 st = case st of
    (_,Replace sl)  => sl
  | (_,SReplace sl) => sl
  | (s,Protect)     => singleton s
  | (s,Watch)       => (debug_unfold ("replace_code1: " ^ s); singleton s)
  | _               => raise ERR "replace_code1" ""

fun replace_code2 st = case st of
    (s,Replace sl) => 
    (
    if length sl = 1 andalso mem #"." (explode (hd sl)) 
    then mlquote_singleton (String.concatWith " " sl)
    else singleton (String.concatWith " " (record_fetch s sl))
    )
  | (s,SReplace sl) => mlquote_singleton (String.concatWith " " sl)
  | (s,Protect)     => mlquote_singleton s
  | (s,Watch)       => (debug_unfold ("replace_code2: " ^ s);
                       singleton (String.concatWith " " (record_fetch s []))
                       )
  | _               => raise ERR "replace_code2" ""

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
    else g s @ replace_program f g head @ g sep @ 
         replace_program f g body @ replace_program f g m
    )
  | _ => raise ERR "replace_program" ""

fun replace_program1 p = replace_program replace_code1 singleton p
fun replace_program2 p = replace_program replace_code2 mlquote_singleton p

(* --------------------------------------------------------------------------
   Profiling
   -------------------------------------------------------------------------- *)

val open_time = ref 0.0
val replace_special_time = ref 0.0
val replace_id_time = ref 0.0

(* --------------------------------------------------------------------------
   Poly/ML 5.7
   rlwrap poly
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
   Extract pattern and identifiers.
   -------------------------------------------------------------------------- *)

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

(* ---------------------------------------------------------------------------
   Watching and replacing some special values:
   functions calling save_thm
   functions making a definitions
   functions with side effects (export_rewrites) which can be unfolded.
   -------------------------------------------------------------------------- *)

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
  prove_list @
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

val let_flag = ref false

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
  | x :: m => (let_flag := true; split_codelevel_aux i s (x :: pl) m)
    (* raise an error on this line not to simulate buggy version 2
       that has better results than v3 *)
  
fun split_codelevel s sl = 
  (let_flag := false; split_codelevel_aux 0 s [] sl)

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
    val lflag = !let_flag
    val (namel,l0)  = split_codelevel "," body
    val (term,qtac) = split_codelevel "," l0
    val name = original_code (last namel)
  in
    if is_string name 
    then SOME (rm_bbra_str (rm_squote name), namel, term, qtac, lflag, cont)
    else NONE
  end

fun extract_prove sl =
  let  
    val (body,cont) = split_codelevel ")" sl
    val lflag = !let_flag
    val (term,qtac) = split_codelevel "," body
  in
    SOME (term,qtac,lflag,cont)
  end

fun extract_thmname sl =
  let  
    val (body,cont) = split_codelevel ")" sl
    val (namel,_) = split_codelevel "," body
    val name = original_code (last namel)
  in
    if is_string name 
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
    if is_string name 
    then SOME (rm_bbra_str (rm_squote name),cont)
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

fun replace_struct stack id =
  case stack_find stack id of
    SOME (Structure full_id) => [full_id]
  | _ => 
    (if mem #"." (explode id) then () 
     else debug_unfold ("warning: replace_struct: " ^ id); [id])

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
    (if mem #"." (explode id) then () else debug_unfold ("id: " ^ id); 
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

fun load_list_loop sl = case sl of
    []     => ["]"]
  | [a]    => [mlquote a,"]"]
  | a :: m => mlquote a :: "," :: load_list_loop m
  
fun load_list sl = "[" :: load_list_loop sl

val interactive_flag = ref true

fun modified_program inh p = case p of
    [] => []
  | Open sl :: m    => 
    (
    if !interactive_flag
    then loadl_glob := sl @ (!loadl_glob)
    else ()
    ;
    ["open"] @ sl @ [";"] @ modified_program inh m
    )
  | Infix l :: m    => 
    List.concat (map stringl_of_infix l) @ modified_program inh m
  | In :: m         => "in" :: modified_program inh m 
  | Start s :: m    => s :: modified_program inh m
  | End :: m        => "end" :: modified_program inh m
  | Code (a,_) :: m =>
    ( 
    if !interactive_flag andalso a = "export_theory" 
      then modified_program inh m
    else if inh 
      then a :: modified_program inh m
    else if mem (drop_sig a) store_thm_list andalso hd_code_par m
      then
      case extract_store_thm (tl m) of
        NONE => a :: modified_program inh m
      | SOME (name,namel,term,qtac,lflag,cont) =>
        let 
          val _ = incr n_store_thm
          val lflag_name = if lflag then "true" else "false"
          val tac1 = original_program qtac
          val tac2 = ppstring_stac qtac
        in
          [a,"("] @ original_program namel @ [","] @ original_program term @ 
          [","] @
            ["let","val","tactictoe_tac1","="] @ tac1 @
            ["val","tactictoe_tac2","=","hhsRecord.wrap_tactics_in",
             mlquote name,"\n",tac2] @
            ["in","hhsRecord.try_record_proof",
             mlquote name,lflag_name,"tactictoe_tac2","tactictoe_tac1","end"] @
          [")"]
          @ modified_program inh cont
        end
    else if mem (drop_sig a) prove_list andalso hd_code_par m
      then
      case extract_prove (tl m) of
        NONE => a :: modified_program inh m
      | SOME (term,qtac,lflag,cont) =>
        let 
          val name = "tactictoe_prove_" ^ (int_to_string (!n_store_thm))
          val _ = incr n_store_thm
          val lflag_name = if lflag then "true" else "false"
          val tac1 = original_program qtac
          val tac2 = ppstring_stac qtac
        in
          [a,"("] @ original_program term @  
          [","] @
            ["let","val","tactictoe_tac1","="] @ tac1 @
            ["val","tactictoe_tac2","=","hhsRecord.wrap_tactics_in",
             mlquote name,"\n",tac2] @
            ["in","hhsRecord.try_record_proof",
             mlquote name,lflag_name,"tactictoe_tac2","tactictoe_tac1","end"] @
          [")"]
          @ modified_program inh cont
        end
    else a :: modified_program inh m
    )
  | Pattern (s,head,sep,body) :: m => 
    s :: modified_program true head @ [sep] @ 
    modified_program (s <> "val") body @ 
    (if mem s ["val","fun"] then [";"] else []) @ 
    modified_program false m

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
        val (l1,l2,l3,l4) = read_open s handle Io _ => export_struct s
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
   Functions for which we know how to extract the name of the theorem from
   its arguments.
   -------------------------------------------------------------------------- *)  

fun is_watch_name x = mem (drop_sig x) (store_thm_list @ name_thm_list)

fun mk_fetch b =
  map (Code o protect) 
    ["(","DB.fetch",mlquote (!cthy_unfold_glob),mlquote b,")"]

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
  
(* ---------------------------------------------------------------------------
   Main call
   -------------------------------------------------------------------------- *)

fun extract_thy file =
  let 
    val suffix = last (String.tokens (fn x => x = #"/") file)
    val cthy = String.substring (suffix, 0, 
      String.size suffix - String.size "Script.sml")
  in
    cthy
  end

val oc = ref TextIO.stdOut
fun os s = TextIO.output (!oc, s)
fun osn s = TextIO.output (!oc, s ^ "\n")

fun rm_endline s =
  let fun f c = if c = #"\n" then #" " else c in implode (map f (explode s)) end

fun is_break s =
  mem s [
   "end", "in", "val", "fun",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr",
   "and", "datatype", "type", "local","let",";"]

fun print_sl sl = case sl of
    []     => () 
  | a :: m => (if is_break a then os ("\n" ^ a) else os (" " ^ a); 
               print_sl m)
               
val infix_decl = tactictoe_dir ^ "/src/infix_file.sml"

fun output_header cthy file = 
  (
  (* Necessary because of cakeml auto-documentation. *)
  app osn
  [
  "(* ========================================================================== *)",
  "(* This file was modifed by TacticToe.                                        *)",
  "(* ========================================================================== *)"
  ];
  osn "load \"hhsRecord\";";
  if !interactive_flag 
  then 
    let 
      val temp = hhs_code_dir ^ "/" ^ cthy ^ "_holdep"
      val cmd = HOLDIR ^ "/bin/holdeptool.exe " ^ file ^ " > " ^ temp 
      val _ = OS.Process.system cmd
      val sl = map mlquote (readl temp)
    in
      osn "hhsRecord.set_irecord ();";
      osn "fun load_err s = load s handle _ => ();";
      osn ("List.app load_err [" ^ String.concatWith ", " sl ^ "];")
    end
  else osn "hhsRecord.set_erecord ();"
  ;
  app os (bare_readl infix_decl);
  os "open hhsRecord;\n";
  os ("val _ = hhsRecord.start_thy " ^ mlquote cthy)
  )

fun output_foot cthy file = 
  os ("\nval _ = hhsRecord.end_thy " ^ mlquote cthy)

fun start_unfold_thy cthy =
  (
  print_endline cthy;
  loadl_glob := [];
  cthy_unfold_glob := cthy;
  mkDir_err hhs_open_dir;
  mkDir_err hhs_unfold_dir;
  erase_file (hhs_unfold_dir ^ "/" ^ cthy);
  if not (!interactive_flag)
  then   
     (
     mkDir_err hhs_scripts_dir;
     erase_file (hhs_scripts_dir ^ "/" ^ cthy)
     )
  else ()
  ;
  (* statistics *)
  n_store_thm := 0;
  open_time := 0.0; 
  replace_special_time := 0.0;
  replace_id_time := 0.0;
  push_time := 0.0;
  (* initial stack *)
  infix_glob := overlay_infixity;
  (* cache *)
  open_cache := []
  )

fun end_unfold_thy () =
  let 
    val n = !n_store_thm
    fun f s r = debug_unfold (s ^ ": " ^ Real.toString (!r)) 
  in
    print_endline (int_to_string n ^ " proofs unfolded");
    debug_unfold (int_to_string n ^ " proofs unfolded");
    f "Push" push_time;
    f "Open" open_time;
    f "Replace special" replace_special_time;
    f "Replace id" replace_id_time
  end

fun unquoteString s =
  let
    val fin  = tactictoe_dir ^ "/code/quoteString1"
    val fout = tactictoe_dir ^ "/code/quoteString2"
    val cmd = HOLDIR ^ "/bin/unquote" ^ " " ^ fin ^ " " ^ fout   
  in
    writel fin [s]; 
    ignore (OS.Process.system cmd);
    String.concatWith " " (readl fout)
  end

val copy_scripts = tactictoe_dir ^ "/copy_scripts.sh"

fun sketch_wrap file =
  let
    val sl = readl file
    val s1 = rm_endline (rm_comment (String.concatWith " " sl))
    val s2 = unquoteString s1
    val sl3 = hhs_lex s2
  in
    sketch sl3
  end

fun unfold_wrap p =
  let val basis_dict = dnew String.compare (map protect basis) in
    unfold 0 [basis_dict] p
  end

(* ---------------------------------------------------------------------------
   Evaluation version
   -------------------------------------------------------------------------- *)

fun erewrite_script file = 
  if extract_thy file = "bool" then () else
  let
    val _ = interactive_flag := false
    val cthy = extract_thy file
    val _ = start_unfold_thy cthy
    val local_file = rm_prefix file (HOLDIR ^ "/")
    val file_out = hhs_scripts_dir ^ "/" ^ cthy
    val p0 = sketch_wrap file
    val p2 = unfold_wrap p0
    val sl5 = modified_program false p2
  in
    if !n_store_thm = 0 then () else
    (
    oc := TextIO.openOut file_out;
    output_header cthy file;
    print_sl sl5;
    output_foot cthy file;
    TextIO.closeOut (!oc);
    end_unfold_thy ();
    append_endline copy_scripts 
      (String.concatWith " " ["cp",quote file_out,quote local_file])
    )
  end

fun hol_scripts () =
  let 
    val file = tactictoe_dir ^ "/code/theory_list"
    val sigdir = HOLDIR ^ "/sigobj"
    val cmd0 = "cd " ^ sigdir
    val cmd1 = "readlink -f $(find -regex \".*[^/]Theory.sig\") > " ^ file
    val cmd2 = "sed -i 's/Theory.sig/Script.sml/g' " ^ file
  in
    ignore (OS.Process.system (cmd0 ^ "; " ^ cmd1 ^ "; " ^ cmd2));
    readl file
  end

fun erewrite_hol_scripts () =
  (
  erase_file copy_scripts;
  app erewrite_script (hol_scripts ())
  )

fun hol_examples_scripts () =
  let 
    val file = tactictoe_dir ^ "/code/theory_list"
    val dir = HOLDIR ^ "/examples"
    val cmd0 = "find " ^ dir ^ " -name \"*Theory.uo\" > " ^ file
    val cmd1 = "sed -i 's/Theory.uo/Script.sml/' " ^ file
  in
    ignore (OS.Process.system (cmd0 ^ "; " ^ cmd1));
    readl file
  end

fun cakeml_scripts cakeml_dir =
  let 
    val file = tactictoe_dir ^ "/code/theory_list"
    val cmd0 = "find " ^ cakeml_dir ^ " -name \"*Theory.uo\" > " ^ file
    val cmd1 = "sed -i 's/Theory.uo/Script.sml/' " ^ file
  in
    ignore (OS.Process.system (cmd0 ^ "; " ^ cmd1));
    readl file
  end

(* ---------------------------------------------------------------------------
   Interactive version
   -------------------------------------------------------------------------- *)

fun name_inter file = #base (OS.Path.splitBaseExt file) ^ "_tactictoe.sml"

fun print_program cthy file sl =
  if !n_store_thm = 0 then () else
  let val file_out = name_inter file in
    oc := TextIO.openOut file_out;
    output_header cthy file;
    print_sl sl;
    output_foot cthy file;
    TextIO.closeOut (!oc)
  end

fun irewrite_script file =
  if extract_thy file = "bool" then () else
  let
    val _ = interactive_flag := true
    val cthy = extract_thy file
    val _ = start_unfold_thy cthy
    val p0 = sketch_wrap file
    val p2 = unfold_wrap p0
    val sl5 = modified_program false p2
  in
    print_program cthy file sl5;
    end_unfold_thy ()
  end

fun irecord_script file =
  (irewrite_script file; run_hol (name_inter file))
  
end (* struct *)

(* ---------------------------------------------------------------------------
  HOL:  
  hol_scripts ();
  
  rlwrap hol
  load "hhsUnfold";
  open hhsUnfold;
  
  app irewrite_script (hol_scripts ());
  app irecord_script (hol_scripts ());
  
  irecord_script "/home/tgauthier/HOL/src/1/ConseqConvScript.sml";
  record_script "complexScript.sml";
  erewrite_hol_scripts ();
  --------------------------------------------------------------------------- *)
  
  
(* ---------------------------------------------------------------------------
  CAKEML:
  
  screen -s cakeml
  cd cakeml/compiler/backend/proofs
  /home/thibault/big/HOL/bin/Holmake
  PATH=$PATH:"$HOME/HOL/bin"
  cd /home/thibault/big
  sh link_sigobj.sh
  cd HOL/src/tactictoe/src
  /home/thibault/big/HOL/bin/Holmake
 
  rlwrap ../HOL/bin/hol
  load "hhsUnfold";
  open hhsTools;
  open hhsUnfold;
  val l = all_examples_files () @ all_cakeml_files ();
  app hhs_rewrite l;         
  --------------------------------------------------------------------------- *)
  
