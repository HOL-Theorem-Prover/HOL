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
  mlTacticData tttSetup

val ERR = mk_HOL_ERR "tttUnfold"

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
    then SOME (rm_bbra_str (rm_squote name), namel, term, qtac, cont)
    else NONE
  end
  handle HOL_ERR _ =>
    (
    print_endline ("Warning: extract_store_thm: " ^
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
  | "fun" :: m    => (bval := false; bfun := true; sketch_pattern "fun" "=" m)
  | "and" :: m    => if !bval
                     then sketch_pattern "val" "=" m
                     else sketch_pattern "fun" "=" m
    (* todo: support for mutually recursive functions *)
  | "fn"  :: m    => (bfun := false; sketch_pattern "fn" "=>" m)
  | "|"   :: m    => sketch_pattern "|" (if !bfun then "=" else "=>") m
  | "of"  :: m    => (bfun := false; sketch_pattern "of" "=>" m)
  | "handle" :: m => (bfun := false; sketch_pattern "handle" "=>" m)
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
    else if mem (drop_sig a) store_thm_list andalso hd_code_par m
      then
      case extract_store_thm (tl m) of
        NONE => a :: continue m
      | SOME (name,namel,term,qtac,cont) =>
        let
          val _ = is_thm_flag := true
          val _ = incr n_store_thm
          val tac1 = original_program qtac
          val lflag = mem "let" tac1
          val lflag_name = if lflag then "true" else "false"
          val tac2 = ppstring_stac qtac
        in
          [a,"("] @ original_program namel @ [","] @ original_program term @
          [","] @
            ["let","val","tactictoe_tac1","="] @ tac1 @
            ["val","tactictoe_tac2","=","tttRecord.app_wrap_proof",
             mlquote name,"\n",tac2] @
            ["in","tttRecord.record_proof",
             mlquote name,lflag_name,"tactictoe_tac2","tactictoe_tac1","end"] @
          [")"]
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
          val tac1 = original_program qtac
          val lflag = mem "let" tac1
          val lflag_name = if lflag then "true" else "false"
          val tac2 = ppstring_stac qtac
        in
          [a,"("] @ original_program term @
          [","] @
            ["let","val","tactictoe_tac1","="] @ tac1 @
            ["val","tactictoe_tac2","=","tttRecord.app_wrap_proof",
             mlquote name,"\n",tac2] @
            ["in","tttRecord.record_proof",
             mlquote name,lflag_name,"tactictoe_tac2","tactictoe_tac1","end"] @
          [")"]
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
          handle Interrupt => raise Interrupt | _ => ([],[],[],[])
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

fun is_watch_name x = mem (drop_sig x) (store_thm_list @ name_thm_list)

fun mk_fetch b =
  map (Code o protect)
    ["(","DB.fetch",mlquote (!ttt_unfold_cthy),mlquote b,")"]

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
  (* recording *)
  reflect_flag oc "tttSetup.record_flag" record_flag;
  reflect_flag oc "tttSetup.record_prove_flag" record_prove_flag;
  reflect_flag oc "tttSetup.record_let_flag" record_let_flag;
  reflect_flag oc "tttSetup.ttt_ex_flag" ttt_ex_flag;
  reflect_flag oc "tttSetup.record_savestate_flag" record_savestate_flag;
  reflect_flag oc "tttSetup.export_thmdata_flag" export_thmdata_flag;
  reflect_flag oc "tttSetup.learn_abstract_term" learn_abstract_term;
  reflect_time oc "tttSetup.record_tactic_time" record_tactic_time;
  reflect_time oc "tttSetup.record_proof_time" record_proof_time;
  (* search *)
  reflect_time oc "tttSetup.ttt_search_time" ttt_search_time;
  reflect_time oc "tttSetup.ttt_tactic_time" ttt_tactic_time;
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
    val s1 = HolParser.inputFile file
    val s2 = rm_spaces (rm_comment s1)
    val sl = partial_sml_lexer s2
    val lexdir =  tactictoe_dir ^ "/log/lexer"
    val _ = app mkDir_err [OS.Path.dir lexdir, lexdir]
    val _ = write_sl (lexdir ^ "/" ^ thy) sl
  in
    sketch sl
  end

fun unfold_wrap p = unfold 0 [dnew String.compare (map protect basis)] p

(* ------------------------------------------------------------------------
   Rewriting script
   ------------------------------------------------------------------------ *)

fun tttsml_of file = OS.Path.base file ^ "_ttt.sml"

fun print_program cthy fileorg sl =
  let
    val _ = debug ("print_program: " ^ fileorg)
    val fileout = tttsml_of fileorg
    val scriptdir = tactictoe_dir ^ "/log/scripts"
    val _ = app mkDir_err [OS.Path.dir scriptdir, scriptdir]
    val oc = TextIO.openOut fileout
    fun script_save () =
      let
        val cmd = String.concatWith " "
          ["cp", fileout, scriptdir ^ "/" ^ cthy]
      in
        cmd_in_dir tactictoe_dir cmd
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

fun find_script x =
  let val dir =
    Binarymap.find(fileDirMap(),x ^ "Theory.sml")
    handle NotFound => raise ERR "find_script" ("please load " ^ x ^ "Theory")
  in
    dir ^ "/" ^ x ^ "Script.sml"
  end

fun ttt_rewrite_thy thy =
  if mem thy ["bool","min"] then () else
  let
    val scriptorg = find_script thy
    val dirorg = OS.Path.dir scriptorg
    val _ = print_endline ("ttt_rewrite_thy: " ^ thy ^ "\n  " ^ scriptorg)
    val (_,t) = add_time (rewrite_script thy) scriptorg
  in
    print_endline ("ttt_rewrite_thy time: " ^ rts_round 4 t)
  end

(* -------------------------------------------------------------------------
   Recording (includes rewriting)
   ------------------------------------------------------------------------ *)

fun ttt_ancestry thy =
  filter (fn x => not (mem x ["min","bool"])) (sort_thyl (ancestry thy))

fun exists_tacdata_ancestry thy =
  exists_tacdata_thy thy andalso
  all exists_tacdata_thy (ttt_ancestry thy)

fun ttt_record_thy thy =
  if mem thy ["min","bool"] then () else
  let
    val _ = ttt_rewrite_thy thy
    val scriptorg = find_script thy
    val _ = print_endline ("ttt_record_thy: " ^ thy ^ "\n  " ^ scriptorg)
    val (_,t) = add_time
      smlExecScripts.exec_tttrecord (tttsml_of scriptorg)
  in
    print_endline ("ttt_record_thy time: " ^ rts_round 4 t);
    if not (exists_tacdata_thy thy)
    then (print_endline "ttt_record_thy: failed";
          raise ERR "ttt_record_thy" thy)
    else ()
  end

fun ttt_clean_temp () =
  (
  clean_dir (HOLDIR ^ "/src/AI/sml_inspection/open");
  clean_dir (HOLDIR ^ "/src/AI/sml_inspection/buildheap");
  clean_dir (tactictoe_dir ^ "/info")
  )

fun ttt_clean_record () =
  (ttt_clean_temp (); clean_dir (tactictoe_dir ^ "/ttt_tacdata"))

fun ttt_clean_savestate () =
  (ttt_clean_temp (); clean_dir (tactictoe_dir ^ "/savestate"))

fun ttt_record () =
  let
    val thyl1 = ttt_ancestry (current_theory ())
    val thyl2 = filter (not o exists_tacdata_ancestry) thyl1
    val ((),t) = add_time (app ttt_record_thy) thyl2
  in
    print_endline ("ttt_record time: " ^ rts_round 4 t)
  end

(* used to record savestates with record_flag := false *)
fun ttt_record_savestate () =
  let
    val _ = ttt_clean_savestate ()
    val thyl1 = ttt_ancestry (current_theory ())
    val ((),t) = add_time (app ttt_record_thy) thyl1
  in
    print_endline ("ttt_record time: " ^ rts_round 4 t)
  end



end (* struct *)
