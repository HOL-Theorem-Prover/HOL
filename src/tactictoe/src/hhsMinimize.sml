(* ========================================================================== *)
(* FILE          : hhsMinimize.sml                                            *)
(* DESCRIPTION   : Minimize proof script including minimization               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsMinimize :> hhsMinimize =
struct

open HolKernel boolLib Abbrev hhsTools hhsExec hhsLexer hhsTimeout

val ERR = mk_HOL_ERR "hhsMinimize"

val hhs_minimize_flag = ref false
val hhs_prettify_flag = ref false

(* --------------------------------------------------------------------------
   Tests
   -------------------------------------------------------------------------- *)

fun same_effect stac1 stac2 g =
  let 
    val gl1o = rec_stac stac1 g
    val gl2o = rec_stac stac2 g
  in
    gl1o <> NONE andalso gl2o <> NONE andalso gl1o = gl2o
  end

fun is_proof stac g = (rec_sproof stac g = SOME [])

fun is_effect stac g gl = (rec_stac stac g = SOME gl)

(*----------------------------------------------------------------------------
  Requoting terms. 
  Does not work with the new lexer. 
  Should be applied just before printing.
  ----------------------------------------------------------------------------

fun unquote s =
  if String.sub (s,0) = #"\"" andalso String.sub (s,String.size s - 1) = #"\""
  then String.substring (s, 1, String.size s - 2)
  else raise ERR "unquote" s

fun is_blank c =
  c = #" " orelse c = #"\n" orelse c = #"\t"

fun rm_blank s = implode (filter (not o is_blank) (explode s))

fun add_quote_aux sl = case sl of
    [] =>  ""
  | [a] => a
  | "(" :: a :: "[" :: b :: s :: "]" :: ")" :: m => 
    if mem a ["Parse.Type","Parse.Term"] andalso drop_sig b = "QUOTE" 
      then dquote_cont s m 
      else cont sl
  | "[" :: b  :: s :: "]" :: m =>
    if drop_sig b = "QUOTE" then quote_cont s m else cont sl
  | _ => cont sl
and quote_cont s m =
  "`" ^ (rm_blank o rm_comment o unquote) s ^ "`" ^ " " ^ add_quote_aux m
and dquote_cont s m =
   "``" ^ (rm_blank o rm_comment o unquote) s ^ "``" ^ " " ^ add_quote_aux m
and cont sl = (hd sl) ^ " " ^ add_quote_aux (tl sl)

fun add_quote stac = add_quote_aux (hhs_lex stac)
*)
 
(*----------------------------------------------------------------------------
  Minimizing the space between parentheses
  ----------------------------------------------------------------------------*)
 
fun minspace_sl sl = case sl of
    [] =>  ""
  | [a] => a
  | a :: b :: m =>
    (
    if mem a ["[","("] orelse mem b ["]",")",",",";"] 
      then a ^ minspace_sl (b :: m)
      else a ^ " " ^ minspace_sl (b :: m)
    )

(*----------------------------------------------------------------------------
  Removing module declaration
  ----------------------------------------------------------------------------*)

fun rm_prefix stac =
  let
    val sl = hhs_lex stac
    fun rm_one_prefix s =
      let
        val l = String.tokens (fn x => x = #".") s
        val s' = last l
      in
        if List.length l = 1 orelse not (is_pointer_eq s s') then s else s'
      end
  in
    map rm_one_prefix sl
  end

fun prettify1_stac stac = 
  (minspace_sl o rm_prefix) stac
fun prettify2_stac stac =
  (minspace_sl o hhs_lex) stac

(*----------------------------------------------------------------------------
  Pretty-printing the abstract tree of the proof.
  ----------------------------------------------------------------------------*)
  
datatype Proof = 
    Tactic of (string * goal)
  | Then   of (Proof * Proof)
  | Thenl  of (Proof * Proof list)

fun prettify_proof proof = case proof of
    Tactic (s,g) =>
    let 
      val s1 = prettify1_stac s
      val s2 = prettify2_stac s
    in
      if same_effect s s1 g then Tactic (s1,g)
      else if same_effect s s2 g then Tactic (s2,g)
      else Tactic (s,g)
    end
  | Then (p1,p2) => Then (prettify_proof p1, prettify_proof p2)
  | Thenl (p,pl) => Thenl (prettify_proof p, map prettify_proof pl)

(* only works after a call to add_proofpar *)
fun string_of_proof proof = case proof of
    Tactic (s,_) => s
  | Then (p1,p2) => string_of_proof p1 ^ " THEN " ^ string_of_proof p2
  | Thenl (p,pl) =>     
    let 
      val sl = map string_of_proof pl
      val set = mk_fast_set String.compare sl
    in
      if length set = 1 
      then string_of_proof p ^ " THEN " ^ hd set
      else string_of_proof p ^ " THENL " ^ 
        "[" ^ String.concatWith ", " sl ^ "]"
    end

(*----------------------------------------------------------------------------
  Minimizing the number of elements of lists without changing the effect of
  the tactics. Also removing unnecessary tactics.
  ----------------------------------------------------------------------------*)
 
fun decompose sl = case sl of
    [] => []
  | "[" :: m => 
    let 
      val (body,cont) = split_level "]" m
      val l = map (String.concatWith " ") (rpt_split_level "," body)
    in
      (true, ([],l)) :: decompose cont
    end
  | a :: m => (false, ([],[a])) :: decompose m
  
fun list_to_string sl = "[ " ^ String.concatWith " , " sl ^ " ]"
  
fun group_to_string l =
  let fun to_string (b,(l1',l2')) =  
    if b then list_to_string (l1' @ l2') else hd l2'
  in
    String.concatWith " " (map to_string l)
  end
  
fun minimize_stac g gl pl l = case l of
    [] => group_to_string pl
  | (false,a) :: m => minimize_stac g gl (pl @ [(false,a)]) m
  | (true,(l1,l2)) :: m => 
    if null l2 
    then minimize_stac g gl (pl @ [(true,(l1,l2))]) m
    else 
      let val new_stac = group_to_string  (pl @ [(true, (l1, tl l2))] @ m) in
        if is_effect new_stac g gl 
        then minimize_stac g gl pl ((true, (l1, tl l2)) :: m)
        else minimize_stac g gl pl ((true, (l1 @ [hd l2], tl l2)) :: m)
      end   
        
fun minimize_stac_full stac g =
  let val gl = fst (tactic_of_sml stac g) 
    handle _ => raise ERR "minimize" stac
  in
    minimize_stac g gl [] (decompose (hhs_lex stac))
  end       

fun minimize_stac_g_gl stac g gl =
  let val gl = fst (tactic_of_sml stac g) 
    handle _ => raise ERR "minimize" stac
  in
    minimize_stac g gl [] (decompose (hhs_lex stac))
  end     

fun pretty_stac stac g gl = prettify1_stac (minimize_stac_g_gl stac g gl) 
       
fun minimize_tac proof = case proof of 
    Tactic (s,g) => Tactic (minimize_stac_full s g,g)   
  | Then (p1,p2) => Then (minimize_tac p1, minimize_tac p2)
  | Thenl (p,pl) => Thenl (minimize_tac p, map minimize_tac pl)
 
fun minimize_proof proof = case proof of
    Tactic _ => proof
  | Then (Tactic (_,g),p2) => 
    let val s = string_of_proof p2 in
      if is_proof s g then p2 else proof
    end
  | Then (p1,p2) => Then (minimize_proof p1, minimize_proof p2)
  | Thenl (p,pl) => Thenl (minimize_proof p, map minimize_proof pl)

fun prettify_proof_wrap p =
  if !hhs_prettify_flag then 
    (
    debug "Starting prettification";
    prettify_proof p before debug "End prettification"
    )
  else p

fun minimize_proof_wrap p =
  if !hhs_minimize_flag then 
    (
    debug "Starting minimization";
    minimize_proof (minimize_tac p) before debug "End minimization"
    )
  else p

fun is_infix s = String.isPrefix "hhs_infix" s 

fun should_par i sl = case sl of
    []     => false
  | a :: m => if is_infix a andalso i <= 0
                then true
              else if mem a ["let","local","struct","(","[","{"]
                then should_par (i + 1) m
              else if mem a ["end",")","]","}"]
                then should_par (i - 1) m
              else should_par i m
 
fun add_tacpar s = if should_par 0 (hhs_lex s) then "(" ^ s ^ ")"  else s

fun add_proofpar proof = case proof of
    Tactic (s,g) => Tactic (add_tacpar s,g)
  | Then (p1,p2) => Then   (add_proofpar p1,add_proofpar p2)
  | Thenl (p,pl) => Thenl  (add_proofpar p,map add_proofpar pl)

fun minimize p = 
  (prettify_proof_wrap o minimize_proof_wrap o add_proofpar) p

(*----------------------------------------------------------------------------
  Reconstructing the proof.
  ----------------------------------------------------------------------------*)

fun proof_length proof = case proof of
  Tactic (s,g) => 1
| Then (p1,p2) => proof_length p1 + proof_length p2
| Thenl (p,pl) => proof_length p + sum_int (map proof_length pl)

fun reconstruct g proof =          
  let
    val sproof = string_of_proof proof
    val tac    = tactic_of_sml sproof
      handle _ => raise ERR "reconstruct" sproof
    val tim = 2.0 * (Time.toReal (!hhs_search_time))
    val (_,new_tim) = add_time (timeOut tim Tactical.TAC_PROOF) (g,tac)
      handle _ => 
        (debug ("Error: reconstruct: " ^ sproof);
         raise ERR "reconstruct" sproof)
  in 
    debug ("proof length: " ^ int_to_string (proof_length proof));
    debug ("proof time: " ^ Real.toString new_tim);
    sproof
  end

end (* struct *)
