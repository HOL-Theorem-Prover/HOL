(* ========================================================================== *)
(* FILE          : hhsTacticgen.sml                                           *)
(* DESCRIPTION   : Tactic synthetizer. Create new tactics that may not have   *)
(* been seen before.                                                          *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsTacticgen :> hhsTacticgen =
struct

open HolKernel boolLib Abbrev hhsTools hhsExec hhsLexer

val hhs_metis_flag  = ref false
val hhs_mutate_flag = ref false

(* ---------------------------------------------------------------------------
   Add a metis call with automatically generated arguments on top of the 
   predictions.
   -------------------------------------------------------------------------- *)

fun add_metis tacdict thmpredictor (g,pred) =
  if !hhs_metis_flag
  then
    let
      val thml = !thmpredictor g
      fun f s = 
        let val (a,b) = split_string "Theory." s in
          if a = current_theory ()
          then String.concatWith " " ["DB.fetch",mlquote a,mlquote b]
          else s 
        end
      val stac = "metisTools.METIS_TAC [ " ^ String.concatWith " , " 
        (map f thml) ^ " ]"
      val tac = tactic_of_sml stac
    in
      tacdict := dadd stac tac (!tacdict);
      (g, ((stac,0.0,([],F),[]),~ 1.0) :: pred)
    end
    handle _ => (g,pred)
  else (g,pred)


(* ---------------------------------------------------------------------------
   Tokenize tactics
   -------------------------------------------------------------------------- *)

fun rep_open_by_close_aux acc charl = case charl of
    [] => rev acc
  | #"_" :: #"o" :: #"p" :: #"e" :: #"n" :: m => 
    rep_open_by_close_aux (rev (explode "_close") @ acc) m
  | c :: m => rep_open_by_close_aux (c :: acc) m

fun rep_open_by_close s = implode (rep_open_by_close_aux [] (explode s))

(* warning: do not cover special constructs *)
fun tokenize_stac sl = 
  if sl = [] then [] else 
  let val a = hd sl in 
    if hd sl = "let" 
      then 
        let val (body,cont) = split_level "end" sl in
          (true,String.concatWith " " body) :: tokenize_stac ("end" :: cont)
        end
    else if String.isPrefix "hhs_infix" a
      then
        let val (body,cont) = split_level (rep_open_by_close a) sl in
          (false,String.concatWith " " body) :: tokenize_stac cont
        end
    else (not (is_reserved a), a) :: tokenize_stac (tl sl)
  end
 
fun type_tokenl tokenl =
  let fun f (b,s) = 
    if b then (s, SOME (type_of_sml s) handle _ => NONE) else (s,NONE)
  in
    map f tokenl
  end
  
val global_seed = Random.newgen ()
 
fun randInt n = 
  let 
    val nextInt = Random.range (0,n)
    val r = nextInt global_seed 
  in
    if r >= n then randInt n else r 
  end
 
(* tokenization is only approximates but it's ok if typing fails correctly *)
fun find_type n l = case l of
  [] => raise ERR "find_type" ""
  | (_,NONE) :: m => find_type n m 
  | (_,SOME ty) :: m => if n <= 0 then ty else find_type (n-1) m

fun repl_type n e l = case l of
    [] => raise ERR "repl_type" ""
  | (x,NONE) :: m => (x,NONE) :: repl_type n e m 
  | (x,SOME ty) :: m => 
    if n <= 0 then (e,SOME ty) :: m else (x,SOME ty) :: repl_type (n-1) e m
  
fun find_tokens ty stacl = 
  if stacl = [] then [] else
    let 
      val l = type_tokenl (tokenize_stac (hd stacl)) 
      val l1 = List.filter (fn x => snd x = SOME ty) l
    in
      if null l1 then find_tokens ty (tl stacl) else map fst l1
    end

(* ---------------------------------------------------------------------------
   Change one token in a tactic.
   -------------------------------------------------------------------------- *)
    
fun mutate_stac stac old_stacl =
  let 
    val stacl = map hhs_lex (filter (fn x => x <> stac) old_stacl)
    val l = type_tokenl (tokenize_stac (hhs_lex stac))
    val l' = (tl l handle _ => raise ERR "build_new_stac" "")
    val n = length (filter (fn x => snd x <> NONE) l')
    val m = randInt n
    val ty = find_type m l'
    val tokenl = find_tokens ty stacl
  in
    if tokenl = []
      then NONE
      else 
        let 
          val m1 = randInt (length tokenl)
          val e = List.nth (tokenl,m1)
          val new_l = (hd l) :: repl_type m1 e (tl l)
        in
          SOME (String.concatWith " " (map fst new_l))
        end
  end

(* ---------------------------------------------------------------------------
   Add one synthetized tactic after each predicted tactic.
   -------------------------------------------------------------------------- *)

fun add_mutate tacdict (g,pred) =
  if !hhs_mutate_flag then
    let
      val stacl = map (#1 o fst) pred
      fun f (lbl as (stac,t,g1,gl1), score) =
        let 
          val staco = mutate_stac stac stacl
        in
          if mem stac stacl orelse staco = NONE
            then [(lbl,score)] 
            else 
              let 
                val new_stac = valOf staco
                val tac = tactic_of_sml stac
              in
                tacdict := dadd new_stac tac (!tacdict);
                [(lbl,score),((new_stac,t,g1,[]),score + 0.0000001)]
              end
        end
    in
      (g, List.concat (map f pred))
    end 
  else (g,pred)
  
end
