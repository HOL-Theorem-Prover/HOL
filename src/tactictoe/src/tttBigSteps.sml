(* ========================================================================= *)
(* FILE          : tttBigSteps.sml                                           *)
(* DESCRIPTION   : Successions of non-backtrackable moves chosen after one   *)
(*                 MCTS call for each step                                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure tttBigSteps :> tttBigSteps =
struct

open HolKernel Abbrev boolLib aiLib smlRedirect psMCTS mlTreeNeuralNetwork
  tttToken tttTrain tttSearch tttRecord tacticToe

val ERR = mk_HOL_ERR "tttBigSteps"

(* -------------------------------------------------------------------------
   Global example datasets
   ------------------------------------------------------------------------- *)

type ex = (term * real) list

val exval = ref []
val expol = ref []
val exarg = ref []

datatype bstatus = BigStepsProved | BigStepsSaturated | BigStepsTimeout

fun string_of_bstatus x = case x of
    BigStepsProved => "BigStepsProved"
  | BigStepsSaturated => "BigStepsSaturated"
  | BigStepsTimeout => "BigStepsTimeout"

(* -------------------------------------------------------------------------
   Extracting examples
   ------------------------------------------------------------------------- *)

fun example_val goalrec =
  if #gvis goalrec < 0.5 
  then []
  else [(nntm_of_stateval (#goal goalrec), #gsum goalrec / #gvis goalrec)]

fun example_pol goal argl1 =
  let 
    val argl2 = map_assoc 
      (fn x => if #sstatus x = StacSaturated then 0.0 else #svis x) argl1
    val tot = sum_real (map snd argl2) 
  in
    if tot <= 0.5 orelse length argl2 <= 1 then [] else
    let
      fun f b = b / tot
      val rl = first_n 3 (map snd (dict_sort compare_rmax argl2))
      val _ = print_endline ("tot: " ^ rts tot ^ ", " ^
        String.concatWith " " (map rts rl))
      val argl3 = map_snd f argl2
      val argl4 = map_fst 
        (fn x => hidef nntm_of_statepol (goal,dest_stac (#token x))) argl3 
    in
      argl4
    end
  end

fun example_arg (goal,stac) argl1 =
  let 
    val argl2 = map_assoc 
      (fn x => if #sstatus x = StacSaturated 
               then 0.0 
               else #svis x) argl1
    val tot = sum_real (map snd argl2) 
  in
    if tot <= 0.5 orelse length argl2 <= 1 then [] else
    let
      fun f b = b / tot 
      val rl = first_n 3 (map snd (dict_sort compare_rmax argl2))
      val _ = print_endline ("tot: " ^ rts tot ^ ", " ^ 
        String.concatWith " " (map rts rl))
      val argl3 = map_snd f argl2
      val argl4 = map_fst 
        (fn x => hidef nntm_of_statearg ((goal,stac), #token x)) argl3 
     in
       argl4
     end
  end

(* -------------------------------------------------------------------------
   Selecting bigsteps
   ------------------------------------------------------------------------- *)

fun children_argtree_aux argtree anl i =
  if dmem (i :: anl) argtree then 
    let val child = dfind (i :: anl) argtree in
      if #sstatus child = StacFresh then [] else 
      (i,child) :: children_argtree_aux argtree anl (i+1)
    end
  else []

fun children_argtree argtree anl = children_argtree_aux argtree anl 0

fun root_argtree stacv i = dfind [] (Vector.sub (stacv,i)) 

fun children_stacv_aux stacv i =
  if can (root_argtree stacv) i then 
    let val child = root_argtree stacv i in
      if #sstatus child = StacFresh then [] else 
      (i,child) :: children_stacv_aux stacv (i+1)
    end
  else []

fun children_stacv stacv = children_stacv_aux stacv 0

fun best_arg tree (sn,anl) =
  let
    val node = dfind [] tree
    val goalrec = Vector.sub (#goalv node,0)
    val argtree = Vector.sub (#stacv goalrec,sn)
    val stac = dest_stac (#token (dfind [] argtree))
    val argl1 = children_argtree argtree anl
    val _ = if null argl1 then raise ERR "best_arg" "empty" else ()
    val _ = exarg := example_arg (#goal goalrec, stac) (map snd argl1) @ !exarg
    val argl2 = filter (fn (_,x) => #sstatus x <> StacSaturated) argl1
  in
    if exists (fn (_,x) => #sstatus x = StacProved) argl2
    then fst (valOf (List.find (fn (_,x) => #sstatus x = StacProved) argl2))
    else if null argl2 then 0 else (* unsafe if no predictions *)
    let 
      val argl3 = dict_sort compare_rmax (map_assoc (#svis o snd) argl2)
      val bestan = fst (fst (hd argl3))
    in 
      bestan
    end
  end

fun best_stac tree = 
  let
    val node = dfind [] tree
    val goalrec = Vector.sub (#goalv node,0)
    val _ = exval := example_val goalrec @ !exval
    val argl1 = children_stacv (#stacv goalrec)
    val _ = if null argl1 then raise ERR "best_stac" "empty" else ()
    val _ = expol := example_pol (#goal goalrec) (map snd argl1) @ !expol
    val argl2 = filter (fn (_,x) => #sstatus x <> StacSaturated) argl1
  in
    (* to do change to a softer version of not always selecting 
       the winning path *)
    if exists (fn (_,x) => #sstatus x = StacProved) argl2
    then fst (valOf (List.find (fn (_,x) => #sstatus x = StacProved) argl2))
    else if null argl2 then 0 else (* unsafe if no predictions *)
    let 
      val argl3 = dict_sort compare_rmax (map_assoc (#svis o snd) argl2)
      val bestsn = fst (fst (hd argl3))
    in
      bestsn
    end
  end

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)

val max_bigsteps = 20 

fun stacrec_of tree (sn,anl) = 
  let
    val node = dfind [] tree
    val goalrec = Vector.sub (#goalv node,0)
    val argtree = Vector.sub (#stacv goalrec,sn)
  in
    dfind anl argtree
  end

fun path_to_anl tree (sn,anl) = 
  let
    val node = dfind [] tree
    val goalrec = Vector.sub (#goalv node,0)
    val (goal : goal) = #goal goalrec
    val argtree = Vector.sub (#stacv goalrec,sn)
    val stac = dest_stac (#token (dfind [] argtree))
    fun loop acc anl_aux = 
      if null anl_aux then acc else
      loop (#token (dfind anl_aux argtree) :: acc) (tl anl_aux)
    val tokenl = loop [] anl
  in
    (goal,stac,tokenl)
  end

fun goallist_of_node node = map #goal (vector_to_list (#goalv node))

fun loop_arg searchobj prevtree (sn,anl) =
  let 
    val (goal,stac,tokenl) = path_to_anl prevtree (sn,anl)
    val _ = 
      if null tokenl 
      then print_endline ("Tactic: " ^ stac)
      else print_endline (string_of_token (last tokenl))
    val stacrec = stacrec_of prevtree (sn,anl)
    val argstatus = #sstatus stacrec
    val _ = if argstatus <> StacUndecided 
      then print_endline (string_of_sstatus argstatus) else ()
  in
    if null (#atyl stacrec) then  
      if argstatus = StacProved 
        then SOME [] 
      else if dmem [(0,sn,anl)] prevtree 
        then SOME (goallist_of_node (dfind [(0,sn,anl)] prevtree))
        else NONE
    else
    let
      val starttree = hidef (starttree_of_gstacarg searchobj) 
        (goal,stac,tokenl) 
      val (_,tree) = hidef (search_loop searchobj (SOME 1600)) starttree
      val newanl = List.tabulate (length anl, fn _ => 0)
      val an = best_arg tree (0, newanl)
      val _ = print_endline ("best arg: " ^ its an)
    in
      loop_arg searchobj tree (0, an :: newanl)    
    end
  end

fun loop_stac searchobj g =
  let
    val _ = print_endline ("Goal: " ^ string_of_goal g)
    val starttree = hidef (starttree_of_goal searchobj) g
    val (_,tree) = hidef (search_loop searchobj (SOME 1600)) starttree
    val sn = best_stac tree
    val _ = print_endline ("best tac: " ^ its sn)
  in      
    loop_arg searchobj tree (sn,[])
  end

fun string_of_gl gl = String.concatWith "\n" (map string_of_goal gl) 

fun loop_node searchobj n gl =
  (
  if length gl > 1 then print_endline ("\nOpen goals: " ^ string_of_gl gl)
  else ()
  ;
  if null gl 
    then BigStepsProved
  else if n + length gl > max_bigsteps 
    then BigStepsTimeout
  else
    let val newglol = map (loop_stac searchobj) gl in
      if exists (fn x => not (isSome x)) newglol
      then BigStepsSaturated
      else
        let val newgl = List.concat (map valOf newglol) in
          loop_node searchobj (n + length gl) newgl
        end
     end
  )

fun run_bigsteps searchobj g = 
  let 
    val _ = print_endline "init bigsteps"
    val _ = (exval := []; expol := []; exarg := [])
    val bstatus = loop_node searchobj 0 [g]
    val r = (bstatus,(!exval,!expol,!exarg))
    val _ = (exval := []; expol := []; exarg := [])
  in
    r
  end

fun run_bigsteps_eval (expdir,ngen) (thmdata,tacdata) (vnno,pnno) g =
  let
    val mem = !hide_flag
    val _ = hide_flag := false 
    val pb = current_theory () ^ "_" ^ its (!savestate_level)
    val gendir = expdir ^ "/" ^ its ngen
    val valdir = gendir ^ "/val"
    val poldir = gendir ^ "/pol"
    val argdir = gendir ^ "/arg"
    val resdir = gendir ^ "/res"
    val errdir = gendir ^ "/err"
    val _ = app mkDir_err [expdir,gendir,valdir,poldir,argdir,resdir,errdir];
    val _ = print_endline "searchobj"
    val searchobj = build_searchobj (thmdata,tacdata) (NONE,NONE) g
      handle Interrupt => raise Interrupt 
        | e => (append_endline (errdir ^ "/" ^ pb) "searchobj"; raise e)
    val _ = print_endline "run_bigsteps"
    val (bstatus,(exv,exp,exa)) = run_bigsteps searchobj g
      handle Interrupt => raise Interrupt 
        | e => (append_endline (errdir ^ "/" ^ pb) "run_bigsteps"; raise e)
  in
    write_tnnex (valdir ^ "/" ^ pb) (basicex_to_tnnex exv);
    write_tnnex (poldir ^ "/" ^ pb) (basicex_to_tnnex exp);
    write_tnnex (argdir ^ "/" ^ pb) (basicex_to_tnnex exa);
    writel (resdir ^ "/" ^ pb) [string_of_bstatus bstatus];
    hide_flag := mem
  end
  
  

(* -------------------------------------------------------------------------
   Toy example (* todo: follow proven *)
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "tttBigSteps"; open tttBigSteps;
load "tacticToe"; open tacticToe;

val goal:goal = ([],``?x. x*x=4``);
val thmdata = mlThmData.create_thmdata ();
val tacdata = mlTacticData.create_tacdata ();
val searchobj = build_searchobj (thmdata,tacdata) (NONE,NONE) goal;

val (b,exl) = run_bigsteps searchobj goal;
val (a,b,c) = exl;

val (_,t) = add_time run_bigsteps goal;
val (winb,ex) = run_bigsteps goal;
*)

(* take care of the edge case when all tactic fails *)

end (* struct *)
