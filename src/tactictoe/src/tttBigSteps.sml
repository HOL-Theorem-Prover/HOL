(* ========================================================================= *)
(* FILE          : tttBigSteps.sml                                           *)
(* DESCRIPTION   : Successions of non-backtrackable moves chosen after one   *)
(*                 MCTS call for each step                                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure tttBigSteps :> tttBigSteps =
struct

open HolKernel Abbrev boolLib aiLib psMCTS smlParallel tttToken 
  tttTrain tttSearch

val ERR = mk_HOL_ERR "tttBigSteps"

(* -------------------------------------------------------------------------
   Global example datasets
   ------------------------------------------------------------------------- *)

type ex = (term * real) list

val exval = ref []
val expol = ref []
val exarg = ref []

(* -------------------------------------------------------------------------
   Extracting examples
   ------------------------------------------------------------------------- *)

fun example_val goalrec =
  (nntm_of_stateval (#goal goalrec), #gsum goalrec / #gvis goalrec)

fun example_pol goal argl1 =
  let 
    val argl2 = map_assoc 
      (fn x => if #sstatus x = StacSaturated then 0.0 else #svis x) argl1
    val tot = sum_real (map snd argl2) 
    val _ = if tot <= 0.5 then raise ERR "example_stacex" "" else () 
    fun f b = b / tot 
    val argl3 = map_snd f argl2
    val argl4 = map_fst 
      (fn x => nntm_of_statepol (goal,dest_stac (#token x))) argl3 
  in
    argl4
  end

fun example_arg (goal,stac) argl1 =
  let 
    val argl2 = map_assoc 
      (fn x => if #sstatus x = StacSaturated then 0.0 else #svis x) argl1
    val tot = sum_real (map snd argl2) 
    val _ = if tot <= 0.5 then raise ERR "example_stacex" "" else () 
    fun f b = b / tot 
    val argl3 = map_snd f argl2
    val argl4 = map_fst 
      (fn x => nntm_of_statearg ((goal,stac), #token x)) argl3 
  in
    argl4
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
    val _ = exarg := example_arg (#goal goalrec, stac) (map snd argl1) @ !exarg
    val argl2 = filter (fn (_,x) => #sstatus x <> StacSaturated) argl1
    val _ = if null argl1 then raise ERR "best_arg" "empty" else ()
    val argl3 = dict_sort compare_rmax (map_assoc (#svis o snd) argl2)
    val bestan = fst (fst (hd argl3))
  in
    bestan
  end

fun best_stac tree = 
  let
    val node = dfind [] tree
    val goalrec = Vector.sub (#goalv node,0)
    val _ = exval := example_val goalrec :: !exval
    val argl1 = children_stacv (#stacv goalrec)
    val _ = if null argl1 then raise ERR "best_stac" "empty" else ()
    val _ = expol := example_pol (#goal goalrec) (map snd argl1) @ !expol
    val argl2 = filter (fn (_,x) => #sstatus x <> StacSaturated) argl1
    val argl3 = dict_sort compare_rmax (map_assoc (#svis o snd) argl2)
    val bestsn = fst (fst (hd argl3))
  in
    bestsn
  end

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)

(* have the system run in a bigstep mode *)
(* ex is reversed *)
val max_bigsteps = 50 
val nsim = 1600

fun stacrec_of tree (sn,anl) = 
  let
    val node = dfind [] tree
    val goalrec = Vector.sub (#goalv node,0)
    val argtree = Vector.sub (#stacv goalrec,sn)
  in
    dfind anl argtree
  end

fun goallist_of_node node = map #goal (vector_to_list (#goalv node))

(*
fun path_to_anl (sn,anl) root =
  let
    val goalrec = Vector.sub (#goalv root,0)
    val argtree = Vector.sub (#stacv goalrec,sn)
    fun f x =
      {token = #token x, atyl = #atyl x,
       svis = 0.0, ssum = 0.0, sstatus = StacFresh}
    fun loop x tree = 
      if null x
      then dadd x (dfind x argtree) tree
      else loop (tl x) (dadd x (f (dfind x argtree)) tree)
    val newargtree = loop anl argtree
    val newstacv = Vector.fromList [newargtree]
    val newgoalrec =
      {
      goal = #goal goalrec,
      gvis = 1.0, gsum = 0.0,
      gstatus = backstatus_stacv newstacv,
      stacv = newstacv,
      siblingd = dempty (list_compare goal_compare)
      }
    val newgoalv = Vector.fromList [newgoalrec]
    val newroot =       
      {
      nvis = 1.0, nsum = 0.0 (* backreward_allgoalv cgoalv *), 
      nstatus = backstatus_goalv newgoalv,
      goalv = newgoalv,
      parentd = dempty goal_compare
      }
  in
    dadd [] newroot (dempty id_compare)
  end
*)

fun loop_arg searchobj prevtree (sn,anl) =
  if #sstatus (stacrec_of prevtree (sn,anl)) = StacProved
    then (StacProved,NONE)
  else if #sstatus (stacrec_of prevtree (sn,anl)) = StacSaturated
    then (StacSaturated,NONE)
  else if null (#atyl (stacrec_of prevtree (sn,anl))) 
    then  
    (if dmem [(0,sn,anl)] prevtree 
     then (StacUndecided, SOME (goallist_of_node 
       (dfind [(0,sn,anl)] prevtree)))
     else (StacUndecided, NONE))
  else
    let 
      (* val starttree = path_to_anl (sn,anl) (dfind [] prevtree) *)
      val (_,tree) = search searchobj 
        (singleton_of_list (goallist_of_node (dfind [] prevtree)))
      (* val stacrec = stacrec_of tree (sn,anl)
      val _ = stats_stacrec stacrec *)
      val an = best_arg tree (sn,anl)
    in
      loop_arg searchobj tree (sn, an :: anl)    
    end

fun loop_stac searchobj g =
  let
    val (_,tree) = search searchobj g
    val node = dfind [] tree
    (* val _ = stats_node node *)
    val goalrec = Vector.sub (#goalv node, 0) 
    val sn = best_stac tree
    val argtree = Vector.sub (#stacv goalrec,sn)
  in      
    loop_arg searchobj tree (sn,[])
  end

fun string_of_gl gl = String.concatWith "," (map string_of_goal gl)

fun loop_node searchobj n gl =
  (
  print_endline ("Goals: " ^ string_of_gl gl);
  if null gl 
    then true
  else if n + length gl > max_bigsteps 
    then false
  else
    let val glol = smlRedirect.hidef (map (loop_stac searchobj)) gl in
      if all (fn x => fst x = StacProved) glol
        then true
      else if exists (fn x => fst x = StacSaturated) glol orelse
              exists (fn x => not (isSome (snd x))) glol
        then false
      else
        let val newgl = List.concat (map (valOf o snd) glol) in
          loop_node searchobj (n + length gl) newgl
        end
     end
  )

fun run_bigsteps searchobj g = 
  let 
    val _ = (exval := []; expol := []; exarg := [])
    val winb = loop_node searchobj 0 [g]
    val r = (winb,(!exval,!expol,!exarg))
    val _ = (exval := []; expol := []; exarg := [])
  in
    r
  end

(* -------------------------------------------------------------------------
   Toy example (* todo: follow proven *)
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "tttBigSteps"; open tttBigSteps;
load "tacticToe"; open tacticToe;

val goal:goal = ([],``1+1=2``);
val thmdata = mlThmData.create_thmdata ();
val tacdata = mlTacticData.create_tacdata ();
val searchobj = build_searchobj (thmdata,tacdata) (NONE,NONE) goal;

run_bigsteps searchobj ([],``1+1=2``);


val (_,t) = add_time run_bigsteps goal;
val (winb,ex) = run_bigsteps goal;
*)

end (* struct *)
