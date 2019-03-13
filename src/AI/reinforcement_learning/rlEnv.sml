(* ========================================================================= *)
(* FILE          : rlEnv.sml                                                 *)
(* DESCRIPTION   : Environnement for reinforcement learning                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlEnv :> rlEnv =
struct

open HolKernel Abbrev boolLib aiLib rlLib psMCTS mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "rlEnv"

type ('a,''b,'c) gamespec =
  {
  movel : ''b list,
  string_of_move : ''b -> string,
  filter_sit : 'a psMCTS.sit -> ((''b * real) list -> (''b * real) list),
  status_of : ('a psMCTS.sit -> psMCTS.status),
  apply_move : (''b -> 'a psMCTS.sit -> 'a psMCTS.sit),
  operl : (term * int) list,
  nntm_of_sit: 'a psMCTS.sit -> term
  }

(* -------------------------------------------------------------------------
   Log
   ------------------------------------------------------------------------- *)

val logfile_glob = ref "rlEnv"
val eval_dir = HOLDIR ^ "/src/AI/reinforcement_learning/eval"
fun log_eval file s =
  let val path = eval_dir ^ "/" ^ file in
    mkDir_err eval_dir;
    append_endline path s
  end
fun summary s = (log_eval (!logfile_glob) s; print_endline s)

(* -------------------------------------------------------------------------
   Hard-coded parameters
   ------------------------------------------------------------------------- *)

val ngen_glob = ref 20
val ntarget_compete = ref 400
val ntarget_explore = ref 400

val exwindow_glob = ref 40000
val dim_glob = ref 4
val batchsize_glob = ref 64

val nsim_glob = ref 1600
val decay_glob = ref 0.99
val ncore_glob = ref 8

fun summary_param () =
  let
    val file  = "  file: " ^ (!logfile_glob)
    val ncore = "ncores: " ^ its (!ncore_glob)
    val gen1  = "gen max: " ^ its (!ngen_glob)
    val gen2  = "target_compete: " ^ its (!ntarget_compete)
    val gen3  = "target_explore: " ^ its (!ntarget_explore)
    val nn1   = "example_window: " ^ its (!exwindow_glob)
    val nn2   = "nn dim: " ^ its (!dim_glob)
    val nn3   = "nn batchsize: " ^ its (!batchsize_glob)
    val mcts2 = "mcts simulation: " ^ its (!nsim_glob)
    val mcts3 = "mcts decay: " ^ rts (!decay_glob) 
  in
    summary "Global parameters";
    summary (String.concatWith "\n  " 
     ([file,ncore] @ [gen1,gen2,gen3] @ [nn1,nn2,nn3] @ [mcts2,mcts3])
     ^ "\n")
  end

(* -------------------------------------------------------------------------
   Evaluation and policy
   ------------------------------------------------------------------------- *)

fun mk_fep_dhtnn startb gamespec dhtnn sit =
  let
    val movel = #movel gamespec
    val filter_sit = (#filter_sit gamespec) sit
    val {opdict,headeval,headpoli,dimin,dimout} = dhtnn
    val etnn = {opdict=opdict,headnn=headeval,dimin=dimin,dimout=1}
    val ptnn = {opdict=opdict,headnn=headpoli,dimin=dimin,dimout=dimout}
    val nntm = (#nntm_of_sit gamespec) sit
  in
    if startb 
    then (0.05, filter_sit (map (fn x => (x,1.0)) movel))
    else (only_hd (infer_tnn etnn nntm),
      filter_sit (combine (movel, infer_tnn ptnn nntm)))
  end

(* -------------------------------------------------------------------------
   Examples
   ------------------------------------------------------------------------- *)

val emptyallex = ([],[])

fun complete_pol movel mrl =
  let fun f move = assoc move mrl handle HOL_ERR _ => 0.0 in
    map f movel
  end

fun update_allex movel (nntm,(e,p)) (eex,pex) =
  ((nntm,[e]) :: eex, (nntm, complete_pol movel p) :: pex)

fun update_allex_from_tree gamespec tree allex =
  let
    val root = dfind [0] tree
    val sit  = #sit root
    val nntm = (#nntm_of_sit gamespec) sit
    val movel = #movel gamespec
  in
    case evalpoli_example tree of
      NONE    => allex
    | SOME ep => update_allex movel (nntm,ep) allex
  end

fun discard_oldex (a,b) n = (first_n n a, first_n n b)

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)

fun n_bigsteps_loop (n,nmax) gamespec mctsparam (allex,allroot) tree =
  if n >= nmax then (allex,allroot) else
  let
    val nntm_of_sit = #nntm_of_sit gamespec
    val sit = #sit (dfind [0] tree)
    val newtree = mcts mctsparam tree
    val root = dfind [0] newtree
    val filter_sit = (#filter_sit gamespec) sit
    val movel = #movel gamespec
  in
   if null (filter_sit (map_assoc (fn x => 0.0) movel))
   then (allex, root :: allroot)
   else
     let val (dis,cido) = select_bigstep newtree [0] in
     case cido of
       NONE => (allex, root :: allroot)
     | SOME cid =>
        let
          (* val _ = print_distrib (#string_of_move gamespec) dis *)
          val cuttree = cut_tree newtree cid
          val newallex = update_allex_from_tree gamespec newtree allex
        in
          n_bigsteps_loop (n+1,nmax) gamespec mctsparam
          (newallex, root :: allroot) cuttree
        end
    end
  end

(*
print_endline "Max depth\n"; 

print_endline "No move available\n";
print_endline ("Target " ^ its ntarg);
print_endline ("  expected proof length: " ^ its nvary);
print_endline "MCTS: no move available\n"; 
*)

fun n_bigsteps gamespec mctsparam target =
  let 
    val tree = starttree_of mctsparam target 
    val nvary = rlGameArithGround.total_cost_target target
    val nvary' = 2 * nvary + 5
  in
    n_bigsteps_loop (0,nvary') gamespec mctsparam (emptyallex,[]) tree
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun random_dhtnn_gamespec gamespec =
  let
    val dimin = !dim_glob
    val dimout = length (#movel gamespec)
    val operl = #operl gamespec
  in
    random_dhtnn (dimin,dimout) operl
  end

fun train_dhtnn gamespec (evalex,poliex) =
  let
    val l1 = (dlist (dregroup Term.compare evalex))
    val r1 = average_real (map (Real.fromInt o length o snd) l1)
    val _ = summary ("Average duplicates: " ^ rts r1) 
    val _ = summary ("Eval examples: " ^ trainset_info evalex)
    val _ = summary ("Poli examples: " ^ trainset_info poliex)
    val schedule = [(100,0.1 / Real.fromInt (!batchsize_glob))]
    val bsize = if length evalex < (!batchsize_glob) then 1 
                else !batchsize_glob
    val dhtnn = random_dhtnn_gamespec gamespec
    val (etrain,ptrain) = (prepare_trainset evalex, prepare_trainset poliex)
  in
    train_dhtnn_schedule (!ncore_glob) dhtnn bsize (etrain,ptrain) schedule
  end

fun train_f gamespec allex =
  let val (dhtnn,t) = add_time (train_dhtnn gamespec) allex in
    summary ("Training time : " ^ rts t); dhtnn
  end

(* -------------------------------------------------------------------------
   Results
   ------------------------------------------------------------------------- *)

fun summary_wins gamespec allrootl =
  let
    val r0 = Real.fromInt (length allrootl)
    val endrootl = map hd allrootl
    val startrootl = map last allrootl
    fun value x = #sum x / #vis x
    val w5 = average_real (map value startrootl)
    val status_of = #status_of gamespec
    val w1 = length (filter (fn x => status_of (#sit x) = Win) endrootl)
    val w2 = length (filter (fn x => #status x = Win) endrootl)
    val w3 = length (filter (fn x => #status x = Win) (List.concat allrootl))
    val w4 = length (filter (fn x => #status x = Win) startrootl)
    val r1 = Real.fromInt (length (List.concat allrootl)) / r0
    val r2 = Real.fromInt w3 / r0
  in
    summary ("  Win start: " ^ its w4);
    summary ("  Value start (average): " ^ rts w5);
    summary ("  Win end: " ^ String.concatWith " " (map its [w1,w2]));
    summary ("  Big steps (average): " ^ rts r1);
    summary ("  Win nodes (average): " ^ rts r2)
  end

(* -------------------------------------------------------------------------
   Adaptive difficulty
   ------------------------------------------------------------------------- *)

val level_glob = ref 1

fun eval_targetl gamespec dhtnn targetl =
  let
    val {opdict,headeval,headpoli,dimin,dimout} = dhtnn
    val etnn = {opdict=opdict,headnn=headeval,dimin=dimin,dimout=1}
    fun f sit = only_hd (infer_tnn etnn ((#nntm_of_sit gamespec) sit))
    val l = map_assoc f targetl    
    val r = rts (average_real (map snd l))
    val l2 = map (rlGameArithGround.total_cost_target) targetl
    val r2 = rts (average_real (map Real.fromInt l2))
  in
    summary ("  Average value (full dataset): " ^ r);
    summary ("  Average expected proof length (full dataset): " ^ r2);
    l
  end

fun interval (step:real) (a,b) =
  if a + (step / 2.0) > b then [b] else a :: interval step (a + step,b)

fun choose_uniform gamespec dhtnn (targetl,ntarget) =
  let
    val l = eval_targetl gamespec dhtnn targetl
    fun f r = map fst (filter (fn (_,x) => x >= r andalso x < r + 0.1) l)
    val ll0 = map f (interval 0.1 (0.0,0.9))
    val _ =
      summary ("  Repartition (self-assessed): " ^ String.concatWith " "
               (map (its o length) ll0))
    fun g x = part_n (ntarget div 10) (shuffle x)
    val ll1 = map g ll0
    val chosenl = List.concat (map fst ll1)
    val otherl = List.concat (map snd ll1)
  in
    chosenl @ first_n (ntarget - (length chosenl)) (shuffle otherl)
  end

(* -------------------------------------------------------------------------
   Competition: comparing n dhtnn
   ------------------------------------------------------------------------- *)

fun mcts_ext fileout dhtnn gamespec target =
  let
    val status_of = #status_of gamespec
    val mctsparam =
      (!nsim_glob, !decay_glob, false,
       #status_of gamespec, #apply_move gamespec, 
       mk_fep_dhtnn false gamespec dhtnn)
    val ((_,allroot),t) = add_time (n_bigsteps gamespec mctsparam) target
    val endroot = hd allroot
    val winb = status_of (#sit endroot) = Win
  in
    if winb then writel fileout ["Win"] else writel fileout ["Lose"]
  end


val gencode_dir = HOLDIR ^ "/src/AI/reinforcement_learning/gencode"
val savestate_file = gencode_dir ^ "/savestate"
val dhtnn_file = gencode_dir ^ "/dhtnn"
val operl_file = gencode_dir ^ "/operl"

fun create_savestate () =
  let
    val sl =
    [
     "open HolKernel rlEnv aiLib",
     "val gamespec = rlGameArithGround.gamespec;",
     "val dhtnn_file = " ^ quote dhtnn_file ^ ";",
     "val operl_file = " ^ quote operl_file ^ ";",
     "val dhtnn = mlTreeNeuralNetwork.read_dhtnn_sl" ^  
     " operl_file (readl dhtnn_file);",
     "val targetl = rlGameArithGround.mk_targetl 1;", (* slow *)
     "val _ = nsim_glob := " ^ its (!nsim_glob) ^ ";",
     "val _ = decay_glob := " ^ rts (!decay_glob) ^ ";",
     "PolyML.SaveState.saveState " ^ quote savestate_file ^ ";"
    ]  
    val file = gencode_dir ^ "/savestate_script.sml"
  in
    writel file sl;
    smlOpen.run_buildheap false file
  end

fun mcts_gencode n =
  let
    val local_dir = gencode_dir ^ "/" ^ its n
    val _ = mkDir_err local_dir
    val file_in = local_dir ^ "/in_script" ^ its n ^ ".sml"
    val file_out = local_dir ^ "/out" ^ its n
    val sl =
    [
     "PolyML.SaveState.loadState " ^ quote savestate_file ^ ";",
     "val file_out = " ^ quote file_out ^ ";",
     "val targetn = " ^ its n ^ ";",
     "val target = List.nth (targetl,targetn);", 
     "val _ = rlEnv.mcts_ext file_out dhtnn gamespec target;"
    ]  
  in
    remove_file file_out;
    writel file_in sl;
    smlOpen.run_buildheap false file_in
  end

fun parmap_ext dhtnn ntot =
  let
    val _ = mkDir_err gencode_dir
    val targetl = first_n ntot (rlGameArithGround.mk_targetl 1)
    val _ = writel dhtnn_file [mlTreeNeuralNetwork.string_of_dhtnn dhtnn]
    val operl = 
      mk_sameorder_set Term.compare (map fst (dkeys (#opdict dhtnn)))
    val _ = mlTacticData.export_terml operl_file operl  
  in
    ignore (parmap 2 mcts_gencode (List.tabulate (ntot,I)))
  end

(*
load "rlEnv"; open rlEnv aiLib;

val dhtnn = random_dhtnn_gamespec rlGameArithGround.gamespec;
val ntot = 100;
val targetl = first_n ntot (rlGameArithGround.mk_targetl 1);
val gamespec = rlGameArithGround.gamespec;
val gencode_dir = HOLDIR ^ "/src/AI/reinforcement_learning/gencode";

val _ = mkDir_err gencode_dir;
val _ = create_savestate ();
fun file_out1 n = gencode_dir ^ "/" ^ its n ^ "/out" ^ its n;
val (_,t1) = add_time (parmap_ext dhtnn) ntot;
val l1 = map (readl o file_out1) (List.tabulate (ntot,I));

val _ = mkDir_err gencode_dir;
fun file_out2 n = gencode_dir ^ "/int" ^ its n;
fun g n = mcts_ext (file_out2 n) dhtnn gamespec (List.nth (targetl,n));
val (_,t2) = add_time (parapp 2 g) (List.tabulate (ntot,I));
val l2 = map (readl o file_out2) (List.tabulate (ntot,I));
test ();

*)


fun compete_one dhtnn gamespec targetl =
  let
    val status_of = #status_of gamespec
    val mctsparam =
      (!nsim_glob, !decay_glob, false,
       #status_of gamespec, #apply_move gamespec, 
       mk_fep_dhtnn false gamespec dhtnn)
    val (result,t) = add_time (parmap (!ncore_glob) 
      (n_bigsteps gamespec mctsparam)) targetl
    val (_,allrootl) = split result
    val _ = summary ("Competition time : " ^ rts t)
    val endrootl = map hd allrootl
  in
    length (filter (fn x => status_of (#sit x) = Win) endrootl)
  end

fun summary_compete (w_old,w_new) =
  summary 
     ((if w_new > w_old then "Passed" else "Failed") ^ ": " ^ 
      its w_old ^ " " ^ its w_new);

fun compete dhtnn_old dhtnn_new gamespec targetl =
  let
    val targetl' = first_n (!ntarget_compete) (shuffle targetl)
    val w_old = compete_one dhtnn_old gamespec targetl'
    val w_new = compete_one dhtnn_new gamespec targetl'
    val levelup = int_div (Int.max (w_new,w_old)) (length targetl') > 0.75
  in
    summary_compete (w_old,w_new);
    if levelup then incr level_glob else ();
    if w_new > w_old then dhtnn_new else dhtnn_old
  end


(* -------------------------------------------------------------------------
   Exploration
   ------------------------------------------------------------------------- *)

fun explore_f startb gamespec allex dhtnn targetl =
  let
    val targetl' = choose_uniform gamespec dhtnn (targetl,!ntarget_explore)
    val mctsparam =
      (!nsim_glob, !decay_glob, true,
       #status_of gamespec, #apply_move gamespec, 
       mk_fep_dhtnn startb gamespec dhtnn)
    val (result,t) = add_time (parmap (!ncore_glob) 
      (n_bigsteps gamespec mctsparam)) targetl'
    val (exl,allrootl) = split result
    val _ = summary ("Exploration time : " ^ rts t)
    val _ = summary_wins gamespec allrootl
    fun concat_ex ((exE,exP),(allexE,allexP)) = (exE @  allexE, exP @ allexP)
    val exl1 = foldl concat_ex allex exl
    fun cmp (a,b) = Term.compare (fst a,fst b)
    (* Optional: seems to provide a little more space for more examples *)
    val exl2 = (mk_sameorder_set cmp (fst exl1), 
                mk_sameorder_set cmp (snd exl1))
  in
    discard_oldex exl2 (!exwindow_glob)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun update_targetl () =  
  let
    val _ = summary ("Level: " ^ its (!level_glob))
    val (targetl,t) = 
      add_time rlGameArithGround.mk_targetl (!level_glob);
    val _ = summary ("Creating " ^ its (length targetl) ^ " new targets" ^ 
            " in " ^ rts t ^ " seconds")
  in
    shuffle targetl
  end

fun rl_start gamespec =
  let
    val _ = summary "Generation 0"
    val dhtnn_random = random_dhtnn_gamespec gamespec
    val targetl = update_targetl ()
    val allex = explore_f true gamespec emptyallex dhtnn_random targetl
    val dhtnn = train_f gamespec allex
  in
    (allex , dhtnn, targetl)
  end

fun test ncorel level bstart ntarget =
  let
    val gamespec = rlGameArithGround.gamespec
    val dhtnn = random_dhtnn_gamespec gamespec
    val _ = level_glob := level
    val targetl = update_targetl ()
    val _ = ntarget_explore := ntarget
    fun f n = 
      (ncore_glob := n;
       explore_f bstart gamespec emptyallex dhtnn targetl)
  in
    map (fn x => snd (add_time f x)) ncorel
  end

fun rl_one n gamespec (allex,dhtnn,targetl) =
  let
    val _ = summary ("\nGeneration " ^ its n)
    val dhtnn_new = train_f gamespec allex
    val dhtnn_best = compete dhtnn dhtnn_new gamespec targetl
    val targetl_new = update_targetl ()
    val newallex = explore_f false gamespec allex dhtnn_best targetl_new
  in
    (newallex, dhtnn_best, targetl_new)
  end

fun rl_loop (n,nmax) gamespec rldata =
  if n >= nmax then rldata else
    let val rldata_new = rl_one n gamespec rldata in
      rl_loop (n+1, nmax) gamespec rldata_new
    end

fun start_rl_loop gamespec =
  let
    val _ = summary_param ()
    val (allex,dhtnn,targetl) = rl_start gamespec
  in
    rl_loop (1,!ngen_glob) gamespec (allex,dhtnn,targetl)
  end

end (* struct *)

(*
app load ["rlGameArithGround","rlEnv"];
open aiLib psMCTS rlGameArithGround rlEnv;

logfile_glob := "march13";
ncore_glob := 8;
ngen_glob := 100;
ntarget_compete := 400;
ntarget_explore := 400;
exwindow_glob := 40000;
dim_glob := 8;
batchsize_glob := 128;
nsim_glob := 1600;
decay_glob := 0.99;
level_glob := 1;

val allex = start_rl_loop gamespec;




load "rlEnv"; open rlEnv;
logfile_glob := "test_mcts_1";
nsim_glob := 1600;
dim_glob := 8;
val ncorel = [1,2,4,8];
val level = 5;
val bstart = false;
val ntarget = 100;
val rl = test ncorel level bstart ntarget;

(* todo: do a similar test for training with saved data *)


*)


