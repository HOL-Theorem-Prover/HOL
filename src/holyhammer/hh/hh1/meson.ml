open Follist;;
open Lib;;

let meson_depth = ref false;;   (* Use depth not inference bound.            *)
let meson_prefine = ref true;;  (* Use Plaisted's positive refinement.       *)
let meson_dcutin = ref 1;;      (* Min size for d-and-c optimization cut-in. *)
let meson_skew = ref 3;;        (* Skew proof bias (one side is <= n / skew) *)

(* ------------------------------------------------------------------------- *)
(* Prolog exception.                                                         *)
(* ------------------------------------------------------------------------- *)

exception Cut;;

let inferences = ref 0;;

type fol_goal =
  Subgoal of fol_lit * fol_goal list * (int * Fusion.thm) *
             int * (fol_term * int)list;;

  let qpartition p m =
    let rec qpartition l =
      if l == m then raise Unchanged else
      match l with
        [] -> raise Unchanged
      | (h::t) -> if p h then
                    try let yes,no = qpartition t in h::yes,no
                    with Unchanged -> [h],t
                  else
                    let yes,no = qpartition t in yes,h::no in
    function l -> try qpartition l
                  with Unchanged -> [],l;;

  (* ----------------------------------------------------------------------- *)
  (* Cacheing continuations. Very crude, but it works remarkably well.       *)
  (* ----------------------------------------------------------------------- *)

  let cacheconts f =
    let memory = ref [] in
    fun (gg,(insts,offset,size) as input) ->
      if exists (fun (_,(insts',_,size')) ->
                     insts = insts' & (size <= size' or !meson_depth))
          (!memory)
      then failwith "cachecont"
      else memory := input::(!memory); f input;;

  (* ----------------------------------------------------------------------- *)
  (* Check ancestor list for repetition.                                     *)
  (* ----------------------------------------------------------------------- *)

  let checkan insts (p,a) ancestors =
    let p' = -p in
    let t' = (p',a) in
    try let ours = assoc p' ancestors in
        if exists (fun u -> fol_atom_eq insts t' (snd(fst u))) ours
        then failwith "checkan"
        else ancestors
    with Failure "find" -> ancestors;;

  (* ----------------------------------------------------------------------- *)
  (* Insert new goal's negation in ancestor clause, given refinement.        *)
  (* ----------------------------------------------------------------------- *)

  let insertan insts (p,a) ancestors =
    let p' = -p in
    let t' = (p',a) in
    let ourancp,otheranc =
      try remove (fun (pr,_) -> pr = p') ancestors
      with Failure _ -> (p',[]),ancestors in
    let ouranc = snd ourancp in
    if exists (fun u -> fol_atom_eq insts t' (snd(fst u))) ouranc
    then failwith "insertan: loop"
    else (p',(([],t'),(0,Bool.tRUTH))::ouranc)::otheranc;;

  (* ----------------------------------------------------------------------- *)
  (* Tease apart local and global instantiations.                            *)
  (* At the moment we also force a full evaluation; should eliminate this.   *)
  (* ----------------------------------------------------------------------- *)

  let separate_insts offset oldinsts newinsts =
    let locins,globins =
      qpartition (fun (_,v) -> offset <= v) oldinsts newinsts in
    if globins = oldinsts then
      map (fun (t,x) -> fol_subst_partial newinsts t,x) locins,oldinsts
    else
      map (fun (t,x) -> fol_subst_partial newinsts t,x) locins,
      map (fun (t,x) -> fol_subst_partial newinsts t,x) globins;;

  (* ----------------------------------------------------------------------- *)
  (* Perform basic MESON expansion.                                          *)
  (* ----------------------------------------------------------------------- *)

  let meson_single_expand loffset rule ((g,ancestors),(insts,offset,size)) =
    let (hyps,conc),tag = rule in
    let allins = rev_itlist2 (fol_unify loffset) (snd g) (snd conc) insts in
    let locin,globin = separate_insts offset insts allins in
    let mk_ihyp h =
      let h' = fol_inst_bump offset locin h in
      h',checkan insts h' ancestors in
    let newhyps =  map mk_ihyp hyps in
    inferences := !inferences + 1;
    newhyps,(globin,offset+offinc,size-length hyps);;

  (* ----------------------------------------------------------------------- *)
  (* Perform first basic expansion which allows continuation call.           *)
  (* ----------------------------------------------------------------------- *)

  let meson_expand_cont loffset rules state cont =
    tryfind
     (fun r -> cont (snd r) (meson_single_expand loffset r state)) rules;;

  (* ----------------------------------------------------------------------- *)
  (* Try expansion and continuation call with ancestor or initial rule.      *)
  (* ----------------------------------------------------------------------- *)

  let meson_expand rules ((g,ancestors),((insts,offset,size) as tup)) cont =
    let pr = fst g in
    let newancestors = insertan insts g ancestors in
    let newstate = (g,newancestors),tup in
    try if !meson_prefine & pr > 0 then failwith "meson_expand" else
        let arules = assoc pr ancestors in
        meson_expand_cont 0 arules newstate cont
    with Cut -> failwith "meson_expand" | Failure _ ->
        try let crules =
              filter (fun ((h,_),_) -> length h <= size) (assoc pr rules) in
            meson_expand_cont offset crules newstate cont
        with Cut -> failwith "meson_expand"
           | Failure _ -> failwith "meson_expand";;

  (* ----------------------------------------------------------------------- *)
  (* Simple Prolog engine organizing search and backtracking.                *)
  (* ----------------------------------------------------------------------- *)

  let expand_goal rules =
    let rec expand_goal depth ((g,_),(insts,offset,size) as state) cont =
      if depth < 0 then failwith "expand_goal: too deep" else
      meson_expand rules state
        (fun apprule (_,(pinsts,_,_) as newstate) ->
            expand_goals (depth-1) newstate
              (cacheconts(fun (gs,(newinsts,newoffset,newsize)) ->
                 let locin,globin = separate_insts offset pinsts newinsts in
                 let g' = Subgoal(g,gs,apprule,offset,locin) in
                 if globin = insts & gs = [] then
                   try cont(g',(globin,newoffset,size))
                   with Failure _ -> raise Cut
                 else
                   try cont(g',(globin,newoffset,newsize))
                   with Cut -> failwith "expand_goal"
                      | Failure _ -> failwith "expand_goal")))

    and expand_goals depth (gl,(insts,offset,size as tup)) cont =
      match gl with
        [] -> cont ([],tup)

      | [g] -> expand_goal depth (g,tup) (fun (g',stup) -> cont([g'],stup))

      | gl -> if size >= !meson_dcutin then
                let lsize = size / (!meson_skew) in
                let rsize = size - lsize in
                let lgoals,rgoals = chop_list (length gl / 2) gl in
                try expand_goals depth (lgoals,(insts,offset,lsize))
                     (cacheconts(fun (lg',(i,off,n)) ->
                         expand_goals depth (rgoals,(i,off,n + rsize))
                           (cacheconts(fun (rg',ztup) -> cont (lg'@rg',ztup)))))
                with Failure _ ->
                    expand_goals depth (rgoals,(insts,offset,lsize))
                      (cacheconts(fun (rg',(i,off,n)) ->
                         expand_goals depth (lgoals,(i,off,n + rsize))
                           (cacheconts (fun (lg',((_,_,fsize) as ztup)) ->
                              if n + rsize <= lsize + fsize
                              then failwith "repetition of demigoal pair"
                              else cont (lg'@rg',ztup)))))
              else
                let g::gs = gl in
                expand_goal depth (g,tup)
                  (cacheconts(fun (g',stup) ->
                      expand_goals depth (gs,stup)
                        (cacheconts(fun (gs',ftup) -> cont(g'::gs',ftup))))) in

    fun g maxdep maxinf cont ->
      expand_goal maxdep (g,([],2 * offinc,maxinf)) cont;;

  (* ----------------------------------------------------------------------- *)
  (* With iterative deepening of inferences or depth.                        *)
  (* ----------------------------------------------------------------------- *)

  let solve_goal rules incdepth min max incsize =
    let rec solve n g =
      if n > max then failwith "solve_goal: Too deep" else
      try let gi =
            if incdepth then expand_goal rules g n 100000 (fun x -> x)
            else expand_goal rules g 100000 n (fun x -> x) in
          gi
      with Failure _ -> solve (n + incsize) g in
    fun g -> solve min (g,[]);;

    let mk_negated (p,a) = -p,a;;
    let rec mk_contraposes n th used unused sofar =
      match unused with
        [] -> sofar
      | h::t -> let nw = (map mk_negated (used @ t),h),(n,th) in
                mk_contraposes (n + 1) th (used@[h]) t (nw::sofar);;


    let fol_of_hol_clause th =
      let lconsts = Fusion.freesl (Fusion.hyp th) in
      let tm = Fusion.concl th in
      let hlits = Basics.disjuncts tm in
      let flits = map (fol_of_literal false [] lconsts) hlits in
      let basics = mk_contraposes 0 th [] flits [] in
      if forall (fun (p,_) -> p < 0) flits then
        ((map mk_negated flits,(1,[])),(-1,th))::basics
      else basics;;

  let fol_of_hol_clauses =
    let eqt (a1,(b1,c1)) (a2, (b2,c2)) =
     ((a1 = a2) & (b1 = b2) & (Fusion.equals_thm c1 c2)) in
    fun thms ->
      let rawrules = itlist (fun x -> union' eqt (fol_of_hol_clause x)) thms [] in
      let prs = setify (map (fun x -> fst (snd (fst x))) rawrules) in
      let prules =
        map (fun t -> t,filter (fun x -> t = fst (snd (fst x))) rawrules) prs in
      let srules = sort (fun (p,_) (q,_) -> abs(p) <= abs(q)) prules in
      srules;;

  let optimize_rules =
    let optimize_clause_order cls =
      sort (fun ((l1,_),_) ((l2,_),_) -> length l1 <= length l2) cls in
    map (fun (a,b) -> a,optimize_clause_order b);;

open Basics;;
open Bool;;
open Simp;;
open Fusion;;
open Theorems;;
open Hl_parser;;
open Equal;;
open Drule;;

  let clear_contrapos_cache,make_hol_contrapos =
    let dISJ_AC = aC dISJ_ACI
    and imp_CONV = rEWR_CONV(Sequent ([], parse_term "a \\/ b <=> ~b ==> a"))
    and push_CONV =
      gEN_REWRITE_CONV tOP_SWEEP_CONV
       [Sequent ([], parse_term "~(a \\/ b) <=> ~a /\\ ~b"); Sequent ([], parse_term "~(~a) <=> a")]
    and pull_CONV = gEN_REWRITE_CONV dEPTH_CONV
       [Sequent ([], parse_term "~a \\/ ~b <=> ~(a /\\ b)")]
    and imf_CONV = rEWR_CONV(Sequent ([], parse_term "~p <=> p ==> F")) in
    let memory = ref [] in
    let clear_contrapos_cache() = memory := [] in
    let make_hol_contrapos (n,th) =
      let tm = concl th in
      let key = (n,tm) in
      try assoc key (!memory) with Failure _ ->
      if n < 0 then
        cONV_RULE (tHENC pull_CONV imf_CONV) th
      else
        let djs = disjuncts tm in
        let acth =
          if n = 0 then th else
          let ldjs,rdjs = chop_list n djs in
          let ndjs = (hd rdjs)::(ldjs@(tl rdjs)) in
          eQ_MP (dISJ_AC(mk_eq(tm,list_mk_disj ndjs))) th in
        let fth =
          if length djs = 1 then acth
          else cONV_RULE (tHENC imp_CONV push_CONV) acth in
        (memory := (key,fth)::(!memory); fth) in
    clear_contrapos_cache,make_hol_contrapos;;

  let meson_to_hol =
    let hol_negate tm =
      try dest_neg tm with Failure _ -> mk_neg tm in
    let merge_inst (t,x) current =
      (fol_subst current t,x)::current in
    let finish_RULE =
      gEN_REWRITE_RULE iii
       [Sequent ([], parse_term "(~p ==> p) <=> p"); Sequent ([], parse_term "(p ==> ~p) <=> ~p")] in
    let rec meson_to_hol insts (Subgoal(g,gs,(n,th),offset,locin)) =
      let newins = itlist merge_inst locin insts in
      let g' = fol_inst newins g in
      let hol_g = hol_of_literal g' in
      let ths = map (meson_to_hol newins) gs in
      let hth =
        if th = tRUTH then aSSUME hol_g else
        let cth = make_hol_contrapos(n,th) in
        if ths = [] then cth else mATCH_MP cth (end_itlist cONJ ths) in
      let ith = pART_MATCH iii hth hol_g in
      finish_RULE (dISCH (hol_negate(concl ith)) ith) in
    meson_to_hol;;


  let sIMPLE_MESON_REFUTE min max inc ths =
    clear_contrapos_cache ();
    inferences := 0;
    let old_dcutin = !meson_dcutin in
    if !meson_depth then meson_dcutin := 100001 else ();
    let ths' = ths @ create_equality_axioms (map Fusion.concl ths) in
    let rules = optimize_rules(fol_of_hol_clauses ths') in
    let proof,(insts,_,_) =
      solve_goal rules (!meson_depth) min max inc (1,[]) in
    meson_dcutin := old_dcutin;
    meson_to_hol insts proof;;

  let pURE_MESON_TAC min max inc gl =
    reset_vars(); reset_consts();
    (www(fun x -> Tactics.aCCEPT_TAC (sIMPLE_MESON_REFUTE min max inc (map snd (fst x)))) gl);;

open Tactics;;
open Simp;;
open Canon;;
  let cONJUNCTS_THEN' ttac cth =
    ttac(Bool.cONJUNCT1 cth) ++++ ttac(Bool.cONJUNCT2 cth);;

let gEN_MESON_TAC min max step ths =
  rEFUTE_THEN aSSUME_TAC ++++
  (mAP_EVERY aSSUME_TAC ths) ++++
  rULE_ASSUM_TAC(Equal.cONV_RULE(Equal.tHENC nNF_CONV sKOLEM_CONV)) ++++
  rEPEAT (fIRST_X_ASSUM cHOOSE_TAC) ++++
  rULE_ASSUM_TAC(Equal.cONV_RULE(Equal.tHENC pRENEX_CONV cNF_CONV)) ++++
  rULE_ASSUM_TAC(repeat
   (fun th -> Bool.sPEC(Basics.genvar(Fusion.type_of(fst(Basics.dest_forall(Fusion.concl th))))) th)) ++++
  rEPEAT (fIRST_X_ASSUM (cONJUNCTS_THEN' aSSUME_TAC)) ++++
  pURE_MESON_TAC min max step
;;

let aSM_MESON_TAC = gEN_MESON_TAC 0 50 1;;
let mESON_TAC ths = pOP_ASSUM_LIST(kkk aLL_TAC) ++++ aSM_MESON_TAC ths;;
let mESON ths tm = Tactics.prove(tm,mESON_TAC ths);;
