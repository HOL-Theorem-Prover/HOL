structure congLib :> congLib =
struct

(*
quietdec := true;

map load
 ["liteLib",
  "computeLib", "simpLib", "Trace", "Traverse", "Opening",
  "Travrules", "relationTheory", "Cond_rewr"];
*)

open HolKernel boolLib
     liteLib computeLib simpLib Trace Traverse Opening
     Travrules Cond_rewr;


(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)

fun extract_preorder_trans (Travrules.PREORDER(_,TRANS,_)) = TRANS;
fun extract_preorder_refl (Travrules.PREORDER(_,_,REFL)) = REFL;
fun extract_preorder_const (Travrules.PREORDER(t,_,_)) = t

(*---------------------------------------------------------------------------*)
(* Composable congruence set fragments                                       *)
(*---------------------------------------------------------------------------*)

val AP_TERM_THM = prove (``!f x. (f x x) ==>
(!y. (x = y) ==> (f x y))``,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (fn x=> ASSUME_TAC (GSYM x)) THEN
  ASM_REWRITE_TAC[]
);


fun mk_preorder_refl preorders preorderTerm =
  let
    val preorder = find_relation preorderTerm preorders;
  in
    extract_preorder_refl preorder
  end;


fun mk_congprocs preorders congs =
  let
    val congs = flatten (map BODY_CONJUNCTS congs)
    fun gen_refl(x as {Rinst,arg}) = mk_preorder_refl preorders Rinst x
  in
    map (CONGPROC gen_refl) congs
  end

fun mk_refl_rewrite preorder =
  let
    val preorderTerm = extract_preorder_const preorder
    val hol_type = hd (#2 (dest_type (type_of preorderTerm)))
    val var = mk_var ("x", hol_type)
    val refl = extract_preorder_refl preorder;
    val reflThm = refl {Rinst=preorderTerm,arg=var}
  in
    EQT_INTRO reflThm
  end;



fun mk_eq_congproc preorder =
  let
    val preorderTerm = extract_preorder_const preorder
    val hol_type = hd (#2 (dest_type (type_of preorderTerm)))
    val var = mk_var ("x", hol_type)
    val refl = extract_preorder_refl preorder;
    val reflThm = refl {Rinst=preorderTerm,arg=var}
    val thm = MATCH_MP AP_TERM_THM reflThm
    val thm = SPEC_ALL thm
  in
    (*The only congruence occuring in an antecedent is =. Thus t == ``$=`` holds for all
      calls and we can use REFL *)
    (CONGPROC (fn {Rinst,arg} => REFL arg)) thm
  end;



val equalityPreorder = Travrules.EQ_preorder


fun is_match_binop binop term =
  let
    val operator = rator (rator (term));
  in
    same_const operator binop
  end handle _ => false;


local
  fun cong_rewrite_internal (rel, refl) term boundvars thm =
      if is_eq (concl thm) then let
          val congThm = refl term
          val congThm = CONV_RULE (RAND_CONV (REWR_CONV thm)) congThm
        in
          congThm
        end
      else let
          val thm_relation = rator(rator(concl thm))
          val _ = samerel thm_relation rel orelse
                  failwith ("not applicable")
          val thmLHS = rand (rator (concl thm))
          val match = match_terml [] boundvars thmLHS term
          val thm = INST_TY_TERM match thm
        in
          thm
        end
in
  fun cong_rewrite net preorder term =
    (let
      val matches = Ho_Net.lookup term net;
      val result = tryfind (fn (boundvars, thm) => cong_rewrite_internal preorder term boundvars thm) matches
    in
      result
    end) handle _ => NO_CONV term;
end




exception CONVNET of (term set * thm) Ho_Net.net;

val cong_reducer =
  let
      fun insertThms net thms =
        let
          val flatThms = flatten (map BODY_CONJUNCTS thms);
          fun insert_one (thm, net) =
            (let
              val concl = rand (rator (concl thm));
              val boundvars = free_varsl (hyp thm);
              val boundvars_set = FVL (hyp thm) empty_varset;
            in
              Ho_Net.enter (boundvars, concl, (boundvars_set, thm)) net
            end) handle _ => net
        in
          (foldr insert_one net flatThms)
        end

      fun addcontext (context,thms) =
        let
          val net = (raise context) handle CONVNET net => net
        in
          CONVNET (insertThms net thms)
        end
      fun apply {solver,context,stack,relation} tm =
        let
            val net = ((raise context) handle CONVNET net => net)
            val thm = cong_rewrite net relation tm
        in
          thm
        end
  in REDUCER {name=SOME"cong_reducer",
              addcontext=addcontext, apply=apply,
              initial=CONVNET (Ho_Net.empty_net)}
  end;


fun reducer_addRwts (REDUCER {name,addcontext,apply,initial}) rwts =
  REDUCER {name=name,addcontext=addcontext, apply=apply, initial=addcontext (initial,rwts)}


fun eq_reducer_wrapper (eq_reducer as REDUCER data)= let
  val name = #name data
  val initial = #initial data
  val addcontext = #addcontext data

  fun apply {solver,context,stack,relation as (_, refl)} tm = let
    val eqthm = #apply data
                       {solver=solver,context=context,stack=stack,
                        relation=relation}
                       tm
    val congThm = refl tm
    val congThm = CONV_RULE (RAND_CONV (REWR_CONV eqthm)) congThm
  in
    congThm
  end
in
  REDUCER {name=name,addcontext=addcontext, apply=apply, initial=initial}
end;


datatype congsetfrag = CSFRAG of
   {rewrs  : thm list,
    relations : preorder list,
    dprocs : Traverse.reducer list,
    congs  : thm list};



abstype congset = CS of
   {cong_reducer : Traverse.reducer,
    limit : int option,
    relations : preorder list,
    dprocs : Traverse.reducer list,
    travrules  : travrules list}

with

val empty_congset = CS {cong_reducer=cong_reducer,
                    relations=[equalityPreorder],
                    dprocs=[], limit = NONE,
                    travrules=[]};


 fun add_to_congset
    (CSFRAG {rewrs, relations=relationsFrag, dprocs=dprocsFrag, congs},
     CS {cong_reducer, relations, dprocs, travrules, limit})
  = let
      val cong_reducer = reducer_addRwts cong_reducer rewrs;

      val refl_rewrites = map mk_refl_rewrite relationsFrag;
      val cong_reducer = reducer_addRwts cong_reducer refl_rewrites;

      val newRelations = relations@relationsFrag;
      val newCongs = mk_congprocs newRelations congs;
      val congsTravrule = TRAVRULES
        {relations=newRelations,
        congprocs=newCongs,
        weakenprocs=[]};
    in
      CS {cong_reducer=cong_reducer,
          relations=relations@relationsFrag,
          dprocs=dprocs@dprocsFrag,
          travrules=travrules@[congsTravrule],
          limit = limit}
    end;

 val mk_congset = foldl add_to_congset empty_congset;
 fun cs_addfrag cs csdata = add_to_congset (csdata,cs);

fun dest_congsetfrag (CSFRAG (data)) = data;

fun merge_cs (s:congsetfrag list) =
    CSFRAG {rewrs=flatten (map (#rewrs o dest_congsetfrag) s),
            relations=flatten (map (#relations o dest_congsetfrag) s),
            dprocs=flatten (map (#dprocs o dest_congsetfrag) s),
            congs=flatten (map (#congs o dest_congsetfrag) s)};

fun csfrag_rewrites rewrs =
   CSFRAG
   {rewrs=rewrs,
    relations = [],
    dprocs = [],
    congs  = []};


fun add_csfrag_rewrites s rewrs =
    merge_cs [s, csfrag_rewrites rewrs];


fun CONGRUENCE_SIMP_QCONV relation (cs as (CS csdata)) ss =
  let
    (*build a connection between the preorders and =*)
    val preorders = (#relations csdata);
    val preorders = filter (fn p => not (same_const (extract_preorder_const p)
                                                    boolSyntax.equality))
                           preorders;
    val preorder_eq_congs = map mk_eq_congproc preorders
    val eq_congsTravrule = TRAVRULES
      {relations=(#relations csdata),
      congprocs=preorder_eq_congs,
      weakenprocs=[]};
    val traversedata = traversedata_for_ss ss;
    val data = {rewriters= (#cong_reducer csdata)::
          (map eq_reducer_wrapper (#rewriters traversedata)),
          dprocs= (#dprocs csdata)@(map eq_reducer_wrapper (#dprocs traversedata)),
          relation= relation, limit = #limit csdata,
          travrules= merge_travrules ([eq_congsTravrule,#travrules traversedata]@(#travrules csdata))}
  in
    TRAVERSE data
  end;


fun CONGRUENCE_SIMP_CONV relation (cs as (CS csdata)) ss =
  let
    val qconv = CONGRUENCE_SIMP_QCONV relation cs ss
    val preorder = find_relation relation (#relations csdata);
    val refl = extract_preorder_refl preorder
    fun conv thms tm = qconv thms tm handle _ => refl {Rinst=relation,arg=tm}
  in
    conv
  end;

end (*Datatype congset*)


val CONGRUENCE_EQ_SIMP_CONV = CONGRUENCE_SIMP_CONV ``$=``;


fun CONGRUENCE_SIMP_RULE cs ss =
  (fn thms =>
    CONV_RULE (CONGRUENCE_EQ_SIMP_CONV cs ss thms));

fun CONGRUENCE_SIMP_TAC cs ss =
  (fn thms =>
    CONV_TAC (CONGRUENCE_EQ_SIMP_CONV cs ss thms));


fun ASM_CONGRUENCE_SIMP_TAC cs ss l = let
  fun base thl (asms, gl) = let
    val working = markerLib.LLABEL_RESOLVE thl asms
  in
    CONGRUENCE_SIMP_TAC cs ss working (asms, gl)
  end
in
  markerLib.ABBRS_THEN base l
end

fun FULL_CONGRUENCE_SIMP_TAC cs ss l =
       let fun drop n (asms,g) =
         let val l = length asms
             fun f asms =
           MAP_EVERY ASSUME_TAC
                                 (rev (fst (split_after (l-n) asms)))
         in
                 if (n > l) then STRUCT_ERR "congLib" ("drop", "Bad cut off number")
           else POP_ASSUM_LIST f (asms,g)
         end

           (* differs only in that it doesn't call DISCARD_TAC *)
           val STRIP_ASSUME_TAC' =
         REPEAT_TCL STRIP_THM_THEN
                    (fn th => FIRST [CONTR_TAC th, ACCEPT_TAC th,
                                           ASSUME_TAC th])
     fun simp_asm (t,l') = CONGRUENCE_SIMP_RULE cs ss (l'@l) t::l'
     fun f asms =
         MAP_EVERY STRIP_ASSUME_TAC' (foldl simp_asm [] asms)
         THEN drop (length asms)
       in
         markerLib.ABBRS_THEN
          (fn l => ASSUM_LIST f THEN ASM_CONGRUENCE_SIMP_TAC cs ss l) l
       end

end
