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
fun extract_preorder_const (Travrules.PREORDER((name, thy),_,_)) =  
  prim_mk_const {Name=name,Thy=thy};
fun extract_preorder_const_string (Travrules.PREORDER((name, thy),_,_)) =  
  (name, thy);

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
    val gen_refl = mk_preorder_refl preorders;
  in
    map (fn cong => ((CONGPROC gen_refl) cong)) congs
  end


fun mk_eq_congproc preorder =
  let
    val preorderTerm = extract_preorder_const preorder
    val hol_type = hd (#2 (dest_type (type_of preorderTerm)))
    val var = mk_var ("x", hol_type)
    val refl = extract_preorder_refl preorder;
    val reflThm = refl var
    val thm = MATCH_MP AP_TERM_THM reflThm
    val thm = SPEC_ALL thm
  in
    (*The only congruence occuring in an antecedent is =. Thus t == ``$=`` holds for all
      calls and we can use REFL *)
    (CONGPROC (fn t => REFL)) thm 
  end;



val equalityPreorder = PREORDER(("=","min"),TRANS,REFL);


fun is_match_binop binop term = 
  let
    val operator = rator (rator (term));
  in
    same_const operator binop
  end handle _ => false;




local
  fun cong_rewrite_internal preorder term thm =
    (if (is_eq (concl thm)) then
      (let
        val refl = extract_preorder_refl preorder;
        val congThm = refl term;
        val congThm = CONV_RULE (RAND_CONV (REWR_CONV thm)) congThm
      in
        congThm
      end)
    else 
      (let
        val thm_relation = rator(rator(concl thm));
        val _ = if (name_of_const (thm_relation) = extract_preorder_const_string preorder) then T else failwith ("not applicable");
        val thmLHS = rand (rator (concl thm));
        val match = match_term thmLHS term;
        val thm = INST_TY_TERM match thm
      in
        thm
      end)
    )
in 
  fun cong_rewrite net preorder term =
    (let
      val matches = Net.match term net;    
      val result = tryfind (cong_rewrite_internal preorder term) matches 
    in
      result
    end) handle _ => NO_CONV term;
end




exception CONVNET of thm Net.net;

fun congr_reducer initialRwts =
  let 
      fun insertThms net thms =
        let
          fun insert_one (thm, net) =
            (Net.insert (rand (rator (concl thm)), thm) net) handle _ => net
        in
          (foldr insert_one net thms)
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
  in REDUCER {addcontext=addcontext, apply=apply,
              initial=CONVNET (insertThms Net.empty initialRwts)}
  end;



fun eq_reducer_wrapper (eq_reducer as REDUCER (data))=
  let 
      val initial = (#initial data);
      val addcontext = ((#addcontext data));

      fun apply {solver,context,stack,relation} tm =
        let 
            val eqthm = (#apply data) {solver=solver,context=context,stack=stack,relation=relation} tm
            val refl = extract_preorder_refl relation;
            val congThm = refl tm;
            val congThm = CONV_RULE (RAND_CONV (REWR_CONV eqthm)) congThm
        in 
          congThm
        end
  in REDUCER {addcontext=addcontext, apply=apply,
              initial=initial}
  end;


datatype congsetfrag = CSFRAG of
   {rewrs  : thm list,
    relations : preorder list,
    dprocs : Traverse.reducer list,
    congs  : thm list};



abstype congset = CS of
   {rewriters : Traverse.reducer list,
    relations : preorder list,
    dprocs : Traverse.reducer list,
    travrules  : travrules list}

with

val empty_congset = CS {rewriters=[],
                    relations=[equalityPreorder],
                    dprocs=[],
                    travrules=[]};


 fun add_to_congset
    (CSFRAG {rewrs, relations=relationsFrag, dprocs=dprocsFrag, congs},
     CS {rewriters, relations, dprocs, travrules})
  = let 
      val rewrites = flatten (map BODY_CONJUNCTS rewrs)
      val rewrsRewriter = congr_reducer rewrites;
      val newRelations = relations@relationsFrag;
      val newCongs = mk_congprocs newRelations congs;
      val congsTravrule = TRAVRULES
        {relations=newRelations,
        congprocs=newCongs,
        weakenprocs=[]};
    in
      CS {rewriters=rewriters@[rewrsRewriter],
          relations=relations@relationsFrag,
          dprocs=dprocs@dprocsFrag,
          travrules=travrules@[congsTravrule]}
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
    val preorders = filter (fn p => not (extract_preorder_const_string p = ("=", "min"))) preorders;
    val preorder_eq_congs = map mk_eq_congproc preorders
    val eq_congsTravrule = TRAVRULES
      {relations=(#relations csdata),
      congprocs=preorder_eq_congs,
      weakenprocs=[]};
    val traversedata = traversedata_for_ss ss;
    val data = {rewriters= (#rewriters csdata)@
          (map eq_reducer_wrapper (#rewriters traversedata)),
          dprocs= (#dprocs csdata)@(map eq_reducer_wrapper (#dprocs traversedata)),
          relation= relation,
          travrules= merge_travrules ([eq_congsTravrule,#travrules traversedata]@(#travrules csdata))}
  in
    TRAVERSE data
  end;


fun CONGRUENCE_SIMP_CONV relation (cs as (CS csdata)) ss =
  let
    val qconv = CONGRUENCE_SIMP_QCONV relation cs ss
    val preorder = find_relation relation (#relations csdata);  
    val refl = extract_preorder_refl preorder
    fun conv thms tm =
      ((qconv thms tm) handle _ => refl tm)
  in
    conv
  end;

end (*Datatype congset*)

end