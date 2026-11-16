(* ========================================================================= *)
(* Simplification of terms similar to SIMP_CONV but regarding arbitrary      *)
(* preorders instead of just equality                                        *)
(* Created by Thomas Tuerk, March 2006                                       *)
(*                                                                           *)
(* The implementation is a functor over the traversal engine, instantiated   *)
(* as congLib (Traverse, simpLib) and congExtLib (TraverseExt, simpExtLib).  *)
(* ========================================================================= *)

(* The interface of congLib, over the engine's reducer and simpset types.
   See congLib.sig for the documentation. *)
signature congLibFn =
sig
  include Abbrev

  type reducer
  type simpset

  datatype congsetfrag = CSFRAG of
    {relations : Travrules.preorder list,
     rewrs  : thm list,
     congs  : thm list,
     dprocs : reducer list
     };
  type congset;

  val empty_congset : congset;
  val mk_congset : congsetfrag list -> congset
  val cs_addfrag : congset -> congsetfrag -> congset
  val merge_cs : congsetfrag list -> congsetfrag
  val csfrag_rewrites : thm list -> congsetfrag
  val add_csfrag_rewrites : congsetfrag -> thm list -> congsetfrag

  val CONGRUENCE_SIMP_CONV :
      term -> congset -> simpset -> thm list -> term -> thm
  val CONGRUENCE_SIMP_QCONV :
      term -> congset -> simpset -> thm list -> term -> thm
  val CONGRUENCE_EQ_SIMP_CONV : congset -> simpset -> thm list -> term -> thm
  val CONGRUENCE_SIMP_RULE : congset -> simpset -> thm list -> thm -> thm
  val CONGRUENCE_SIMP_TAC : congset -> simpset -> thm list -> tactic
  val ASM_CONGRUENCE_SIMP_TAC : congset -> simpset -> thm list -> tactic
  val FULL_CONGRUENCE_SIMP_TAC : congset -> simpset -> thm list -> tactic
end


(* The engine a congruence library runs on.  lift turns the library's own
   cong_reducer into an engine reducer; eq_reducer_wrapper makes a simpset
   reducer, which proves equations, prove the reflexive relation instead;
   traversal projects a simpset's reducers and travrules together with the
   traversal to run them with. *)
functor congLibFn
  (E : sig
         type reducer
         type simpset
         val lift : Traverse.reducer -> reducer
         val addctxt : Abbrev.thm list -> reducer -> reducer
         val eq_reducer_wrapper : reducer -> reducer
         val CONGPROC : ({Rinst:Abbrev.term,arg:Abbrev.term} -> Abbrev.thm) ->
                        Abbrev.thm -> Opening.congproc
         val traversal :
             simpset ->
             {rewriters : reducer list, dprocs : reducer list,
              travrules : Travrules.travrules} *
             ({rewriters : reducer list, dprocs : reducer list,
               limit : int option, travrules : Travrules.travrules,
               relation : Abbrev.term} -> Abbrev.thm list -> Abbrev.conv)
       end) : congLibFn =
struct
open HolKernel boolLib
     liteLib Trace Opening Travrules Cond_rewr;

type reducer = E.reducer
type simpset = E.simpset


(*
HOLFlags.set_bflag (Parse.show_assums, false);
HOLFlags.set_bflag (Parse.show_assums, true);
HOLFlags.set_bflag (Parse.show_types, true);
HOLFlags.set_bflag (Parse.show_types, false);
quietdec := false;
*)

fun extract_preorder_trans (Travrules.PREORDER(_,TRANS,_)) = TRANS;
fun extract_preorder_refl (Travrules.PREORDER(_,_,REFL)) = REFL;
fun extract_preorder_const (Travrules.PREORDER(t,_,_)) = t

(*---------------------------------------------------------------------------*)
(* Composable congruence set fragments                                       *)
(*---------------------------------------------------------------------------*)

(* AP_TERM_THM : !f x. f x x ==> !y. x = y ==> f x y.
   Derived forward via AP_TERM so we don't fire a load-time
   Tactical.prove. *)
val AP_TERM_THM =
  let
    val f = mk_var("f", Type.alpha --> Type.alpha --> Type.bool)
    val x = mk_var("x", Type.alpha)
    val y = mk_var("y", Type.alpha)
    val f_x_x = list_mk_comb(f, [x, x])
    val eqn = mk_eq(x, y)
    val h1 = ASSUME f_x_x
    val h2 = ASSUME eqn
    val fx_eq = AP_TERM (mk_comb(f, x)) h2      (* [x=y] |- f x x = f x y *)
    val fxy = EQ_MP fx_eq h1                    (* [f x x, x=y] |- f x y *)
  in
    fxy |> DISCH eqn |> GEN y |> DISCH f_x_x |> GEN x |> GEN f
  end


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
    map (E.CONGPROC gen_refl) congs
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
    (E.CONGPROC (fn {Rinst,arg} => REFL arg)) thm
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
          (List.foldr insert_one net flatThms)
        end

      fun addcontext (context,thms) =
        let
          val net = (raise context) handle CONVNET net => net
        in
          CONVNET (insertThms net thms)
        end
      fun apply {solver,conv,context,stack,relation} tm =
        let
            val net = ((raise context) handle CONVNET net => net)
            val thm = cong_rewrite net relation tm
        in
          thm
        end
  in E.lift (Traverse.REDUCER
       {name=SOME"cong_reducer", addcontext=addcontext, apply=apply,
        initial=CONVNET (Ho_Net.empty)})
  end;

datatype congsetfrag = CSFRAG of
   {rewrs  : thm list,
    relations : preorder list,
    dprocs : reducer list,
    congs  : thm list};



datatype congset = CS of
   {cong_reducer : reducer,
    limit : int option,
    relations : preorder list,
    dprocs : reducer list,
    travrules  : travrules list}

val empty_congset = CS {cong_reducer=cong_reducer,
                    relations=[equalityPreorder],
                    dprocs=[], limit = NONE,
                    travrules=[]};


 fun add_to_congset
    (CSFRAG {rewrs, relations=relationsFrag, dprocs=dprocsFrag, congs},
     CS {cong_reducer, relations, dprocs, travrules, limit})
  = let
      val cong_reducer = E.addctxt rewrs cong_reducer;

      val refl_rewrites = map mk_refl_rewrite relationsFrag;
      val cong_reducer = E.addctxt refl_rewrites cong_reducer;

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
    val (traversedata, traverse) = E.traversal ss
    val data = {rewriters= (#cong_reducer csdata)::
          (map E.eq_reducer_wrapper (#rewriters traversedata)),
          dprocs= #dprocs csdata @
                  map E.eq_reducer_wrapper (#dprocs traversedata),
          relation=relation, limit= #limit csdata,
          travrules=merge_travrules
            ([eq_congsTravrule,#travrules traversedata] @
             #travrules csdata)}
  in
    traverse data
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


val CONGRUENCE_EQ_SIMP_CONV = CONGRUENCE_SIMP_CONV boolSyntax.equality;


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
         STRIP_ALL_THEN
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
