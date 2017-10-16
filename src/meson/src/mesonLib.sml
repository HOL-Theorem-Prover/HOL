(* ========================================================================= *)
(* Version of the MESON procedure a la PTTP. Various search options.         *)
(* ========================================================================= *)

structure mesonLib :> mesonLib =
struct

open HolKernel boolLib liteLib Ho_Rewrite Canon_Port tautLib;

infix THEN THENC ORELSE ORELSE_TCL;

(* Fix the grammar used by this file *)
val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars boolTheory.bool_grammars

(*---------------------------------------------------------------------------*
 * Miscellaneous bits.                                                       *
 *---------------------------------------------------------------------------*)

exception NOT_FOUND;
exception Cut;

fun assoc1 item =
   let fun assc ((key,ob)::rst) = if (item=key) then SOME ob else assc rst
         | assc [] = NONE
    in assc
    end;
fun assoc1_eq cmp item = let
  fun assc ((k,ob)::rst) = if cmp(item,k) = EQUAL then SOME ob else assc rst
    | assc [] = NONE
in
  assc
end
fun assoc2 item =
   let fun assc ((ob,key)::rst) = if (item=key) then SOME ob else assc rst
         | assc [] = NONE
    in assc
    end;

fun tmpair_eq (t11,t12) (t21,t22) = aconv t11 t21 andalso aconv t12 t22
fun allpairs f l1 l2 = itlist (op_union tmpair_eq o C map l2 o f) l1 []

fun thm_eq th1 th2 = let
  val (h1, c1) = dest_thm th1
  val (h2, c2) = dest_thm th2
  fun all_aconv [] [] = true
    | all_aconv [] _ = false
    | all_aconv _ [] = false
    | all_aconv (h1::t1) (h2::t2) = aconv h1 h2 andalso all_aconv t1 t2
in
  all_aconv h1 h2 andalso aconv c1 c2
end

fun tmi_eq (tm1,i1:int) (tm2,i2) = aconv tm1 tm2 andalso i1 = i2

val the_true = T
val the_false = F

fun type_match vty cty sofar =
  if is_vartype vty
  then if ((vty = cty) orelse
           (case subst_assoc (equal vty) sofar
             of SOME ty => (ty = cty)
              | NONE => false))
       then sofar
       else {redex=vty, residue=cty}::sofar
  else let val (vop,vargs) = dest_type vty
           and (cop,cargs) = dest_type cty
       in
         if vop = cop
         then itlist2 type_match vargs cargs sofar
         else failwith "type_match"
       end;


fun is_beq tm = (type_of (lhs tm) = bool) handle HOL_ERR _ => false;

(*---------------------------------------------------------------------------*
 * Global constant.                                                          *
 *---------------------------------------------------------------------------*)

val offinc = 10000;;     (* NB: should be bigger than all variable codes.    *)


(* ------------------------------------------------------------------------- *)
(* Some "flags".                                                             *)
(* ------------------------------------------------------------------------- *)

val inferences = ref 0;;        (* Inference counter                         *)

val depth = ref false;;         (* Use depth not inference bound.            *)

val prefine = ref true;;        (* Plaisted's "positive refinement".         *)

val precheck = ref false;;      (* Precheck ancestors for repetitions.       *)

val dcutin = ref 1;;            (* Min size for d-and-c optimization cut-in. *)

val skew = ref 3;;              (* Skew proof bias (one side is <= n / skew) *)

val cache = ref true;;          (* Cache continuations                       *)

val chatting = ref (if !Globals.interactive then 1 else 0);
                                (* Gives intermediate info as proof runs.
                                   When the number is 1, then minimal output
                                   is given. When the number is 0, no output
                                   is given. Otherwise, jrh's original output
                                   is given.                                 *)
val _ = register_trace("meson", chatting, 2);



(* ------------------------------------------------------------------------- *)
(* Shadow syntax for FOL terms in NNF. Functions and predicates have         *)
(* numeric codes, and negation is done by negating the predicate code.       *)
(* ------------------------------------------------------------------------- *)


datatype fol_term = Var of int
                  | Fnapp of int * fol_term list;;

type fol_atom = int * fol_term list;;

datatype fol_form = Atom   of fol_atom
                  | Conj   of fol_form * fol_form
                  | Disj   of fol_form * fol_form
                  | Forall of int * fol_form;;

(* ------------------------------------------------------------------------- *)
(* Translate a term (in NNF) into the shadow syntax.                         *)
(* ------------------------------------------------------------------------- *)

local
  val vstore = ref ([]:(term * int) list)
  val gstore = ref ([]:(term * int) list)
  val vcounter = ref 0
  fun inc_vcounter () =
    let
      val n = !vcounter
      val m = n + 1
    in
      if (m >= offinc) then
        raise failwith "inc_vcounter: too many variables"
      else
        (vcounter := m; n)
    end
  fun hol_of_var v =
     case assoc2 v (!vstore)
      of NONE => assoc2 v (!gstore)
       | x => x
  fun hol_of_bumped_var v =
    case (hol_of_var v)
     of SOME x => x
      | NONE =>
         let val v' = v mod offinc
             val hv' = case (hol_of_var v')
                        of SOME y => y
                         | NONE => failwith "hol_of_bumped_var"
             val gv = genvar (type_of hv')
         in
            gstore := (gv, v)::(!gstore);
            gv
         end
in
  fun reset_vars () = (vstore := []; gstore := []; vcounter := 0)
  fun fol_of_var (v:term) =
    let val currentvars = !vstore
    in case op_assoc1 aconv v currentvars
        of SOME x => x
         | NONE =>
            let val n = inc_vcounter()
            in vstore := (v,n)::currentvars; n
            end
    end
  val hol_of_var = hol_of_bumped_var
end;

local
  val cstore = ref ([]:(term * int) list)
  val ccounter = ref 2
in
  fun reset_consts () = (cstore := [(the_false, 1)]; ccounter := 2)
  fun fol_of_const c =
    let
      val currentconsts = !cstore
    in
      case assoc1_eq Term.compare c currentconsts of
        SOME x => x
      | NONE =>
        let val n = !ccounter
        in
          ccounter := n + 1;
          cstore := (c,n)::currentconsts;
          n
        end
    end
  fun hol_of_const c =
     case assoc2 c (!cstore)
      of SOME x => x
       | NONE => failwith "hol_of_const"
end;

fun fol_of_term env consts tm =
  if is_var tm andalso not (op_mem aconv tm consts) then Var(fol_of_var tm)
  else
    let val (f,args) = strip_comb tm
    in if op_mem aconv f env then failwith "fol_of_term: higher order"
       else let val ff = fol_of_const f
            in Fnapp(ff, map (fol_of_term env consts) args)
            end
    end

fun fol_of_atom env consts tm =
  let val (f,args) = strip_comb tm
  in if op_mem aconv f env then failwith "fol_of_atom: higher order"
     else (fol_of_const f, map (fol_of_term env consts) args)
  end

fun fol_of_literal env consts tm =
  let val tm' = dest_neg tm
      val (p,a) = fol_of_atom env consts tm'
  in
    (~p,a)
  end
  handle HOL_ERR _ => fol_of_atom env consts tm

val subtract = op_set_diff aconv
fun fol_of_form env consts tm =
  let val (v,bod) = dest_forall tm
      val fv = fol_of_var v
      val fbod = fol_of_form (v::env) (subtract consts [v]) bod
  in
     Forall(fv,fbod)
  end
  handle HOL_ERR _ =>
    let val (l,r) = dest_conj tm
        val fl = fol_of_form env consts l
        val fr = fol_of_form env consts r
    in
        Conj(fl,fr)
    end
  handle HOL_ERR _ =>
    let val (l,r) = dest_disj tm
        val fl = fol_of_form env consts l
        and fr = fol_of_form env consts r
    in
        Disj(fl,fr)
    end
  handle HOL_ERR _ => Atom(fol_of_literal env consts tm);;

(* ------------------------------------------------------------------------- *)
(* Further translation functions for HOL formulas.                           *)
(* ------------------------------------------------------------------------- *)

fun hol_of_term tm =
  case tm of
    Var v => hol_of_var v
  | Fnapp(f,args) => list_mk_comb(hol_of_const f,map hol_of_term args);;

fun hol_of_atom (p,args) =
  list_mk_comb(hol_of_const p,map hol_of_term args);;

fun hol_of_literal (p,args) =
  if p < 0 then mk_neg(hol_of_atom(~p,args))
  else hol_of_atom (p,args);;

(* ------------------------------------------------------------------------- *)
(* Versions of shadow syntax operations with variable bumping.               *)
(* ------------------------------------------------------------------------- *)

fun fol_free_in v  =
  let fun freein (Var x) = (x=v)
        | freein (Fnapp(_,lis)) = exists freein lis
  in freein end;

val fol_frees =
  let fun fol_frees (Var x) acc        = insert x acc
        | fol_frees (Fnapp(_,lis)) acc = itlist fol_frees lis acc
  in
    fn tm => fol_frees tm []
  end;


(*---------------------------------------------------------------------------*
 * Short-cutting function applications of various sorts.                     *
 *---------------------------------------------------------------------------*)

local exception Unchanged
      fun qmap f =
        let fun app [] = raise Unchanged
              | app (h::t) =
                 let val t' = app t
                     val h' = f h handle Unchanged => h
                 in h'::t'
                 end
                 handle Unchanged => f h::t
        in app end

      fun qtry f arg = f arg handle Unchanged => arg
in
fun raw_fol_subst theta (Var v) =
       (case assoc2 v theta
         of SOME x => x
          | NONE => raise Unchanged)
  | raw_fol_subst theta (Fnapp(f,args)) =
     Fnapp(f,qmap (raw_fol_subst theta) args);;

fun fol_subst theta tm = raw_fol_subst theta tm handle Unchanged => tm;

fun fol_substl theta tms =
  qmap (raw_fol_subst theta) tms handle Unchanged => tms;;

fun fol_inst theta (at as (p,args)) =
  (p,qmap (raw_fol_subst theta) args) handle Unchanged => at;;

fun raw_fol_subst_bump offset theta tm =
  case tm
   of Var v =>
        if v < offinc
        then let val v' = v + offset
             in case (assoc2 v' theta) of SOME x => x | NONE => Var(v')
             end
        else (case assoc2 v theta of SOME x => x | NONE => raise Unchanged)
    | Fnapp(f,args) =>
      Fnapp(f,qmap (raw_fol_subst_bump offset theta) args);;

fun fol_subst_bump offset theta tm =
  raw_fol_subst_bump offset theta tm handle Unchanged => tm;;

fun fol_inst_bump offset theta (at as (p,args)) =
  (p,qmap (raw_fol_subst_bump offset theta) args) handle Unchanged => at;;

(* ------------------------------------------------------------------------- *)
(* Versions of "augment_insts" and "fol_unify" with variable offsets.        *)
(* ------------------------------------------------------------------------- *)

val raw_augment_insts =
 let fun augment1 theta (s,x) =
      let val s' = raw_fol_subst theta s
      in if fol_free_in x s andalso not(s = Var(x))
            then failwith "augment1: Occurs check"
            else (s',x)
      end
 in
    fn p => fn insts => p :: qtry (qmap (augment1 [p])) insts
 end;

fun qpartition p m =
 let fun qpart l =
   if l=m then raise Unchanged else
   case l
    of [] => raise Unchanged
     | h::t => if p h
                 then let val (yes,no) = qpart t in (h::yes,no) end
                      handle Unchanged => ([h],t)
                 else let val (yes,no) = qpart t in (yes,h::no) end
 in
    fn l => qpart l handle Unchanged => ([], l)
 end
end;

fun augment_insts offset (t,v) insts =
  let val t' = fol_subst_bump offset insts t
      val p = (t',v)
  in
    case t' of
      Var(w) =>
        if w <= v then
          if w = v then insts else raw_augment_insts p insts
        else raw_augment_insts (Var(v),w) insts
    | _ =>
        if fol_free_in v t' then failwith "augment_insts: Occurs check"
        else raw_augment_insts p insts
  end;

fun fol_unify offset tm1 tm2 sofar =
  if tm1 = tm2 then sofar else
  case tm1 of
    Var(x) =>
      let val x' = if x < offinc then x + offset else x
      in case assoc2 x' sofar
          of SOME tm1' => fol_unify offset tm1' tm2 sofar
           | NONE      => augment_insts offset (tm2,x') sofar
      end
  | Fnapp(f1,args1) =>
      (case tm2 of
        Var(y) =>
          let val y' = if y < offinc then y + offset else y
          in case assoc2 y' sofar
              of SOME tm2' => fol_unify offset tm1 tm2' sofar
               | NONE      => augment_insts offset (tm1,y') sofar
          end
      | Fnapp(f2,args2) =>
          if f1 = f2
          then rev_itlist2 (fol_unify offset) args1 args2 sofar
          else failwith "fol_unify: No match");

(* ------------------------------------------------------------------------- *)
(* Test for equality under the pending instantiations.                       *)
(* ------------------------------------------------------------------------- *)

fun fol_eq insts tm1 tm2 =
  tm1 = tm2 orelse
  case tm1
   of Var(x) =>
      (case assoc2 x insts
        of SOME tm1' => fol_eq insts tm1' tm2
         | NONE =>
            (case tm2
              of Var(y) => (if x = y then true
                            else case (assoc2 y insts)
                                  of SOME tm2' => (tm1 = tm2')
                                   | NONE      => (tm1 = tm2))
               | _ => false))
   | Fnapp(f1,args1) =>
      case tm2
       of Var(y) =>
           (case assoc2 y insts
             of SOME tm2' => fol_eq insts tm1 tm2'
              | NONE      => false)
       | Fnapp(f2,args2) =>
           if f1 = f2 then Lib.all2 (fol_eq insts) args1 args2
                      else false;


fun fol_atom_eq insts (p1,args1) (p2,args2) =
  (p1 = p2) andalso Lib.all2 (fol_eq insts) args1 args2;;

(* ------------------------------------------------------------------------- *)
(* Cacheing continuations. Very crude, but it works remarkably well.         *)
(* ------------------------------------------------------------------------- *)

fun cacheconts f =
 if !cache
 then let val memory = ref []
      in fn input as (gg, (insts,offset,(size:int))) =>
           if exists (fn (_,(insts',_,size')) =>
                       insts=insts' andalso (size <= size' orelse !depth))
                     (!memory)
           then failwith "cachecont"
           else (memory := input::(!memory); f input)
      end
 else f;;

(* ------------------------------------------------------------------------- *)
(* Check ancestor list for repetition.                                       *)
(* ------------------------------------------------------------------------- *)

fun checkan insts (p:int,a) ancestors =
 if !precheck
 then let val p' = ~p
          val t' = (p',a)
      in case assoc1 p' ancestors
          of NONE => ancestors
           | SOME ours =>
             if exists (fn u => fol_atom_eq insts t' (snd(fst u))) ours
                then failwith "checkan"
                else ancestors
      end
 else ancestors;;

(* ------------------------------------------------------------------------- *)
(* Insert new goal's negation in ancestor clause, given refinement.          *)
(* ------------------------------------------------------------------------- *)

fun insertan insts (p,a) ancestors =
  let val p':int = ~p
      val t' = (p',a)
      val (ourancp,otheranc) = Lib.pluck (fn (pr,_) => pr = p') ancestors
           handle HOL_ERR _ => ((p',[]),ancestors)
      val ouranc = snd ourancp
  in
    if exists (fn u => fol_atom_eq insts t' (snd(fst u))) ouranc
    then failwith "insertan: loop"
    else (p',(([],t'),(0,TRUTH))::ouranc)::otheranc
  end

(* ------------------------------------------------------------------------- *)
(* Recording MESON proof tree.                                               *)
(* ------------------------------------------------------------------------- *)

datatype fol_goal = Subgoal of fol_atom
                               * fol_goal list
                               * (int * thm)
                               * int
                               * (fol_term * int)list;;

(* ------------------------------------------------------------------------- *)
(* Perform basic MESON expansion.                                            *)
(* ------------------------------------------------------------------------- *)

fun meson_single_expand rule ((g,ancestors),(insts,offset,size)) =
 let val ((hyps,conc),tag) = rule
     val allins = rev_itlist2 (fol_unify offset) (snd g) (snd conc) insts
     val (locin,globin) = qpartition (fn (_,v) => offset <= v) insts allins
     fun mk_ihyp h =
         let val h' = fol_inst_bump offset locin h
         in (h', checkan insts h' ancestors)
         end
     val newhyps =  map mk_ihyp hyps
  in
    inferences := !inferences + 1;
    (newhyps, (globin, offset+offinc, size - length hyps))
  end;


(* ------------------------------------------------------------------------- *)
(* Perform first basic expansion which allows continuation call.             *)
(* ------------------------------------------------------------------------- *)

fun meson_expand_cont rules state cont =
  tryfind (fn r => cont (snd r) (meson_single_expand r state)) rules;;

(* ------------------------------------------------------------------------- *)
(* Try expansion and continuation call with either ancestor or initial rule. *)
(* ------------------------------------------------------------------------- *)

fun meson_expand rules ((g,ancestors),(tup as (insts,offset,size))) cont =
 let val pr = fst g
     val newancestors = insertan insts g ancestors
     val newstate = ((g,newancestors),tup)
 in
   (if !prefine andalso pr > 0 then failwith "meson_expand"
    else case (assoc1 pr ancestors)
          of SOME arules => meson_expand_cont arules newstate cont
           | NONE => failwith "not found")
   handle Cut => failwith "meson_expand"
        | HOL_ERR _ =>
           (case (assoc1 pr rules)
             of SOME x =>
                  let val crules = filter (fn ((h,_),_) => length h <= size) x
                  in meson_expand_cont crules newstate cont
                  end
              | NONE => failwith "not found")
           handle Cut => failwith "meson_expand"
 end

(* ------------------------------------------------------------------------- *)
(* Simple Prolog engine which organizes search and backtracking.             *)
(* ------------------------------------------------------------------------- *)

fun expand_goal rules =
  let
    fun exp_goal depth (state as ((g,_),(insts,offset,size))) cont =
      if depth < 0 then failwith "expand_goal: too deep"
      else
        meson_expand rules state
        (fn apprule => fn (newstate as (_,(pinsts,_,_))) =>
         exp_goals (depth-1) newstate
         (cacheconts
          (fn (gs,(newinsts,newoffset,newsize)) =>
           let val (locin,globin) =
                      qpartition (fn (_,v) => offset <= v) pinsts newinsts
               val g' = Subgoal(g,gs,apprule,offset,locin)
           in
             if (globin = insts) andalso null(gs) then
               cont(g',(globin,newoffset,size)) handle HOL_ERR _ => raise Cut
             else
               cont(g',(globin,newoffset,newsize))
               handle Cut => failwith "expand_goal"
           end)))
    and
      exp_goals depth (gl, tup as (insts,offset,size)) cont =
      case gl of
        []    => cont ([],tup)
      | [g]   => exp_goal depth (g,tup) (fn (g',stup) => cont([g'],stup))
      | g::gs =>
        if size >= !dcutin
        then let val lsize = size div (!skew)
                 val rsize = size - lsize
                 val (lgoals,rgoals) = chop_list (length gl div 2) gl
             in
              exp_goals depth (lgoals,(insts,offset,lsize))
                (cacheconts(fn (lg',(i,off,n)) =>
                            exp_goals depth (rgoals,(i,off,n + rsize))
                          (cacheconts(fn (rg',ztup) => cont (lg'@rg',ztup)))))
              handle HOL_ERR _ =>
                exp_goals depth (rgoals,(insts,offset,lsize))
                (cacheconts(fn (rg',(i,off,n)) =>
                            exp_goals depth (lgoals,(i,off,n + rsize))
                            (cacheconts (fn (lg',ztup as (_,_,fsize)) =>
                                   if n + rsize <= lsize + fsize
                                    then failwith "repetition of demigoal pair"
                                    else cont (lg'@rg',ztup)))))
            end
        else
            exp_goal depth (g,tup)
                (cacheconts (fn (g',stup) =>
                     exp_goals depth (gs,stup)
                        (cacheconts (fn (gs',ftup) => cont(g'::gs',ftup)))))
  in
    fn g      =>
     fn maxdep =>
      fn maxinf =>
         fn cont => exp_goal maxdep (g,([],2 * offinc,maxinf)) cont
  end

(*
val state = (g,([],2 * offinc,maxinf))
   : ((int * fol_term list)
      * (int * (((int * fol_term list) list * (int * fol_term list)) * (int * thm)) list) list)
     * ((fol_term * int) list * int * int);;

*)
(* ------------------------------------------------------------------------- *)
(* With iterative deepening of inferences or depth.                          *)
(*                                                                           *)
(* NB: If multiple solutions are required, simply give a continuation which  *)
(* stores putative solutions then fails; that will initiate backtracking!    *)
(* ------------------------------------------------------------------------- *)

fun chat n =
  case !chatting
   of 0 => ()
    | 1 => say "."
    | _ => say (String.concat[int_to_string (!inferences),
                              " inferences so far. ",
                              "Searching with maximum size ",
                              int_to_string n, ".\n"]);

fun say_solved n =
  if (n <> 0 andalso n <> 1)
  then say (String.concat["Internal goal solved with ",
                          int_to_string (!inferences),
                          " MESON inferences.\n"])
  else ();

fun solve_goal rules incdepth min max incsize =
 let fun solve n g =
      if n > max then failwith "solve_goal: Too deep"
      else let val _ = chat n
               val gi = if incdepth then expand_goal rules g n 100000 I
                                    else expand_goal rules g 100000 n I
               val _ = say_solved (!chatting)
           in
             gi
           end
           handle HOL_ERR _ => solve (n + incsize) g
 in
    fn g => solve min (g,[])
 end;

(* ------------------------------------------------------------------------- *)
(* Creation of tagged contrapositives from a HOL clause.                     *)
(* This includes any possible support clauses (1 = falsity).                 *)
(* The rules are partitioned into association lists.                         *)
(* ------------------------------------------------------------------------- *)

val fol_of_hol_clauses =
  let
    fun mk_negated (p:int,a) = (~p,a)
    fun mk_contraposes n th used unused sofar =
      case unused
       of [] => sofar
        | h::t =>
            let val new = ((map mk_negated (used @ t),h),(n,th))
            in mk_contraposes (n + 1) th (used@[h]) t (new::sofar)
            end
    fun fol_of_hol_clause th =
      let
        val lconsts = freesl (hyp th)
        val tm = concl th
        val hlits = strip_disj tm
        val flits = map (fol_of_literal [] lconsts) hlits
        val basics = mk_contraposes 0 th [] flits []
      in
        if Lib.all (fn (p,_) => p < 0) flits then
          ((map mk_negated flits,(1,[])),(~1,th))::basics
        else basics
      end
    fun eek (x1,(i1,th1)) (x2,(i2,th2)) =
        (x1=x2) andalso (i1=i2) andalso thm_eq th1 th2
  in
    fn thms =>
    let
      val rawrules = itlist (Lib.op_union eek o fol_of_hol_clause) thms []
      val prs = mk_set (map (fst o snd o fst) rawrules)
      val prules =
        map (fn t => (t,filter (curry op = t o fst o snd o fst) rawrules)) prs
      val srules = sort (fn (p:int,_) => fn (q,_) => abs(p) <= abs(q)) prules
    in
      srules
    end
  end

(* ------------------------------------------------------------------------- *)
(* Optimize a set of clauses (changing literal order complicates HOL stuff). *)
(* ------------------------------------------------------------------------- *)

fun optimize_rules l =
  let
    fun fol_atom_frees (p,a) = fol_frees(Fnapp(p,a))
    fun optimize_clause_order cls =
      sort (fn ((l1,_),_) => fn ((l2,_),_) => length l1 <= length l2) cls
  in
    map (fn (a,b) => (a,optimize_clause_order b)) l
  end


(* ------------------------------------------------------------------------- *)
(* Create a HOL contrapositive on demand, with a cache.                      *)
(* ------------------------------------------------------------------------- *)

local
  open boolTheory
  val DISJ_ASSOC' = SPEC_ALL DISJ_ASSOC
  val DISJ_SYM'   = SPEC_ALL DISJ_SYM
  val DEMORG      = SPEC_ALL DE_MORGAN_THM
  val DEMORG_DISJ = CONJUNCT2 DEMORG
  val DEMORG_AND  = SYM (CONJUNCT1 DEMORG)
  val NOT2        = CONJUNCT1(SPEC_ALL NOT_CLAUSES)
  val NOT_IMP     = IMP_ANTISYM_RULE (SPEC_ALL boolTheory.F_IMP)
                                     (SPEC_ALL boolTheory.IMP_F);

  val DISJ_AC   = EQT_ELIM o AC_CONV (DISJ_ASSOC', DISJ_SYM')
  val imp_CONV  = REWR_CONV(TAUT `a \/ b = ~b ==> a`)
  val push_CONV = GEN_REWRITE_CONV TOP_SWEEP_CONV [DEMORG_DISJ, NOT2]
  and pull_CONV = GEN_REWRITE_CONV DEPTH_CONV [DEMORG_AND]
  and imf_CONV  = REWR_CONV NOT_IMP
  val memory    = ref ([]: ((int * term) * thm) list)
in
  fun clear_contrapos_cache() = memory := []
  fun make_hol_contrapos (n,th) =
    let val tm = concl th
        val key = (n,tm)
        fun key_eq (i1,tm1) (i2,tm2) = aconv tm1 tm2 andalso i1 = i2
    in
     case op_assoc1 key_eq key (!memory)
      of SOME x => x
       | NONE =>
         if n < 0 then CONV_RULE (pull_CONV THENC imf_CONV) th
         else let val djs = strip_disj tm
                  val acth =
                    if n = 0 then th else
                    let val (ldjs,rdjs) = chop_list n djs
                        val ndjs = hd rdjs::(ldjs@(tl rdjs))
                    in
                      EQ_MP (DISJ_AC(mk_eq(tm,list_mk_disj ndjs))) th
                    end
                  val fth = if length djs = 1 then acth
                            else CONV_RULE (imp_CONV THENC push_CONV) acth
              in
               memory := (key,fth)::(!memory);
               fth
              end
    end
end

(* ------------------------------------------------------------------------- *)
(* Translate back the saved proof into HOL.                                  *)
(* ------------------------------------------------------------------------- *)

local
  fun bump_hol_thm offset th =
    let val fvs = subtract (free_vars (concl th)) (freesl(hyp th))
    in INST (map(fn v => {redex=v,residue=hol_of_var(fol_of_var v + offset)})
                 fvs) th
    end
  fun hol_negate tm = dest_neg tm handle HOL_ERR _ => mk_neg tm
  fun merge_inst (t,x) current = (fol_subst current t,x)::current
  val finish_RULE = Rewrite.GEN_REWRITE_RULE I Rewrite.empty_rewrites
                          [TAUT `(~p ==> p) = p`, TAUT `(p ==> ~p) = ~p`]
in
  fun meson_to_hol insts (Subgoal(g,gs,(n,th),offset,locin)) =
    let val newins = itlist merge_inst locin insts
        val g'     = fol_inst newins g
        val hol_g  = hol_of_literal g'
        val ths    = map (meson_to_hol newins) gs
        val hth =
           if aconv (concl th) the_true then ASSUME hol_g
           else let val cth = make_hol_contrapos(n,th)
                in if null ths then cth
                   else Drule.MATCH_MP cth (Lib.end_itlist Thm.CONJ ths)
              handle e as HOL_ERR _ =>
                (say ("Attempting to match\n  "^
                      (term_to_string (concl cth))^"\n\nand\n\n   "^
                      (term_to_string (concl (end_itlist CONJ ths)))^
                      "\n\nwith n = "^ (int_to_string n)^
                      " and th = "^(term_to_string (concl th))^"\n");
                 raise e)
          end
      val ith = HO_PART_MATCH I hth hol_g
    in
      finish_RULE (DISCH (hol_negate(concl ith)) ith)
    end
end

fun ASM_FOL_TAC (asl,w) =
  let val headsp = itlist Canon_Port.get_thm_heads asl ([],[])
  in jrhTactics.RULE_ASSUM_TAC
      (CONV_RULE(Canon_Port.GEN_FOL_CONV headsp)) (asl,w)
  end


(* ------------------------------------------------------------------------- *)
(* Initial canonicalizer.                                                    *)
(* ------------------------------------------------------------------------- *)

val PREMESON_CANON_TAC =
  let fun GSPEC th = SPEC (genvar(type_of(fst(dest_forall(concl th))))) th
      open jrhTactics
  in
    RULE_ASSUM_TAC
    (CONV_RULE
     (PRESIMP_CONV THENC DELAMB_CONV THENC NNFC_CONV THENC SKOLEM_CONV)) THEN
    REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
    ASM_FOL_TAC THEN
    REPEAT(FIRST_X_ASSUM
           ((DISJ_CASES_THEN ORELSE_TCL CONJUNCTS_THEN) ASSUME_TAC)) THEN
    RULE_ASSUM_TAC(CONV_RULE(PRENEX_CONV THENC PROP_CNF_CONV)) THEN
    RULE_ASSUM_TAC(liteLib.repeat GSPEC) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC))
  end


(* ------------------------------------------------------------------------- *)
(* Create equality axioms for all the function and predicate symbols in      *)
(* a HOL term. Not very efficient (but then neither is throwing them into    *)
(* automated proof search!)                                                  *)
(* ------------------------------------------------------------------------- *)

val create_equality_axioms =
  let
    (* open Resolve *)
    val eq_thms = (CONJUNCTS o prove)
      (``(x:'a = x) /\
         (~(x:'a = y) \/ ~(x = z) \/ (y = z))``,
      REWRITE_TAC[] THEN ASM_CASES_TAC ``x:'a = y`` THEN
      ASM_REWRITE_TAC[ONCE_REWRITE_RULE[boolTheory.DISJ_SYM]
                       (REWRITE_RULE[] boolTheory.BOOL_CASES_AX)])
    val imp_elim_CONV = REWR_CONV (TAUT `(a ==> b) = ~a \/ b`)
    val eq_elim_RULE = MATCH_MP(TAUT `(a = b) ==> b \/ ~a`)
    val veq_tm = rator(rator(concl(hd eq_thms)))
    fun create_equivalence_axioms (eq,_) =
      let val tyins = type_match (type_of veq_tm) (type_of eq) []
      in map (INST_TYPE tyins) eq_thms
      end
    val insert_tmi = op_insert tmi_eq
    fun tm_consts tm acc =
      let val (fnc,args) = strip_comb tm
      in if null args then acc
        else itlist tm_consts args (insert_tmi (fnc,length args) acc)
      end
    fun fm_consts tm (acc as (preds,funs)) =
      fm_consts(snd(dest_forall tm)) acc
        handle HOL_ERR _ => fm_consts(snd(dest_exists tm)) acc
        handle HOL_ERR _ =>
           let val (l,r) = dest_conj tm in fm_consts l (fm_consts r acc) end
        handle HOL_ERR _ =>
           let val (l,r) = dest_disj tm in fm_consts l (fm_consts r acc) end
        handle HOL_ERR _ =>
           let val (l,r) = dest_imp tm in fm_consts l (fm_consts r acc) end
        handle HOL_ERR _ => fm_consts (dest_neg tm) acc
        handle HOL_ERR _ =>
           let val (l,r) = dest_eq tm
           in if type_of l = Type.bool
              then fm_consts r (fm_consts l acc)
              else failwith "atomic equality"
           end
        handle HOL_ERR _ =>
           let val (pred,args) = strip_comb tm
           in if null args then acc
              else (insert_tmi (pred,length args) preds,
                    itlist tm_consts args funs)
           end;

    fun create_congruence_axiom pflag (tm,len) =
      let val (atys,rty) = splitlist (fn ty =>
               let val (opn,l) = dest_type ty
               in if opn = "fun" then (hd l,hd(tl l)) else fail()
               end) (type_of tm)
         val ctys = fst(chop_list len atys)
         val largs = map genvar ctys
         and rargs = map genvar ctys
         val th1 = rev_itlist (C (curry MK_COMB))
                             (map (ASSUME o mk_eq) (zip largs rargs)) (REFL tm)
         val th2 = if pflag then eq_elim_RULE th1 else th1
      in
        itlist (fn e => fn th =>
                CONV_RULE imp_elim_CONV (DISCH e th)) (hyp th2) th2
      end
  in
    fn tms =>
    let val (preds,funs) = itlist fm_consts tms ([],[])
        val (eqs0,noneqs) = partition (is_eqc o fst) preds
    in if null eqs0 then []
       else let val pcongs = map (create_congruence_axiom true) noneqs
                and fcongs = map (create_congruence_axiom false) funs
                val (preds1,_) =
                  itlist fm_consts (map concl (pcongs @ fcongs)) ([],[])
                val eqs1 = filter (is_eqc o fst) preds1
                val eqs = op_union tmi_eq eqs0 eqs1
                val equivs = itlist
                  (Lib.op_union thm_eq o create_equivalence_axioms) eqs []
            in
               equivs@pcongs@fcongs
            end
    end
 end

(* ------------------------------------------------------------------------- *)
(* Push duplicated copies of poly theorems to match existing assumptions.    *)
(* ------------------------------------------------------------------------- *)

val (POLY_ASSUME_TAC:thm list -> jrhTactics.Tactic) =
  let
    open jrhTactics
    fun grab_constants tm acc =
      if is_forall tm orelse is_exists tm then
         grab_constants (body(rand tm)) acc
      else
        if is_beq tm orelse is_imp tm orelse is_conj tm orelse is_disj tm then
          grab_constants (rand tm) (grab_constants (lhand tm) acc)
        else
          if is_neg tm then
            grab_constants (rand tm) acc
          else op_union aconv (find_terms is_const tm) acc
    fun match_consts (tm1,tm2) =
      let val {Name=s1,Thy=thy1,Ty=ty1} = dest_thy_const tm1
          and {Name=s2,Thy=thy2,Ty=ty2} = dest_thy_const tm2
      in
        if (s1=s2) andalso (thy1=thy2)
        then type_match ty1 ty2 []
        else failwith "match_consts"
      end
    fun polymorph mconsts th =
      let val tvs = Lib.subtract (type_vars_in_term (concl th))
                                 (Lib.U (map type_vars_in_term (hyp th)))
      in
        if tvs = [] then [th] else
          let
            val pconsts = grab_constants (concl th) []
            val tyins = mapfilter match_consts
              (allpairs (fn x => fn y => (x,y)) pconsts mconsts)
            val ths' = Lib.op_mk_set thm_eq (mapfilter (C INST_TYPE th) tyins)
          in
            if null ths' then
              (if not (!Globals.interactive) then ()
               else say "No useful-looking instantiations of lemma\n";
               [th])
            else ths'
          end
      end

    fun polymorph_all mconsts ths acc =
      if null(ths) then acc else
        let
          val ths' = polymorph mconsts (hd ths)
          val mconsts' = itlist grab_constants (map concl ths') mconsts
        in
          polymorph_all mconsts' (tl ths) (Lib.op_union thm_eq ths' acc)
        end
  in
    fn ths => fn (gl as (asl,w)) =>
    let
      val mconsts = itlist (grab_constants o concl) asl []
      val ths' = polymorph_all mconsts ths []
    in
      MAP_EVERY ASSUME_TAC ths' gl
    end
  end

(* ------------------------------------------------------------------------- *)
(* HOL MESON procedure.                                                      *)
(*                                                                           *)
(* NB! We try all the support clauses in each iterative deepening  run.      *)
(*                                                                           *)
(* This makes sure we get the shortest proof, but it can increase the run    *)
(* time if there is a proof based on the first support clause with similar   *)
(* size. It would be easy to separate out the support-clause trying (and     *)
(* it would save a little time in the assocs to take it out of the main      *)
(* rules too).                                                               *)
(* ------------------------------------------------------------------------- *)

fun SIMPLE_MESON_REFUTE min max inc ths =
  (clear_contrapos_cache();
   inferences := 0;
   let val old_dcutin = !dcutin
   in
     if !depth then dcutin := 100001 else ();
     let
        val ths' = ths @ create_equality_axioms (map concl ths)
        val rules = optimize_rules(fol_of_hol_clauses ths')
        val (proof,(insts,_,_)) = solve_goal rules (!depth) min max inc (1,[])
      in
        dcutin := old_dcutin;
        meson_to_hol insts proof
      end
   end);


fun PURE_MESON_TAC min max inc gl =
  let open jrhTactics
  in
    (reset_vars(); reset_consts();
     (FIRST_ASSUM CONTR_TAC ORELSE
      W(ACCEPT_TAC o SIMPLE_MESON_REFUTE min max inc o fst)) gl)
  end


fun inform tac g =
  let val _ = if (!chatting = 1) then say "Meson search level: " else ()
      val res = tac g
      val _ = if (!chatting = 0) then ()
         else if (!chatting = 1) then say"\n"
              else say  ("  solved with "^(int_to_string (!inferences))^
                         " MESON inferences.\n")
  in  res  end;

fun GEN_MESON_TAC min max step ths g =
 inform
 (REFUTE_THEN ASSUME_TAC
   THEN let open jrhTactics
        in convert (POLY_ASSUME_TAC (map GEN_ALL ths)
                      THEN PREMESON_CANON_TAC
                      THEN PURE_MESON_TAC min max step)
        end) g;


val max_depth = ref 30;
fun ASM_MESON_TAC e = GEN_MESON_TAC 0 (!max_depth) 1 e;

fun MESON_TAC ths = POP_ASSUM_LIST (K ALL_TAC) THEN ASM_MESON_TAC ths;

val _ = Parse.temp_set_grammars ambient_grammars;

end;
