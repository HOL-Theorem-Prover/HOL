(* ========================================================================== *)
(* FILE          : hhsData.sml                                                *)
(* DESCRIPTION   : Storing feature vectors                                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsData :> hhsData =
struct

open HolKernel boolLib Abbrev hhsTools hhsTimeout hhsExec hhsLearn

val ERR = mk_HOL_ERR "hhsData"

(*----------------------------------------------------------------------------
 * Saving feature vectors to disk.
 *----------------------------------------------------------------------------*)

val feature_time = ref 0.0

fun save_lbl (lbl0 as (stac0,t0,g0,gl0)) =
  if mem g0 gl0 then () else
    let
      val fea = total_time feature_time hhsFeature.fea_of_goal g0
      val (lbl as (stac,t,g,gl)) = orthogonalize (lbl0,fea)
      val feav = (lbl,fea)
    in
      update_stacfea_ddict feav
    end

fun mk_graph feavl =
  let 
    val term_graph = ref (dempty Term.compare)
    val type_graph = ref (dempty Type.compare)
    val iterm_graph = ref (dempty Int.compare)
    val itype_graph = ref (dempty Int.compare)
    fun update_ty nl ty =
      let val n = dlength (!type_graph) in
        type_graph := dadd ty (n,nl) (!type_graph);
        itype_graph := dadd n (ty,nl) (!itype_graph);
        n
      end
    fun update_tm nl1 nl2 tm =
      let val n = dlength (!term_graph) in
        term_graph := dadd tm (n,nl1,nl2) (!term_graph);
        iterm_graph := dadd n (tm,nl1,nl2) (!iterm_graph);
        n
      end
    fun add_ty ty = 
      fst (dfind ty (!type_graph)) handle _ => 
      if is_vartype ty then update_ty [] ty else 
        let 
          val {Args,Thy,Tyop} = dest_thy_type ty
          val nl = map add_ty Args
        in
          update_ty nl ty
        end
    fun add_tm tm = 
      #1 (dfind tm (!term_graph)) handle _ => 
      if is_var tm then
        update_tm [] [add_ty (snd (dest_var tm))] tm
      else if is_const tm then 
        let val {Thy, Name, Ty} = dest_thy_const tm in
          update_tm [] [add_ty Ty] tm
        end
      else if is_abs tm then 
        let val (v,t) = dest_abs tm in
          update_tm [add_tm v,add_tm t] [] tm
        end
      else if is_comb tm then     
        let val (t1,t2) = dest_comb tm in
          update_tm [add_tm t1,add_tm t2] [] tm
        end
      else raise ERR "mk_graph" ""
    fun add_goal (asl,w) =
      (ignore (add_tm w); app (ignore o add_tm) asl) 
    fun add_feav ((_,_,g,gl),_) =
      (add_goal g; app add_goal gl)
  in
    app add_feav feavl;
    (!type_graph, !term_graph, !itype_graph, !iterm_graph)
  end

val sep = "$"
val csep = #"$"
fun is_sep c = c = csep
val line_sep = "__SEP__"

fun contain_sep s = mem csep (explode s) orelse mem #"\n" (explode s)

fun mk_record sl = 
  if exists contain_sep sl
    then raise ERR "mk_record" (String.concatWith "--" sl)
    else String.concatWith sep sl
    
fun export_feav feavl =
  let 
    val its = int_to_string
    val file = hhs_feature_dir ^ "/" ^ current_theory ()
    val _ = erase_file file
    val oc = TextIO.openAppend file
    fun os s = TextIO.output (oc, s ^ "\n")
    val (type_graph,term_graph,itype_graph,iterm_graph) = mk_graph feavl  
    val tygr = map snd (dlist type_graph)
    val tysort = topo_sort tygr
    val tmgr = map (fn (_,(n,nl1,_)) => (n,nl1)) (dlist term_graph)
    val tmsort = topo_sort tmgr
    fun log_ty n =
      let 
        val (ty,nl) = dfind n itype_graph 
        handle _ => raise ERR "export_feav" "0"
      in
        if is_vartype ty then 
          mk_record [its n,"U",dest_vartype ty]
        else
          let val {Thy,Tyop,...} = dest_thy_type ty in
            mk_record ([its n,"T",Thy,Tyop] @ map its nl)
          end 
      end
    fun log_tm n =
      let 
        val (tm,nl1,nl2) = dfind n iterm_graph 
        handle _ => raise ERR "export_feav" "1"
      in
        if is_var tm then 
          mk_record [its n,"V",fst (dest_var tm),its (hd nl2)]
        else if is_const tm then  
          let val {Thy,Name,...} = dest_thy_const tm in
            mk_record [its n,"C",Thy,Name,its (hd nl2)]
          end
        else if is_abs tm then
          let val (v,t) = dest_abs tm in
            mk_record ([its n,"A"] @ map its nl1)
          end
        else if is_comb tm then
          let val (t1,t2) = dest_comb tm in
            mk_record ([its n,"B"] @ map its nl1)
          end
        else raise ERR "export_feav" "3"
      end
    fun log_goal (asl,w) =
      let fun lookup t = #1 (dfind t term_graph) 
        handle _ => raise ERR "export_feav" "2" 
      in
        String.concatWith " " (map (its o lookup) (w :: asl))
      end
    fun log_feav (lbl as (stac,tim,g,gl),fea) =
      (
      os stac;
      os (Real.toString tim);
      os (log_goal g);
      os line_sep;
      app (os o log_goal) gl;
      os line_sep;
      os (String.concatWith sep fea);
      os line_sep
      )
  in
    app (os o log_ty) tysort;
    os line_sep;
    app (os o log_tm) tmsort;
    os line_sep;
    app log_feav feavl;
    TextIO.closeOut oc
  end

(*----------------------------------------------------------------------------
 * Reading feature vectors from disk.
 *----------------------------------------------------------------------------*)

fun read_graph (tyl,tml) =
  let 
    fun C s t ty = mk_thy_const {Thy=s,Name=t,Ty=ty}
    fun T s t a  = mk_thy_type {Thy=s,Tyop=t,Args=a}
    fun V s ty   = mk_var (s,ty)
    fun A v t    = mk_abs (v,t)
    fun B t1 t2  = mk_comb (t1,t2)
    val sti = string_to_int
    val type_graph = ref (dempty Int.compare)
    val term_graph = ref (dempty Int.compare)
    fun update_ty ns ty = type_graph := dadd (sti ns) ty (!type_graph)
    fun update_tm ns tm = term_graph := dadd (sti ns) tm (!term_graph)
    fun lookup_ty ns = dfind (sti ns) (!type_graph)
    fun lookup_tm ns = dfind (sti ns) (!term_graph)
    fun fty s =
      case String.tokens is_sep s of
        ns :: "U" :: vs :: [] => 
        update_ty ns (mk_vartype vs)
      | ns :: "T" :: Thy :: Tyop :: m => 
        update_ty ns (T Thy Tyop (map lookup_ty m))
      | [] => ()
      | _ => raise ERR "read_graph" "wrong type format"
    fun ftm s =
      case String.tokens is_sep s of
        ns :: "V" :: vs :: tyn :: [] => 
        update_tm ns (V vs (lookup_ty tyn))
      | ns :: "C" :: Thy :: Name :: tyn :: [] => 
        update_tm ns (C Thy Name (lookup_ty tyn))
      | ns :: "A" :: n1 :: n2 :: [] => 
        update_tm ns (A (lookup_tm n1) (lookup_tm n2))
      | ns :: "B" :: n1 :: n2 :: [] => 
        update_tm ns (B (lookup_tm n1) (lookup_tm n2))
      | [] => ()
      | _ => raise ERR "read_graph" "wrong term format"
  in
    app fty tyl;
    app ftm tml;
    (!type_graph,!term_graph)
  end

exception EmptyThy

fun read_init thy ll = case ll of
    l1 :: l2 :: m => (l1,l2,m)
  | _ => (print "Empty theory"; raise EmptyThy)

fun read_feavl ll = case ll of
    [stac,ts,gs] :: gsl :: [fea] :: m => 
    (stac,ts,gs,gsl,fea) :: read_feavl m
  | a :: b :: c :: d :: m => raise ERR "read_feav" "wrong format"
  | _ => []

fun read_feav thy =
  if mem thy ["min","bool"] then [] else
  let
    val sl = readl_empty (hhs_feature_dir ^ "/" ^ thy)
             handle _ => (print_endline ("File not found:" ^ thy); [])
    val sll = rpt_split_sl line_sep sl
    val (tyl,tml,cont) = read_init thy sll
    val (_,term_graph) = read_graph (tyl,tml)
    fun lookup_tm ns = dfind (string_to_int ns) term_graph
    val feavsl = read_feavl cont
    fun parse_goal gs = case String.tokens Char.isSpace gs of
        []     => raise ERR "parse_goal" ""
      | a :: m => (map lookup_tm m, lookup_tm a)
    fun parse_feav (stac,t,gs,gsl,fea) =
      ((stac, valOf (Real.fromString t), parse_goal gs, map parse_goal gsl), 
       String.tokens is_sep fea)
  in
    map parse_feav feavsl
  end
  handle EmptyThy => []

fun import_feav thyl = 
  (
  print_endline "Importing feature vectors";
  List.concat (map read_feav thyl)
  )


end (* struct *)
