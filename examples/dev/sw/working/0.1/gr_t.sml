(*
 *  gr_t.sml  --  graph implementations based on balanced binary search tress
 *
 *  COPYRIGHT (c) 1997 by Martin Erwig.  See COPYRIGHT file for details.
 *)
 
(*
   structures and functors defined:

    Graph,
    UnlabGraph:
      A graph is represented by pair (t,m) where t is a search tree 
      storing labels, predecessors, and successors, and m is
      the maximum node value in the domain of t. 
  
   GraphFwd,
   UnlabGraphFwd:  
     Only successors are stored. This speeds up the operations 
     "suc" and "anySuc" that do not access the full context
     
   Employed utilities:
     UTuple:
       p1 (x,y) = x
       P2 f (x,y) = (x,f y)
     UList:
       cons x l = x::l
       select f p l = map f (filter p l)
*)


local (* local scope for auxiliary definitions *)

(* 
   auxiliary structures:
   
     AdjUtil     utilities on adjacency structures, just the definitions
                 shared by MapUtil and MapUtilFwd
     MapUtil     utilities for (node->context) maps 
     MapUtilFwd  utilities for maps, for forward represenation

     ShareAll    function definitions shared by all implementations   
     ShareFwd    function definitions shared by forward implementations
*)

structure AdjUtil =
struct
  (* 
     updAdj (t,l,f)     repeatedly updates the context entries for
                        each node in l by adding either a successor or 
                        a predecessor as specified by f
     updLabAdj          ... similar for labeled graphs
     remFrom (t,v,l,Fi) remove v from the successor or predecessor lists of 
                        all nodes in l. 
                        T2 : pred in full tree
                        T3 : suc  in full tree
                        P2 : suc  in fwd  tree --> is not used
     remFromLab        ... similar in labeled graphs
     any               selects arbitrary node and apply match or matchFwd
  *)   
  structure M = IntBinaryMapUpd
  open GraphExceptions UTuple UGeneral
  
  fun updAdj (t,[],f)   = t
   |  updAdj (t,v::l,f) = updAdj (M.update (t,v,f),l,f) 
      handle Binaryset.NotFound => raise Edge
  fun updLabAdj (t,[],f)         = t
   |  updLabAdj (t,(lab,v)::l,f) = updLabAdj (M.update (t,v,f lab),l,f) 
      handle Binaryset.NotFound => raise Edge
  fun remFrom (t,v,[],F)   = t
   |  remFrom (t,v,x::l,F) =
      remFrom (M.update (t,x,F (List.filter (neq v))),v,l,F)
  fun remFromLab (t,v,[],F)   = t
   |  remFromLab (t,v,(_,x)::l,F) = 
      remFromLab (M.update (t,x,F (List.filter (neq v o p2))),v,l,F)
  fun any proj (g as (t,m)) = proj (#1 (valOf (M.findSome t)),g)
                              handle Option => raise Match
end

structure MapUtil =
struct
  (*   
     addSuc, addPred   add a node to successor/predecessor list
                       (functions to be passed as arguments to M.update)
     addLabSuc, 
     addLabPred        ... similar for labeled graphs
     mkContext         rearranges map entry to a context value
  *)
  open AdjUtil
  fun addSuc v (l,p,s) = (l,p,v::s)
  fun addPred v (l,p,s) = (l,v::p,s)
  fun addLabSuc v lab (l,p,s) = (l,p,(lab,v)::s)
  fun addLabPred v lab (l,p,s) = (l,(lab,v)::p,s)
  fun mkContext (n,(l,p,s)) = (p,n,l,s) handle Option => raise Match
  fun mkFwdAdj (l,p,s) = (l,s) handle Option => raise Match
  fun mkBwdAdj (l,p,s) = (l,p) handle Option => raise Match
end 

structure MapUtilFwd =
struct
  open AdjUtil
  fun addSuc v (l,s) = (l,v::s)
  fun addLabSuc v lab (l,s) = (l,(lab,v)::s)
  fun mkFwd (n,(t,(l,s)),m:int) = ((l,s),(t,if m=n then m-1 else m))
end 


(*
   shared implementations
*)
structure ShareAll =
struct
  structure M = IntBinaryMapUpd
  
  val empty              = (M.empty,0)
  fun isEmpty  (t,_)     = case (M.findSome t) of NONE=>true | _=>false
  fun nodes    (t,_)     = map UTuple.p1 (M.listItemsi t)
  fun noNodes  (t,_)     = M.numItems t
  fun newNodes i (_,m)   = UGeneral.to (m+1,m+i)
end


structure ShareFwd =
struct
  structure M = IntBinaryMapUpd
  open GraphExceptions

  fun match       _  = raise NotImplemented
  fun matchAny    _  = raise NotImplemented
  fun matchFwd    _  = raise NotImplemented (* must scan all edges to ...  *)
  fun matchAnyFwd _  = raise NotImplemented (* ... remove n from suc-lists *)
  fun context     _  = raise NotImplemented
  fun bwd         _  = raise NotImplemented
  fun pred        _  = raise NotImplemented
  fun ufold _ _ _       = raise NotImplemented
  fun gfold _ _ _ _ _ _ = raise NotImplemented
  fun fwd (n,(t,_))  = valOf (M.find (t,n)) handle Option => raise Match
  fun labNodes (t,_) = map (UTuple.P2 UTuple.p1) (M.listItemsi t)
end


in (* scope of auxiliary definitions *)


structure Graph : GRAPH =
struct
  structure M = IntBinaryMapUpd
  open GraphNode GraphExceptions MapUtil UTuple

  type ('a,'b) graph = ('a * ('b * node) list * ('b * node) list) M.map * int

  structure Types = GraphTypes (struct type ('a,'b) graph=('a,'b) graph end)
  open Types

  (* exported functions *)
 
  open ShareAll
  
  fun embed ((pred,n,l,suc),(t,m)) = 
      case M.find (t,n) of NONE => 
         let val t1 = M.insert (t,n,(l,pred,suc))
             val t2 = updLabAdj (t1,pred,addLabSuc n)
             val t3 = updLabAdj (t2,suc,addLabPred n)
          in
             (t3,Int.max (n,m))
         end
      | _ => raise Node

  fun match (n,(t,m)) = 
      let val (t1,(l,p,s)) = M.remove (t,n)
          val p' = List.filter (neq n o p2) p
          val s' = List.filter (neq n o p2) s
          val t2 = remFromLab (t1,n,s',T2) (* rem. n from each pred-list of s *)
          val t3 = remFromLab (t2,n,p',T3) (* rem. n from each suc-list of p *)
       in ((p',n,l,s),(t3,if m=n then m-1 else m)) end
(*
      handle Binaryset.NotFound => raise Match
*)
      handle Binaryset.NotFound => 
      (print ("match "^Int.toString n^" in graph:\n");
       map (fn x=>print (Int.toString x^",")) (nodes (t,m));
       raise Match)

  fun matchFwd    n_g     = P1 q34 (match n_g)
  fun matchAny    g       = any match g
  fun matchAnyFwd g       = any matchFwd g
  (*
  fun matchOrd (n,l,l',g) = let val ((p,_,lab,s),g') = match (n,g)
      in ((SortEdges.labsort (l,p),n,lab,SortEdges.labsort (l',s)),g') end
  fun matchOrdFwd (n,l,g) = let val ((lab,s),g') = matchFwd (n,g) 
      in ((lab,SortEdges.labsort (l,s)),g') end
  *)

  fun context  (n,(t,_))  = mkContext (n,valOf (M.find (t,n)))
  fun fwd      (n,(t,_))  = mkFwdAdj (valOf (M.find (t,n)))
  fun bwd      (n,(t,_))  = mkBwdAdj (valOf (M.find (t,n)))
  fun suc      g          = map p2 (p2 (fwd g))
  fun pred     g          = map p2 (p2 (bwd g))
  fun labNodes (t,_)      = map (P2 t1) (M.listItemsi t)

  fun ufold f u g = if isEmpty g then u else
                    let val (c,g') = matchAny g
                     in f (c,ufold f u g') end
                
  fun gfold f d b u l g = if isEmpty g then u else
      let fun gfold1 v g = 
              let val (c as (_,_,l,_),g1) = match (v,g)
                  val (r,g2) = gfoldn (f c) g1
               in (d (l,r),g2) end
          and gfoldn []     g = (u,g)
           |  gfoldn (v::l) g = 
              let val (x,g1) = gfold1 v g
                  val (y,g2) = gfoldn l g1
               in (b (x,y),g2) end
              handle Match => gfoldn l g
        in
           #1 (gfoldn l g)
       end

  fun mkgr (nl,el) =
      let fun insNodes (t,i,[])   = t
           |  insNodes (t,i,v::l) = insNodes (M.insert (t,i,(v,[],[])),i+1,l)
          fun insEdges (t,[])          = t
           |  insEdges (t,(v,w,l)::el) = 
              let val t1 = M.update (t,v,addLabSuc w l)
                  val t2 = M.update (t1,w,addLabPred v l)
               in insEdges (t2,el) end
              handle Binaryset.NotFound => raise Edge
       in
          (insEdges (insNodes (M.empty,0,nl),el),length nl-1)
      end
  fun adj (t,_) = map (fn (v,(l,p,s))=>(v,(l,s))) (M.listItemsi t)
end (* structure Graph *)


structure UnlabGraph : UNLAB_GRAPH =
struct
  structure M = IntBinaryMapUpd
  open GraphNode GraphExceptions MapUtil UTuple

  type 'a graph = ('a * node list * node list) M.map * int

  structure Types = UnlabGraphTypes (struct type 'a graph='a graph end)
  open Types

  (* exported functions *)
 
  open ShareAll
  
  fun embed ((pred,n,l,suc),(t,m)) = 
      case M.find (t,n) of NONE => 
         let val t1 = M.insert (t,n,(l,pred,suc))
             val t2 = updAdj (t1,pred,addSuc n)
             val t3 = updAdj (t2,suc,addPred n)
          in (t3,Int.max (n,m)) end
      | _ => raise Node

  fun match (n,(t,m)) = 
      let val (t1,(l,p,s)) = M.remove (t,n)
          val p' = List.filter (neq n) p
          val s' = List.filter (neq n) s
          val t2 = remFrom (t1,n,s',T2) (* rem. n from each pred-list of s *)
          val t3 = remFrom (t2,n,p',T3) (* rem. n from each suc-list of p *)
       in ((p',n,l,s),(t3,if m=n then m-1 else m)) end
      handle Binaryset.NotFound => raise Match

  fun matchFwd    n_g    = P1 q34 (match n_g)
  fun matchAny    g      = any match g
  fun matchAnyFwd g      = any matchFwd g
  fun context  (n,(t,_)) = mkContext (n,valOf (M.find (t,n)))
  fun fwd      (n,(t,_)) = mkFwdAdj (valOf (M.find (t,n)))
  fun bwd      (n,(t,_)) = mkBwdAdj (valOf (M.find (t,n)))
  fun suc      g         = p2 (fwd g)
  fun pred     g         = p2 (bwd g)
  fun labNodes (t,_)     = map (P2 t1) (M.listItemsi t)
  
  fun ufold f u g = if isEmpty g then u else
                    let val (c,g') = matchAny g
                     in f (c,ufold f u g') end
                
  fun gfold f d b u l g = if isEmpty g then u else
      let fun gfold1 v g = 
              let val (c as (_,_,l,_),g1) = match (v,g)
                  val (r,g2) = gfoldn (f c) g1
               in (d (l,r),g2) end
          and gfoldn []     g = (u,g)
           |  gfoldn (v::l) g = 
              let val (x,g1) = gfold1 v g
                  val (y,g2) = gfoldn l g1
               in (b (x,y),g2) end
              handle Match => gfoldn l g
        in
           #1 (gfoldn l g)
       end
                
  fun mkgr (nl,el) =
      let fun insNodes (t,_,[])   = t
           |  insNodes (t,i,v::l) = insNodes (M.insert (t,i,(v,[],[])),i+1,l)
          fun insEdges (t,[])        = t
           |  insEdges (t,(v,w)::el) = 
              let val t1 = M.update (t,v,addSuc w)
                  val t2 = M.update (t1,w,addPred v)
               in insEdges (t2,el) end
              handle Binaryset.NotFound => raise Edge
       in
          (insEdges (insNodes (M.empty,0,nl),el),length nl-1)
      end
  fun adj (t,_) = map (fn (v,(l,p,s))=>(v,(l,s))) (M.listItemsi t)
end (* structure UnlabGraph *)


structure GraphFwd : GRAPH =
struct
  structure M = IntBinaryMapUpd
  open GraphExceptions MapUtilFwd UTuple

  type ('a,'b) graph = ('a * ('b * GraphNode.node) list) M.map * int

  structure Types = GraphTypes (struct type ('a,'b) graph=('a,'b) graph end)
  open Types

  (* exported functions *)
 
  open ShareAll
  open ShareFwd

  fun embed ((pred,n,l,suc),(t,m)) = 
      case M.find (t,n) of NONE => 
         let val t1 = M.insert (t,n,(l,suc))
             val t2 = updLabAdj (t1,pred,addLabSuc n)
          in
             (t2,Int.max (n,m))
         end
      | _ => raise Node
      
  fun matchOrd    _ = raise NotImplemented
  fun matchOrdFwd _ = raise NotImplemented
  fun suc         g = map p2 (p2 (fwd g))

  fun mkgr (nl,el) =
      let fun insNodes (t,i,[])   = t
           |  insNodes (t,i,v::l) = insNodes (M.insert (t,i,(v,[])),i+1,l)
          fun insEdges (t,[])          = t
           |  insEdges (t,(v,w,l)::el) = insEdges (M.update (t,v,addLabSuc w l),el)
              handle Binaryset.NotFound => raise Edge
       in
          (insEdges (insNodes (M.empty,0,nl),el),length nl-1)
      end
  fun adj (t,_) = M.listItemsi t
end (* structure GraphFwd *)


structure UnlabGraphFwd : UNLAB_GRAPH =
struct
  structure M = IntBinaryMapUpd
  open GraphNode GraphExceptions MapUtilFwd UTuple

  type 'a graph = ('a * node list) M.map * int

  structure Types = UnlabGraphTypes (struct type 'a graph='a graph end)
  open Types

  (* exported functions *)
 
  open ShareAll
  open ShareFwd
  
  fun embed ((pred,n,l,suc),(t,m)) = 
      case M.find (t,n) of NONE => 
         let val t1 = M.insert (t,n,(l,suc))
             val t2 = updAdj (t1,pred,addSuc n)
          in
             (t2,Int.max (n,m))
         end
      | _ => raise Node
      
  fun suc         g         = p2 (fwd g)

  fun mkgr (nl,el) =
      let fun insNodes (t,_,[])   = t
           |  insNodes (t,i,v::l) = insNodes (M.insert (t,i,(v,[])),i+1,l)
          fun insEdges (t,[])        = t
           |  insEdges (t,(v,w)::el) = insEdges (M.update (t,v,addSuc w),el)
              handle Binaryset.NotFound => raise Edge
       in
          (insEdges (insNodes (M.empty,0,nl),el),length nl-1)
      end
  fun adj (t,_) = M.listItemsi t
end (* structure UnlabGraphFwd *)

end (* of local scope *)
