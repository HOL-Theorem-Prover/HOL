(****************************************************************************)
(* FILE          : congruence.sml                                           *)
(* DESCRIPTION   : Congruence closure algorithm for deciding the theory of  *)
(*                 uninterpreted function symbols.                          *)
(*                 (Nelson and Oppen, Journal of the ACM, 27(2), pp356-364.)*)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 27th February 1995                                       *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 20th August 1996                                         *)
(****************************************************************************)

structure CongruenceClosure =
struct

local

open Exception Lib Dsyntax Psyntax 
     DecisionConv DecisionSupport 
     DecisionNormConvs LazyThm LazyRules;

in

fun failwith function = raise HOL_ERR{origin_structure = "CongruenceClosure",
                                      origin_function = function,
                                      message = ""};

type thm = LazyThm.pre_thm;

(*==========================================================================*)
(* Directed Graphs                                                          *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* A graph is represented as a list of vertices each with a list of         *)
(* vertices that are adjacent to it.                                        *)
(*--------------------------------------------------------------------------*)

datatype graph = Graph of (int * int list) list;

fun successors (Graph rep) vertex =
   assoc vertex rep handle HOL_ERR _ => [];

fun predecessors (Graph rep) vertex =
   map #1 (filter (fn (_,adjs) => member vertex adjs) rep);

(*==========================================================================*)
(* Equivalence classes                                                      *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* The integers are labels of vertices in a graph.                          *)
(* The terms are the heads of the left-hand side of the corresponding       *)
(* theorem and so are always variables or constants not compound terms.     *)
(*                                                                          *)
(* Examples:                                                                *)
(*                                                                          *)
(*    Vertex ((i,h),|- t = t)                                               *)
(*    Equivalent ((i1,h1),|- t1 = t2,Equivalent ((i2,h2),|- t2 = ...,...))  *)
(*                                                                          *)
(* where each t_j is of the form (h_j x1 ... xn), i.e., h_j applied to n    *)
(* curried arguments.                                                       *)
(*--------------------------------------------------------------------------*)

datatype equivalence = Vertex of (int * term) * thm
                     | Equivalent of (int * term) * thm * equivalence;

(*--------------------------------------------------------------------------*)
(* Failure to find a vertex in an equivalence class.                        *)
(*--------------------------------------------------------------------------*)

exception Find;

(*--------------------------------------------------------------------------*)
(* in_equivalence : int -> equivalence -> bool                              *)
(*                                                                          *)
(* Tests for the presence of a vertex in an equivalence class.              *)
(*--------------------------------------------------------------------------*)

fun in_equivalence v (Vertex ((i,_),_)) = (v = i)
  | in_equivalence v (Equivalent ((i,_),_,equiv)) =
   (v = i) orelse (in_equivalence v equiv);

(*--------------------------------------------------------------------------*)
(* find_equiv : equivalence list -> int -> equivalence                      *)
(*                                                                          *)
(* Find which equivalence class (if any) in a list contains a particular    *)
(* vertex.                                                                  *)
(*--------------------------------------------------------------------------*)

fun find_equiv [] v = raise Find
  | find_equiv (equiv::equivs) v =
   if (in_equivalence v equiv)
   then equiv
   else find_equiv equivs v;

(*--------------------------------------------------------------------------*)
(* trans_equivalence : equivalence -> thm                                   *)
(*                                                                          *)
(* Generates the equivalence theorem between the first and last vertices in *)
(* the equivalence class representation.                                    *)
(*--------------------------------------------------------------------------*)

fun trans_equivalence (Vertex (_,th)) = th
  | trans_equivalence (Equivalent (_,th,Vertex _)) = th
  | trans_equivalence (Equivalent (_,th,equiv)) =
   TRANS th (trans_equivalence equiv);

(*--------------------------------------------------------------------------*)
(* equal_to_first : int -> equivalence -> thm                               *)
(*                                                                          *)
(* Generates the equivalence theorem between the first vertex and a named   *)
(* vertex in the equivalence class representation.                          *)
(*--------------------------------------------------------------------------*)

fun equal_to_first v (Vertex ((i,_),th)) =
   if (i = v) then th else raise Find
  | equal_to_first v (Equivalent ((i,_),th,equiv)) =
   if (i = v)
   then REFL (lhs (concl th))
   else TRANS th (equal_to_first v equiv);

(*--------------------------------------------------------------------------*)
(* equal_to_last : int -> equivalence -> thm                                *)
(*                                                                          *)
(* Generates the equivalence theorem between a named vertex and the last    *)
(* vertex in the equivalence class representation.                          *)
(*--------------------------------------------------------------------------*)

fun equal_to_last v (Vertex ((i,_),th)) =
   if (i = v) then th else raise Find
  | equal_to_last v (Equivalent ((i,_),th,equiv)) =
   if (i = v)
   then TRANS th (trans_equivalence equiv)
   else equal_to_last v equiv;

(*--------------------------------------------------------------------------*)
(* equal_to : int * int -> equivalence -> thm                               *)
(*                                                                          *)
(* Generates the equivalence theorem between two named vertices in the      *)
(* equivalence class representation.                                        *)
(*--------------------------------------------------------------------------*)

fun equal_to (u,v) (equiv as Vertex ((i,_),_)) =
   if (i = u) then equal_to_first v equiv
   else if (i = v) then SYM (equal_to_first u equiv)
   else raise Find
  | equal_to (u,v) (equiv as Equivalent ((i,_),_,equiv')) =
   if (i = u) then equal_to_first v equiv
   else if (i = v) then SYM (equal_to_first u equiv)
   else equal_to (u,v) equiv';

(*--------------------------------------------------------------------------*)
(* append_equivalences : equivalence -> thm -> equivalence -> equivalence   *)
(*                                                                          *)
(* Combines two equivalence classes given a theorem that justifies the      *)
(* equivalence of the last vertex in the first class with the first vertex  *)
(* of the second class.                                                     *)
(*--------------------------------------------------------------------------*)

fun append_equivalences (Vertex (itm,_)) linkth equiv2 =
   Equivalent (itm,linkth,equiv2)
  | append_equivalences (Equivalent (itm,th,equiv1)) linkth equiv2 =
   Equivalent (itm,th,append_equivalences equiv1 linkth equiv2);

(*--------------------------------------------------------------------------*)
(* combine_equivalences :                                                   *)
(*    (int * int) * thm -> equivalence -> equivalence -> equivalence        *)
(*                                                                          *)
(* Combines two equivalence classes given a theorem that justifies the      *)
(* equivalence of a named vertex in the first class with a named vertex in  *)
(* the second class.                                                        *)
(*--------------------------------------------------------------------------*)

fun combine_equivalences ((u,v),th) uequiv vequiv =
   let val linkth = TRANS (SYM (equal_to_last u uequiv))
                          (TRANS th (SYM (equal_to_first v vequiv)))
   in  append_equivalences uequiv linkth vequiv
   end;

(*--------------------------------------------------------------------------*)
(* filter_equivalence : ((int * term) * thm -> bool) -> equivalence ->      *)
(*                      ((int * term) * term) list                          *)
(*                                                                          *)
(* Filters an equivalence by applying a predicate to each node. The result  *)
(* is a list of vertices each with its head term and the full term it       *)
(* represents.                                                              *)
(*--------------------------------------------------------------------------*)

fun filter_equivalence p (Vertex (itm,th)) =
   if (p (itm,th)) then [(itm,lhs (concl th))] else []
  | filter_equivalence p (Equivalent (itm,th,equiv)) =
   if (p (itm,th))
   then (itm,lhs (concl th)) :: filter_equivalence p equiv
   else filter_equivalence p equiv;

(*--------------------------------------------------------------------------*)
(* node_name : int -> equivalence -> term                                   *)
(*                                                                          *)
(* Computes the head term (a variable or a constant) of a vertex in an      *)
(* equivalence class.                                                       *)
(*--------------------------------------------------------------------------*)

exception NodeName;

fun node_name v (Vertex ((i,tm),_)) = if (v = i) then tm else raise NodeName
  | node_name v (Equivalent ((i,tm),_,equiv)) =
   if (v = i) then tm else node_name v equiv;

(*--------------------------------------------------------------------------*)
(* equivalents : equivalence -> int list                                    *)
(*                                                                          *)
(* Returns the labels of the vertices in an equivalence class.              *)
(*--------------------------------------------------------------------------*)

fun equivalents (Vertex ((i,_),_)) = [i]
  | equivalents (Equivalent ((i,_),_,equiv)) = i :: equivalents equiv;

(*--------------------------------------------------------------------------*)
(* class : equivalence -> int                                               *)
(*                                                                          *)
(* Returns the representative element of the equivalence class.             *)
(*--------------------------------------------------------------------------*)

fun class (Vertex ((i,_),_)) = i
  | class (Equivalent ((i,_),_,_)) = i;

(*==========================================================================*)
(* Generating a graph and an equivalence class from terms                   *)
(*==========================================================================*)

local

(*--------------------------------------------------------------------------*)
(* Discrimination nets (allowing in-place update)                           *)
(*                                                                          *)
(* A net is either a list of labels or a choice based on the head of a      *)
(* term. An association list binds a nested association list to each        *)
(* possible head. The nested association list binds a sub-net to each       *)
(* possible number of arguments to which the head can be applied. The       *)
(* sub-net behaves similarly for the first argument of the head. When all   *)
(* of its arguments and their subterms have been examined the nesting of    *)
(* nets continues for the second argument of the original head. Thus a      *)
(* nested sequence of nets corresponds to a left-to-right depth-first       *)
(* traversal of the term to be discriminated. When all the nodes of the     *)
(* term have been dealt with, the sub-net is a list of labels indexed by    *)
(* that term.                                                               *)
(*                                                                          *)
(* WARNING: This datatype and its associated functions are not designed for *)
(* use outside of the enclosing local declaration.                          *)
(*--------------------------------------------------------------------------*)

datatype 'a net = Labels of 'a list ref
                | Choice of (term * (int * 'a net) list ref) list ref;

(*--------------------------------------------------------------------------*)
(* add_to_net : 'a net -> term list * 'a -> unit                            *)
(*                                                                          *)
(* Updates the named net to index the first term in the list and each of    *)
(* its subterms. Any further terms in the list are also processed but not   *)
(* in the same way; the function should normally be called with a list      *)
(* containing exactly one term.                                             *)
(*--------------------------------------------------------------------------*)

exception Add_to_net;

(*---------------------------------------------------------------------------
 * New addition to get around value restriction -- kls.
 *---------------------------------------------------------------------------*)
fun mk_new_net [] = Labels (ref [])
  | mk_new_net  _ = Choice (ref []);

fun add_to_net (net as Labels labels) ([],label) =
   labels := label :: !labels
  | add_to_net (net as Choice head_alist) (tm::tms,label) =
   let val (f,args) = strip_comb tm
       val n = length args
       val tms' = args @ tms
   in  let val args_alist = assoc f (!head_alist)
       in  let val args_net = assoc n (!args_alist)
           in  add_to_net args_net (tms',label)
           end
           handle HOL_ERR _ =>
           let val new_net = mk_new_net tms'
           in  args_alist := (n,new_net) :: !args_alist;
               add_to_net new_net (tms',label)
           end
       end
       handle HOL_ERR _ =>
       let val new_net = mk_new_net tms'
       in  head_alist := (f,ref [(n,new_net)]) :: !head_alist;
           add_to_net new_net (tms',label)
       end
   end
  | add_to_net _ _ = raise Add_to_net;

(*--------------------------------------------------------------------------*)
(* labels_in_net : 'a net -> term list -> 'a list                           *)
(*                                                                          *)
(* Returns a list of the labels in a net that are associated with a         *)
(* specified term (the first element in the list of terms) without removing *)
(* duplicates. The function should normally be called with a list           *)
(* containing exactly one term.                                             *)
(*--------------------------------------------------------------------------*)

exception Labels_in_net;

fun labels_in_net (Labels labels) [] = !labels
  | labels_in_net (Choice head_alist) (tm::tms) =
   (let val (f,args) = strip_comb tm
        val tms' = args @ tms
        val args_alist = assoc f (!head_alist)
        val args_net = assoc (length args) (!args_alist)
    in  labels_in_net args_net tms'
    end
    handle HOL_ERR _ => raise Labels_in_net)
  | labels_in_net _ _ = raise Labels_in_net;

(*--------------------------------------------------------------------------*)
(* contents_of_net : 'a net -> 'a list list                                 *)
(*                                                                          *)
(* Returns a list of all the lists of labels in a net without removing      *)
(* duplicates from the sub-lists or the list itself.                        *)
(*--------------------------------------------------------------------------*)

fun contents_of_net (Labels labels) = [!labels]
  | contents_of_net (Choice head_alist) =
   flat (map (flat o map (contents_of_net o #2) o ! o #2) (!head_alist));

in

(*--------------------------------------------------------------------------*)
(* construct_congruence :                                                   *)
(*    (term -> term list) -> term list ->                                   *)
(*    graph * equivalence list * (term -> int) * (int * term) list          *)
(*                                                                          *)
(* Constructs a graph (with integers as vertex labels) plus a list of       *)
(* initial equivalence classes (one for each vertex) from a list of terms.  *)
(* The graph has a vertex for each term and each subterm of the terms. A    *)
(* function to compute the integer vertex label for any of the terms and    *)
(* subterms is also returned, as is a list of extra vertices in the graph.  *)
(* The extra vertices are given as both an integer vertex label and a term. *)
(* The extra vertices are generated by applying the first argument of       *)
(* `construct_congruence' to each of the given terms and their subterms.    *)
(*--------------------------------------------------------------------------*)

fun construct_congruence compute_extras tms =
   let val net = Choice (ref [])
       fun add_extra (n,extras) tm =
          (add_to_net net ([tm],(n,#1 (strip_comb tm),tm));
           (n + 1,(n,tm) :: extras))
       fun add_term (n,extras) tm =
          let val (f,args) = strip_comb tm
          in  add_to_net net ([tm],(n,f,tm));
              itlist (C add_term) args
                 (itlist (C add_extra) (compute_extras tm) (n + 1,extras))
          end
       val (n,extras) = itlist (C add_term) tms (1,[])
       fun label_for_term tm =
          (#1 o hd o labels_in_net net) [tm]
          handle _ => failwith "construct_congruence: label_for_term"
       fun label_and_term tm = (label_for_term tm,tm)
       fun adjacency_lists (label,tm) =
          let val (_,args) = strip_comb tm
              val labels_and_args = map label_and_term args
          in  (label,map #1 labels_and_args) ::
              flat (map adjacency_lists labels_and_args)
          end
       val adj_lists =
          flat (map (adjacency_lists o label_and_term) (map #2 extras @ tms))
       fun adj_lists_for_vertex v =
          case (remove_duplicates (op =)
                   (filter (fn (v',_) => v' = v) adj_lists))
          of [] => (v,[])
           | [vadjs] => vadjs
           | _ => failwith "adj_lists_for_vertex"
       val contents = map hd (contents_of_net net)
       val graph = Graph (map (adj_lists_for_vertex o #1) contents)
       val equivs = map (fn (n,f,tm) => Vertex ((n,f),REFL tm)) contents
   in  (graph,equivs,label_for_term,extras)
   end
   handle HOL_ERR _ => failwith "construct_congruence";

end;

(*==========================================================================*)
(* Congruence closure functions                                             *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* congruent : graph -> int * int -> equivalence list -> thm                *)
(*                                                                          *)
(* Given a graph and equivalence classes this function proves that the      *)
(* terms corresponding to two specified vertices are equal or it fails if   *)
(* they are not. The two terms will be shown to be equal if they have the   *)
(* same head term and the arguments of one are each in the same equivalence *)
(* class as the corresponding argument of the other.                        *)
(*--------------------------------------------------------------------------*)

exception Congruent;

fun congruent graph (u,v) equivs =
   let val uf = node_name u (find_equiv equivs u)
       and vf = node_name v (find_equiv equivs v)
       val usuccs = successors graph u
       and vsuccs = successors graph v
       val uequivs = map (find_equiv equivs) usuccs
       and vequivs = map (find_equiv equivs) vsuccs
   in  if (uf = vf) andalso (map class uequivs = map class vequivs)
       then let val succs = zip uequivs (zip usuccs vsuccs)
                val argths = map (fn (e,uv') => equal_to uv' e) succs
            in  rev_itlist (fn xth => fn fth => MK_COMB (fth,xth))
                   argths (REFL uf)
            end
       else raise Congruent
   end
   handle _ => raise Congruent;

(*--------------------------------------------------------------------------*)
(* merge :                                                                  *)
(*    graph -> (int * int) * thm -> equivalence list -> equivalence list    *)
(*                                                                          *)
(* Merges equivalence classes using an equality between two vertices. The   *)
(* merging is done recursively using congruence properties.                 *)
(*--------------------------------------------------------------------------*)

fun merge graph (uvth as ((u,v),_)) equivs =
   let val uequiv = find_equiv equivs u
       and vequiv = find_equiv equivs v
   in  if (class uequiv = class vequiv)
       then equivs
       else let val Pfun = remove_duplicates (op =) o flat o
                           map (predecessors graph) o equivalents
                val Pu = Pfun uequiv
                and Pv = Pfun vequiv
                val other_equivs =
                   filter (fn equiv => not ((in_equivalence u equiv) orelse
                                            (in_equivalence v equiv))) equivs
                val equivs' =
                   combine_equivalences uvth uequiv vequiv :: other_equivs
                val xs = zip Pu (map (class o find_equiv equivs') Pu)
                and ys = zip Pv (map (class o find_equiv equivs') Pv)
                val pairs = pairings (fn p => p) (xs,ys)
                val pairs' =
                   filter (fn ((_,classx),(_,classy)) => not (classx = classy))
                          pairs
                val xys = map (fn ((x,_),(y,_)) => (x,y)) pairs'
                val xyths =
                   mapfilter (fn xy => (xy,congruent graph xy equivs')) xys
            in  itlist (merge graph) xyths equivs'
            end
   end
   handle Find => equivs;

(*--------------------------------------------------------------------------*)
(* congruence_closure :                                                     *)
(*    graph * (term -> int) -> equivalence list -> thm list ->              *)
(*    equivalence list                                                      *)
(*                                                                          *)
(* Performs congruence closure on a list of equivalence classes using a     *)
(* list of equality theorems between terms in the classes. The underlying   *)
(* graph and the function to compute a graph vertex label for a term must   *)
(* also be supplied.                                                        *)
(*--------------------------------------------------------------------------*)

fun congruence_closure _ equivs [] = equivs
  | congruence_closure (graph,label_for_term) equivs (eqth::eqths) =
   let val eq = concl eqth
       val (lhs,rhs) = dest_eq eq
       val lhs_label = label_for_term lhs
       and rhs_label = label_for_term rhs
       val equivs' = merge graph ((lhs_label,rhs_label),eqth) equivs
   in  congruence_closure (graph,label_for_term) equivs' eqths
   end
   handle HOL_ERR _ => failwith "congruence_closure";

(*--------------------------------------------------------------------------*)
(* refute_diseq : equivalence list * (term -> int) -> thm -> thm            *)
(*                                                                          *)
(* Given a list of equivalence classes, the function to compute a graph     *)
(* vertex label for a term, and a theorem of the form C |- ~(l = r), this   *)
(* function attempts to prove C |- F, where C is a set of hypotheses and F  *)
(* is the constant `false'. It fails if l and r are not in the same         *)
(* equivalence class.                                                       *)
(*--------------------------------------------------------------------------*)

fun refute_diseq (equivs,label_for_term) diseqth =
   let val (l,r) = (dest_eq o dest_neg o concl) diseqth
       val llabel = label_for_term l
       and rlabel = label_for_term r
       val lequiv = find_equiv equivs llabel
       val requiv = find_equiv equivs rlabel
   in  if (class lequiv = class requiv)
       then let val eqth = equal_to (llabel,rlabel) lequiv
            in  X_AND_NOT_X_F_RULE (CONJ eqth diseqth)
            end
       else failwith ""
   end
   handle HOL_ERR _ => failwith "refute_diseq";

(*--------------------------------------------------------------------------*)
(* refute_diseqs : equivalence list * (term -> int) -> thm list -> thm      *)
(*                                                                          *)
(* Tries to use the equivalence classes and theorems of the form            *)
(* C |- ~(l = r) to derive C |- F. It stops looking at the theorems as soon *)
(* as it has derived C |- F. See also the documentation for `refute_diseq'. *)
(*--------------------------------------------------------------------------*)

fun refute_diseqs (equivs,label_for_term) [] = failwith "refute_diseqs"
  | refute_diseqs (equivs,label_for_term) (diseqth::diseqths) = 
   (refute_diseq (equivs,label_for_term) diseqth handle HOL_ERR _ =>
    refute_diseqs (equivs,label_for_term) diseqths);

(*--------------------------------------------------------------------------*)
(* CONGRUENCE_CONV : term -> thm                                            *)
(*                                                                          *)
(* A generic congruence closure procedure that does not assign a special    *)
(* meaning to any of the function symbols, i.e., it is a decision procedure *)
(* (actually a refutation procedure) for the theory of equality over        *)
(* uninterpreted function symbols. For a term t, it attempts to prove the   *)
(* theorem |- t = F. The term t must be a conjunction of literals where     *)
(* each literal is an equation or the negation of an equation between terms *)
(* built up by function application from constants and variables. Literals  *)
(* that are not equations or disequations are transformed into that form,   *)
(* i.e., x becomes (x = T) and ~x becomes ~(x = T).                         *)
(*--------------------------------------------------------------------------*)

fun CONGRUENCE_CONV tm =
   let val ths = CONJUNCTS (ASSUME tm)
       val posths = filter (not o is_neg o concl) ths
       and negths = filter (is_neg o concl) ths
       val eqths =
          map (fn th => if (is_eq o concl) th then th else EQT_INTRO th) posths
       val diseqths =
          map (fn th => if (is_eq o dest_neg o concl) th
                        then th
                        else NOT_EQT_INTRO th) negths
       val tms = itlist (fn eq => fn tms => lhs eq :: rhs eq :: tms)
                    (map concl eqths @ map (dest_neg o concl) diseqths) []
       val (graph,equivs,label_for_term,_) =
          construct_congruence (fn _ => []) tms
       val equivs' = congruence_closure (graph,label_for_term) equivs eqths
   in  IMP_F_EQ_F_RULE
          (DISCH tm (refute_diseqs (equivs',label_for_term) diseqths))
   end
   handle HOL_ERR _ => failwith "CONGRUENCE_CONV";

end;

end; (* CongruenceClosure *)
