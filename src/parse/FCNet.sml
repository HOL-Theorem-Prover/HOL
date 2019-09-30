structure FCNet :> FCNet =
struct

open Lib HolKernel
type term = Term.term

val ERR = Feedback.mk_HOL_ERR "FCNet";

(*---------------------------------------------------------------------------*
 *   Tags corresponding to the underlying term constructors.                 *
 *---------------------------------------------------------------------------*)

datatype label
    = V
    | Cmb
    | Lam
    | Cnst of string * string ;  (* name * segment *)

(*---------------------------------------------------------------------------*
 *    Term nets.                                                             *
 *---------------------------------------------------------------------------*)

datatype 'a t
    = LEAF of (term * 'a) list
    | NODE of (label * 'a t) list;


val empty = NODE [];

fun is_empty (NODE[]) = true
  | is_empty    _     = false;

(*---------------------------------------------------------------------------*
 * Determining the top constructor of a term.                                *
 *---------------------------------------------------------------------------*)

local
  open Term GrammarSpecials HolKernel
in
fun label_of tm =
  case dest_term tm of
      LAMB _ => Lam
    | VAR (s, _) =>
      let
      in
        case dest_fakeconst_name s of
            SOME {original = SOME kid, ...} => Cnst (#Name kid, #Thy kid)
          | _ => V
      end
    | CONST{Name,Thy,...} => Cnst(Name,Thy)
    | _ => Cmb
end

fun net_assoc label =
 let fun get (LEAF _) = raise ERR "net_assoc" "LEAF: no children"
       | get (NODE subnets) =
            case Lib.assoc1 label subnets
             of NONE => empty
              | SOME (_,net) => net
 in get
 end;


local
  fun mtch tm (NODE []) = []
    | mtch tm net =
       let val label = label_of tm
           val Vnet = net_assoc V net
           val nets =
            case label
             of V => []
              | Cnst _ => [net_assoc label net]
              | Lam    => mtch (Term.body tm) (net_assoc Lam net)
              | Cmb    => let val (Rator,Rand) = Term.dest_comb tm
                          in itlist(append o mtch Rand)
                                   (mtch Rator (net_assoc Cmb net)) []
                           end
       in itlist (fn NODE [] => I | net => cons net) nets [Vnet]
       end
in
fun match tm net =
  if is_empty net then []
  else
    itlist (fn LEAF L => append (map #2 L) | _ => fn y => y)
           (mtch tm net) []
end;

(*---------------------------------------------------------------------------
        Finding the elements mapped by a term in a term net.
 ---------------------------------------------------------------------------*)

fun index x net = let
  fun appl  _   _  (LEAF L) = SOME L
    | appl defd tm (NODE L) =
      let val label = label_of tm
      in case assoc1 label L
          of NONE => NONE
           | SOME (_,net) =>
              case label
               of Lam => appl defd (Term.body tm) net
                | Cmb => let val (Rator,Rand) = Term.dest_comb tm
                         in appl (Rand::defd) Rator net end
                |  _  => let fun exec_defd [] (NODE _) = raise ERR "appl"
                                  "NODE: should be at a LEAF instead"
                               | exec_defd [] (LEAF L) = SOME L
                               | exec_defd (h::rst) net =  appl rst h net
                         in
                           exec_defd defd net
                         end
      end
in
  case appl [] x net
   of SOME L => map #2 L
    | NONE   => []
end;

(*---------------------------------------------------------------------------*
 *        Adding to a term net.                                              *
 *---------------------------------------------------------------------------*)

fun overwrite (p as (a,_)) =
  let fun over [] = [p]
        | over ((q as (x,_))::rst) =
            if (a=x) then p::rst else q::over rst
  in over
  end;

fun insert (p as (tm,_)) N =
let fun enter _ _  (LEAF _) = raise ERR "insert" "LEAF: cannot insert"
   | enter defd tm (NODE subnets) =
      let val label = label_of tm
          val child =
             case assoc1 label subnets of NONE => empty | SOME (_,net) => net
          val new_child =
            case label
             of Cmb => let val (Rator,Rand) = Term.dest_comb tm
                       in enter (Rand::defd) Rator child end
              | Lam => enter defd (Term.body tm) child
              | _   => let fun exec [] (LEAF L)  = LEAF(p::L)
                             | exec [] (NODE _)  = LEAF[p]
                             | exec (h::rst) net = enter rst h net
                       in
                          exec defd child
                       end
      in
         NODE (overwrite (label,new_child) subnets)
      end
in enter [] tm N
end;


(*---------------------------------------------------------------------------
     Removing an element from a term net. It is not an error if the
     element is not there.
 ---------------------------------------------------------------------------*)

fun split_assoc P =
 let fun split front [] = raise ERR "split_assoc" "not found"
       | split front (h::t) =
          if P h then (rev front,h,t) else split (h::front) t
 in
    split []
 end;


fun delete (tm,P) N =
let fun del [] = []
      | del ((p as (x,q))::rst) =
          if Term.aconv x tm andalso P q then del rst else p::del rst
 fun remv  _   _ (LEAF L) = LEAF(del L)
   | remv defd tm (NODE L) =
     let val label = label_of tm
         fun pred (x,_) = (x=label)
         val (left,(_,childnet),right) = split_assoc pred L
         val childnet' =
           case label
            of Lam => remv defd (Term.body tm) childnet
             | Cmb => let val (Rator,Rand) = Term.dest_comb tm
                      in remv (Rand::defd) Rator childnet end
             |  _  => let fun exec_defd [] (NODE _) = raise ERR "remv"
                                "NODE: should be at a LEAF instead"
                            | exec_defd [] (LEAF L) = LEAF(del L)
                            | exec_defd (h::rst) net =  remv rst h net
                      in
                        exec_defd defd childnet
                      end
         val childnetl =
           case childnet' of NODE [] => [] | LEAF [] => [] | y => [(label,y)]
     in
       NODE (List.concat [left,childnetl,right])
     end
in
  remv [] tm N handle Feedback.HOL_ERR _ => N
end;

fun filter P =
 let fun filt (LEAF L) = LEAF(List.filter (fn (x,y) => P y) L)
       | filt (NODE L) =
          NODE (itlist  (fn (l,n) => fn list =>
                 case filt n
                  of LEAF [] => list
                   | NODE [] => list
                   |   n'    => (l,n')::list) L [])
 in
    filt
 end;

fun listItems0 (LEAF L) = L
  | listItems0 (NODE L) = rev_itlist (append o listItems0 o #2) L [];

fun union net1 net2 = rev_itlist insert (listItems0 net1) net2;

fun listItems net = map #2 (listItems0 net);

fun map f (LEAF L) = LEAF (List.map (fn (x,y) => (x, f y)) L)
  | map f (NODE L) = NODE (List.map (fn (l,net) => (l,map f net)) L);

fun itnet f (LEAF L) b = itlist f (List.map #2 L) b
  | itnet f (NODE L) b = itlist (itnet f) (List.map #2 L) b;

fun size net = itnet (fn x => fn y => y+1) net 0;


(*---------------------------------------------------------------------------
                Compatibility mode.
 ---------------------------------------------------------------------------*)

fun get_tip_list (LEAF L) = L
  | get_tip_list (NODE _) = [];

fun get_edge label =
   let fun get (NODE edges) =
              (case Lib.assoc1 label edges
                 of SOME (_,net) => net
                  | NONE => empty)
         | get (LEAF _) = raise ERR "get_edge" "tips have no edges"
   in get
   end;

fun net_update elem =
let fun update _ _ (LEAF _) = raise ERR "net_update" "cannot update a tip"
      | update defd tm (net as (NODE edges)) =
           let fun exec_defd [] net = LEAF (elem::get_tip_list net)
                 | exec_defd (h::rst) net = update rst h net
               val label = label_of tm
               val child = get_edge label net
               val new_child =
                 case label
                   of Cmb => let val (Rator,Rand) = Term.dest_comb tm
                             in update (Rator::defd) Rand child
                             end
                    | Lam => update defd (Term.body tm) child
                    | _   => exec_defd defd child
           in NODE (overwrite (label,new_child) edges)
           end
in  update
end;

fun enter (tm,elem) net = net_update (tm,elem) [] tm net;

fun follow tm net =
 let val nets =
       case (label_of tm)
       of (label as Cnst _) => [get_edge label net]
        | V   => []
        | Lam => follow (Term.body tm) (get_edge Lam net)
        | Cmb => let val (Rator,Rand) = Term.dest_comb tm
                 in Lib.itlist(fn i => fn A => (follow Rator i @ A))
                              (follow Rand (get_edge Cmb net)) []
                 end
 in List.filter (not o is_empty) (get_edge V net::nets)
 end;

fun lookup tm net =
 if is_empty net then []
 else
   itlist (fn (LEAF L) => (fn A => (List.map #2 L @ A)) | (NODE _) => I)
          (follow tm net)  [];

(* term match *)
structure Map = Binarymap
fun bvar_free (bvmap, tm) = let
  (* return true if none of the free variables occur as keys in bvmap *)
  fun recurse bs t =
      case dest_term t of
        v as VAR _ => HOLset.member(bs, t) orelse
                      not (isSome (Map.peek(bvmap, t)))
      | CONST _ => true
      | COMB(f,x) => recurse bs f andalso recurse bs x
      | LAMB(v, body) => recurse (HOLset.add(bs, v)) body
in
  Map.numItems bvmap = 0 orelse recurse empty_varset tm
end

type tminfo = {ids : term HOLset.set, n : int,
               patbvars : (term,int)Map.dict,
               obbvars :  (term,int)Map.dict,
               theta : (term,term) Lib.subst}

datatype tmpair = TMP of term * term
                | BVrestore of {patbvars : (term,int)Map.dict,
                                obbvars : (term,int)Map.dict,
                                n : int}
fun add_id v {ids, patbvars, obbvars, theta, n} =
    {ids = HOLset.add(ids, v), patbvars = patbvars, obbvars = obbvars, n = n,
     theta = theta}
fun add_binding v tm {ids, patbvars, obbvars, theta, n} =
    {ids = ids, patbvars = patbvars, obbvars = obbvars, n = n,
     theta = (v |-> tm) :: theta}

fun MERR s = raise ERR "can_match_term" s

fun mlookup x ids = let
  fun look [] = if HOLset.member(ids, x) then SOME x else NONE
    | look ({redex,residue}::t) = if aconv x redex then SOME residue else look t
in
  look
end

fun RM patobs (theta0 as (tminfo, tyS)) =
    case patobs of
      [] => true
    | TMP (t1,t2)::rest => let
      in
        case (dest_term t1, dest_term t2) of
          (VAR(_, ty), _) => let
          in
            case Map.peek(#patbvars tminfo, t1) of
              NONE => (* var on left not bound *) let
              in
                if bvar_free (#obbvars tminfo, t2) then
                  (* TODO: aconv below should be "aconv wrt fake-consts" *)
                  RM rest ((case mlookup t1 (#ids tminfo) (#theta tminfo) of
                              NONE => if aconv t1 t2 then add_id t1 tminfo
                                      else add_binding t1 t2 tminfo
                            | SOME tm' => if aconv tm' t2 then tminfo
                                          else MERR "double bind"),
                           Type.raw_match_type ty (type_of t2) tyS)
                else
                  MERR "Attempt to capture bound variable"
              end
            | SOME i => if is_var t2 andalso
                           Map.peek(#obbvars tminfo, t2) = SOME i
                        then
                          RM rest theta0
                        else false
          end
        | (CONST{Name=n1,Thy=thy1,Ty=ty1}, CONST{Name=n2,Thy=thy2,Ty=ty2}) =>
          if n1 <> n2 orelse thy1 <> thy2 then false
          else RM rest (tminfo, Type.raw_match_type ty1 ty2 tyS)
        | (CONST{Name,Thy,Ty}, VAR(vnm, vty)) =>
          let
          in
            case GrammarSpecials.dest_fakeconst_name vnm of
                SOME {original = SOME {Name=vnm,Thy=vthy}, ...} =>
                if vnm = Name andalso vthy = Thy then
                  RM rest (tminfo, Type.raw_match_type Ty vty tyS)
                else false
              | _ => false
          end
        | (COMB(f1, x1), COMB(f2, x2)) =>
          RM (TMP (f1, f2) :: TMP (x1, x2) :: rest) theta0
        | (LAMB(x1, bdy1), LAMB(x2, bdy2)) => let
            val tyS' = Type.raw_match_type (type_of x1) (type_of x2) tyS
            val {ids, patbvars, obbvars, n, theta} = tminfo
          in
            RM (TMP (bdy1, bdy2) ::
                BVrestore {patbvars = patbvars, obbvars = obbvars, n = n} ::
                rest)
               ({ids = #ids tminfo, n = n + 1, theta = theta,
                 patbvars = Map.insert(patbvars, x1, n),
                 obbvars = Map.insert(obbvars, x2, n)}, tyS')
          end
        | _ => false
      end
    | BVrestore{patbvars, obbvars, n} :: rest => let
        val {ids, theta, ...} = tminfo
      in
        RM rest ({ids = ids, theta = theta, patbvars = patbvars,
                  obbvars = obbvars, n = n}, tyS)
      end

val empty_subst = Map.mkDict Term.compare
fun can_match_term pat t =
  RM [TMP (pat,t)] ({ids = empty_tmset, n = 0, theta = [],
                     patbvars = empty_subst, obbvars = empty_subst},
                    ([], [])) handle HOL_ERR _ => false

end (* Net *)
