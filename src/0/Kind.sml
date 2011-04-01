(* ===================================================================== *)
(* FILE          : Kind.sml                                              *)
(* DESCRIPTION   : HOL kinds (of types).                                 *)
(*                                                                       *)
(* AUTHOR        : (c) Peter Vincent Homeier                             *)
(* DATE          : September 10, 2007                                    *)
(* ===================================================================== *)

structure Kind :> Kind =
struct

(*
In *scratch*, type
(hol-set-executable sml-executable)
and type Ctrl-j.

loadPath := "/usr/local/hol/hol/sigobj" :: !loadPath;
loadPath := Globals.HOLDIR ^ "/src/0" :: !loadPath;
app load ["Feedback","Lib","KernelTypes","Lexis"];
*)

open Feedback Lib KernelTypes Rank;   infix |-> ## :=:;

type rank = KernelTypes.rank
type kind = KernelTypes.kind;

val ERR = mk_HOL_ERR "Kind";
val WARN = HOL_WARNING "Kind";


(*---------------------------------------------------------------------------
       The kind of HOL types
 ---------------------------------------------------------------------------*)

val rcheck = Rank.check "Kind"

fun typ r = Type (rcheck "typ" r)

fun mk_type_kind r = Type (rcheck "mk_type_kind" r)

fun dest_type_kind (Type rank) = rank
  | dest_type_kind _ = raise ERR "dest_type_kind" "not a type kind";

(*---------------------------------------------------------------------------
       Operator (arrow) kinds
 ---------------------------------------------------------------------------*)

infixr 3 ==>;   val op ==> = Oper;
infix 3 :=: :>=:;

fun kind_dom_rng (Oper(X,Y)) = (X,Y)
  | kind_dom_rng _ = raise ERR "kind_dom_rng" "not an operator kind";

fun ((Type r1) :=: (Type r2)) = true
  | ((KdVar (s1,r1)) :=: (KdVar (s2,r2))) = (s1 = s2) andalso (r1 = r2)
  | ((Oper (k1s,k1t)) :=: (Oper (k2s,k2t))) = (k1s :=: k2s) andalso (k1t :=: k2t)
  | (_ :=: _) = false;

(* Kind containment: kinds match, but ranks are same or lower than container *)
fun ((Type r1) :>=: (Type r2)) = ge_rk(r1,r2)
  | ((KdVar (s1,r1)) :>=: (KdVar (s2,r2))) = (s1 = s2) andalso (r1 = r2)
  | ((Oper (k1s,k1t)) :>=: (Oper (k2s,k2t))) = (k1s :>=: k2s) andalso (k1t :>=: k2t)
  | (_ :>=: _) = false;

fun mk_arity 0 = Type rho
  | mk_arity n = Type rho ==> mk_arity (n-1);

fun is_arity (Type 0) = true
  | is_arity (Oper(Type 0,Y)) = is_arity Y
  | is_arity _ = false;

fun arity_of (Type 0) = 0
  | arity_of (Oper(Type 0,Y)) = arity_of Y + 1
  | arity_of _ = raise ERR "arity_of" "not an arity kind";

fun list_mk_arrow_kind (X::XS,Y) = X ==> list_mk_arrow_kind(XS,Y)
  | list_mk_arrow_kind ( []  ,Y) = Y;

val dest_arrow_kind = kind_dom_rng;

fun strip_arrow_kind (Oper(X,Y)) = let val (args,res) = strip_arrow_kind Y
                                   in (X::args, res)
                                   end
  | strip_arrow_kind Z = ([],Z);


(*---------------------------------------------------------------------------
       Kind variables
 ---------------------------------------------------------------------------*)

val kappa = KdVar ("'k", rho)

val varkindcomplain = ref true
val _ = register_btrace ("Varkind Format Complaint", varkindcomplain)

local val chk = rcheck "mk_var_kind"
in
fun mk_var_kind ("'k", 0) = kappa
  | mk_var_kind (s,r) = if Lexis.allowed_user_type_var s then KdVar (s,chk r)
                        else (if !varkindcomplain then
                                WARN "mk_var_kind" "non-standard syntax"
                              else (); KdVar (s,chk r))
end

fun dest_var_kind (KdVar p) = p
  | dest_var_kind _ = raise ERR "dest_var_kind" "not a kind variable"


(*---------------------------------------------------------------------------
     Automatically generated kind variables. The unusual names make
     it unlikely that the names will clash with user-created
     kind variables.
 ---------------------------------------------------------------------------*)

local val gen_kdvar_prefix = "%%gen_kdvar%%"
      fun num2name i = gen_kdvar_prefix^Lib.int_to_string i
      val nameStrm   = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun gen_var_kind r = KdVar(state(next nameStrm), rcheck "gen_var_kind" r)

fun is_gen_kdvar (KdVar (name,_)) = String.isPrefix gen_kdvar_prefix name
  | is_gen_kdvar _ = false;
end;


(*---------------------------------------------------------------------------
                Discriminators
 ---------------------------------------------------------------------------*)

fun is_type_kind (Type  _) = true | is_type_kind _ = false;
fun is_var_kind  (KdVar _) = true | is_var_kind _ = false;
fun is_arrow_kind (Oper _) = true | is_arrow_kind _ = false;


(* ----------------------------------------------------------------------
    A total ordering on kinds.
    Type < KdVar < Oper
   ---------------------------------------------------------------------- *)

fun kind_compare (Type r1,  Type r2)  = rank_compare(r1,r2)
  | kind_compare (Type _,   _)        = LESS
  | kind_compare (KdVar _,  Type _)   = GREATER
  | kind_compare (KdVar p1, KdVar p2) = Lib.pair_compare(String.compare,rank_compare)(p1,p2)
  | kind_compare (KdVar _,  _)        = LESS
  | kind_compare (Oper p1,  Oper p2)  = Lib.pair_compare(kind_compare,kind_compare)(p1,p2)
  | kind_compare (Oper _,   _)        = GREATER;


(* ----------------------------------------------------------------------
    A total ordering on kinds that does not distinguish ranks of Type's.
    Type < KdVar < Oper
   ---------------------------------------------------------------------- *)

fun tycon_kind_compare (Type r1,  Type r2)  = EQUAL
  | tycon_kind_compare (Type _,   _)        = LESS
  | tycon_kind_compare (KdVar _,  Type _)   = GREATER
  | tycon_kind_compare (KdVar p1, KdVar p2) = Lib.pair_compare(String.compare,rank_compare)(p1,p2)
  | tycon_kind_compare (KdVar _,  _)        = LESS
  | tycon_kind_compare (Oper p1,  Oper p2)  = Lib.pair_compare(tycon_kind_compare,tycon_kind_compare)(p1,p2)
  | tycon_kind_compare (Oper _,   _)        = GREATER;


(*----------------------------------------------------------------------*
 * The kind variables in a kind.  Tail recursive (from Ken Larsen).     *
 *----------------------------------------------------------------------*)

local fun KV (v as KdVar _) A k   = k (Lib.insert v A)
        | KV (Oper(kd1, kd2)) A k = KV kd1 A (fn q => KV kd2 q k)
        | KV _ A k = k A
      and KVl (kd::kds) A k       = KV kd A (fn q => KVl kds q k)
        | KVl _ A k = k A
in
fun kind_vars kd = rev(KV kd [] Lib.I)
fun kind_varsl L = rev(KVl L [] Lib.I)
end;


(*---------------------------------------------------------------------------
    Does there exist a kind variable v in a kind such that P(v) holds.
    Returns false if there are no kind variables in the kind.
 ---------------------------------------------------------------------------*)

fun exists_kdvar P =
 let fun occ (Type _) = false
       | occ (w as KdVar _) = P w
       | occ (Oper(kd1,kd2)) = occ kd1 orelse occ kd2
 in occ end;
                         
(*---------------------------------------------------------------------------
     Does a kind variable occur in a kind
 ---------------------------------------------------------------------------*)

fun kind_var_in v = 
  if is_var_kind v then exists_kdvar (equal v)
                   else raise ERR "kind_var_occurs" "not a kind variable"


(*---------------------------------------------------------------------------*
 * Computing the rank of a kind.                                             *
 *---------------------------------------------------------------------------*)

fun rank_of (Type rk)       = rk
  | rank_of (KdVar(_,rk))   = rk
  | rank_of (Oper(dom,rng)) = max (rank_of dom, rank_of rng);

(*---------------------------------------------------------------------------*
 * Is a kind polymorphic, or contain a non-zero rank?                        *
 *---------------------------------------------------------------------------*)

fun polymorphic (Type rk)       = (rk > 0)
  | polymorphic (KdVar _)       = true
  | polymorphic (Oper(dom,rng)) = polymorphic dom orelse polymorphic rng


(*---------------------------------------------------------------------------*
 * Increasing the rank of a kind. (Promotion)                                *
 *---------------------------------------------------------------------------*)

local val chk = rcheck "inst_rank"
in
fun inst_rank 0 = I
  | inst_rank rkS =
  let val promote = promote rkS
      fun inc_rk (Type rk)        = Type (promote rk)
        | inc_rk (KdVar(s,rk))    = KdVar(s,promote rk)
        | inc_rk (Oper (dom,rng)) = Oper (inc_rk dom, inc_rk rng)
  in inc_rk
  end
  handle HOL_ERR{message=m,...} => raise ERR "inst_rank" m
end;

fun raw_subst_rank rkS =
  let fun chk rk = (rcheck "raw_subst_rank" rk; rk)
      fun subst_rank0 [] = chk rkS
        | subst_rank0 ({redex,residue} :: s) =
            raw_match_rank false (rank_of redex) (rank_of residue) (subst_rank0 s)
  in subst_rank0
  end

val subst_rank = raw_subst_rank 0

fun inst_rank_subst rkS =
  let val inst = inst_rank rkS
      fun inst_rank_subst0 [] = []
        | inst_rank_subst0 ({redex,residue} :: s) =
            ({redex=inst redex, residue=residue} :: inst_rank_subst0 s)
  in inst_rank_subst0
  end
  handle HOL_ERR{message=m,...} => raise ERR "inst_rank_subst" m

fun align_kinds theta = let
        val rkS = subst_rank theta
        val inst = inst_rank rkS
        fun inst_redex [] = []
          | inst_redex ({redex,residue} :: s) = let
                val redex' = inst redex
              in
                if redex' = residue then inst_redex s
                else (redex' |-> residue) :: inst_redex s
              end
      in
        (rkS, if rkS=0 then theta else inst_redex theta)
      end
      handle HOL_ERR{message=m,...} => raise ERR "align_kinds" m

(*---------------------------------------------------------------------------*
 * Substitute in a kind, trying to preserve existing structure.              *
 *---------------------------------------------------------------------------*)

fun kd_sub [] _ = SAME
  | kd_sub theta (Type _) = SAME
  | kd_sub theta (Oper(kd1,kd2))
      = (case delta_map (kd_sub theta) [kd1,kd2]
          of SAME => SAME
           | DIFF [kd1',kd2'] => DIFF (Oper(kd1', kd2'))
           | DIFF _ => raise ERR "kd_sub" "can't happen")
  | kd_sub theta v =
      case Lib.subst_assoc (equal v) theta
       of NONE    => SAME
        | SOME kd => DIFF kd

fun kd_sub1 theta kd =
  case Lib.subst_assoc (equal kd) theta
   of SOME kd' => if kd'=kd then SAME else DIFF kd'
    | NONE     => (case kd
                    of Oper(kd1,kd2) =>
                         (case delta_map (kd_sub1 theta) [kd1,kd2]
                           of SAME => SAME
                            | DIFF [kd1',kd2'] => DIFF (Oper(kd1',kd2'))
                            | DIFF _ => raise ERR "kd_sub1" "can't happen")
                     | _ => SAME)

fun kind_subst theta =
    if null theta then I
    else
    let val (rk,theta') = align_kinds theta
    in if rk = 0 then
         if List.all (is_var_kind o #redex) theta
         then delta_apply (kd_sub theta)
         else delta_apply (kd_sub1 theta)
       else
         if List.all (is_var_kind o #redex) theta'
         then delta_apply (kd_sub theta') o inst_rank rk
         else delta_apply (kd_sub1 theta') o inst_rank rk
    end

val emptysubst:(kind,kind)Binarymap.dict = Binarymap.mkDict kind_compare
local
  open Binarymap
  fun add [] A = A
    | add ({redex,residue}::t) A =
        if not (ge_rk (rank_of redex, rank_of residue))
        then raise ERR "pure_inst_kind" "rank of residue is not contained in rank of redex"
        else add t (insert(A,redex,residue))
in
fun pure_inst_kind []    = Lib.I
  | pure_inst_kind theta =
  let val fmap = add theta emptysubst
      fun inst (k as Type _)    = k
        | inst (Oper(kd1, kd2)) = Oper(inst kd1, inst kd2)
        | inst (v as KdVar _)   = case peek(fmap,v) of NONE => v | SOME y => y
  in inst
  end

(* fun inst_rank_kind rank theta = kind_subst theta o inst_rank rank *)

fun inst_rank_kind 0  []    = Lib.I
  | inst_rank_kind rk []    = (inst_rank rk
                                handle HOL_ERR{message=m,...} => raise ERR "inst_rank_kind" m)
  | inst_rank_kind 0  theta = (pure_inst_kind theta
                                handle HOL_ERR{message=m,...} => raise ERR "inst_rank_kind" m)
  | inst_rank_kind rank theta =
  let val rk_inst = Rank.promote rank
      val fmap = add theta emptysubst
      fun inst (Type rk)        = Type (rk_inst rk)
        | inst (Oper(kd1, kd2)) = Oper(inst kd1, inst kd2)
        | inst (KdVar(s,rk))    = let val v = KdVar(s,rk_inst rk) in
                                    case peek(fmap,v)
                                    (*case subst_assoc (equal v) theta*)
                                     of SOME y => y
                                      | NONE => v
                                  end
  in inst
  end
  handle HOL_ERR{message=m,...} => raise ERR "inst_rank_kind" m
end; (* local *)

(* inst_kind aligns the ranks of its substitution *)
fun inst_kind theta =
  let val (rktheta,kdtheta) = align_kinds theta
  in inst_rank_kind rktheta kdtheta
  end
  handle e as HOL_ERR _ => raise (wrap_exn "Kind" "inst_kind" e)

(*---------------------------------------------------------------------------
         This matching algorithm keeps track of identity bindings
         v |-> v in a separate area. This eliminates the need for
         post-match normalization of substitutions coming from the
         matching algorithm.
 ---------------------------------------------------------------------------*)
  
local
  fun MERR s = raise ERR "raw_match_kind" s
  fun lookup x ids =
   let fun look [] = if Lib.mem x ids then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
in   
fun kdmatch _ [] [] rSids = rSids
  | kdmatch incty (Type r1::ps) (Type r2::obs) ((rkS,rkfixed),Sids) =
     kdmatch incty ps obs ((if incty then rkS else raw_match_rank rkfixed r1 r2 rkS,rkfixed),Sids)
  | kdmatch incty ((v as KdVar(name,rk))::ps) (kd::obs) (rSids as ((rkS,rkfixed),Sids as (S,ids))) =
     kdmatch incty ps obs
       (case lookup v ids S
         of NONE => if v=kd then ((raw_match_rank rkfixed rk rk rkS,rkfixed),(S,v::ids))
                    else ((raw_match_rank rkfixed rk (rank_of kd) rkS,rkfixed),
                          ((v |-> kd)::S,ids))
          | SOME kd1 => if kd1=kd then rSids else
                        MERR ("double bind on kind variable "^name))
  | kdmatch incty (Oper(p1,p2)::ps) (Oper(obs1,obs2)::obs) rSids =
      kdmatch incty (p1::p2::ps) (obs1::obs2::obs) rSids
  | kdmatch _ any other thing = MERR "different kind constructors"
end

fun norm_subst (rk as (rkS,rkfixed),(kdS,kdI)) =
 let val Theta = inst_rank rkS
     val mapTheta = case rkS of
                      0 => I
                    | _ => map Theta
     fun del A [] = A
       | del (kdS,kdI) ({redex,residue}::rst) =
         del (let val redex' = Theta(redex)
              in if residue = redex' then (kdS,redex'::kdI)
                                     else ((redex' |-> residue)::kdS,kdI)
              end) rst
 in (rk, del ([],mapTheta kdI) kdS)
 end

fun prim_match_kind inconty pat ob rSids = kdmatch inconty [pat] [ob] rSids

val raw_match_kind = prim_match_kind false

fun match_kind_restr rkfixed fixed pat ob =
    let val ((rkS,rkfixed),(kdS,ids)) = norm_subst (raw_match_kind pat ob ((0,rkfixed),([],fixed)))
    in (rkS,kdS)
    end
fun match_kind_in_context pat ob (rk,S) =
    let val ((rkS,rkfixed),(kdS,ids)) = norm_subst (raw_match_kind pat ob ((rk,false),(S,[])))
    in (rkS,kdS)
    end

fun match_kind pat ob = match_kind_in_context pat ob (0,[])

fun match_kinds theta =
 let fun match ({redex,residue},matches) = raw_match_kind redex residue matches
     val ((rkS,rkfixed),(kdS,ids)) = norm_subst (List.foldr match ((0,false),([],[])) theta)
 in (rkS,kdS)
 end


fun size acc kdlist =
    case kdlist of
      [] => acc
    | [] :: kds => size acc kds
    | (kd::kds1) :: kds2 => let
      in
        case kd of
          Oper(opr, arg) => size acc ((opr :: arg :: kds1) :: kds2)
        | _              => size (1 + acc) (kds1 :: kds2)
      end

fun kind_size kd = size 0 [[kd]]


(*---------------------------------------------------------------------------*
 *  Syntax prettyprinters for kinds.                                         *
 *                                                                           *
 * The following prettyprinter prints kinds which are arities as "ar <n>".   *
 * If possible, the simplest kind (Type) is printed as "ty"; kind variables  *
 * are printed as their name (normally beginning with '); else as an arity.  *
 * Otherwise, kinds which are not arities are printed using the infix "=>".  *
 * "=>" associates to the right, else, parentheses are printed as needed.    *
 *---------------------------------------------------------------------------*)

fun pp_kind pps kd =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     fun pp1 paren (Type rk) = if rk=rho then add_string "ty"
                                       else add_string ("ty:"^rank_to_string rk)
       | pp1 paren (KdVar(s,rk)) = if rk=rho then add_string s
                                       else add_string (s^":"^rank_to_string rk)
       | pp1 paren (Oper(Rator,Rand)) =
          ( if paren then (add_string "("; begin_block INCONSISTENT 0) else ();
            pp true Rator; add_string " =>"; add_break(1,0); pp false Rand;
            if paren then (end_block(); add_string ")") else () )
     and pp paren (Type rk) = if rk=rho then add_string "ty"
                                       else add_string ("ty:"^rank_to_string rk)
       | pp paren (KdVar(s,rk)) = if rk=rho then add_string s
                                       else add_string (s^":"^rank_to_string rk)
       | pp paren kd = add_string ("ar " ^ Lib.int_to_string (arity_of kd))
                       handle HOL_ERR _ => pp1 paren kd
 in
   begin_block INCONSISTENT 0;
   pp false kd;
   end_block()
 end;

fun pp_qkind pps kd =
 let open Portable Globals
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_kind = pp_kind pps
 in
   begin_block INCONSISTENT 0;
   add_string (!kind_pp_prefix);
   add_string "::";
   pp_kind kd;
   add_string (!kind_pp_suffix);
   end_block()
 end;

(*---------------------------------------------------------------------------*)
(* Send the results of prettyprinting to a string                            *)
(*---------------------------------------------------------------------------*)

fun sprint pp x = HOLPP.pp_to_string 72 pp x

val kind_to_string = sprint pp_kind;

(*
val _ = installPP pp_kind;
*)


end (* Kind *)
