
(* various operations on terms of type mu, as well as on the ML datatype for mu formulas that is used by the checker *)

structure muSyntax =
struct

local

open Globals HolKernel Parse goalstackLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open Psyntax;

open bossLib;
open pairTheory;
open pred_setTheory;
open pred_setLib;
open stringLib;
open listTheory;
open simpLib;
open pairSyntax;
open pairLib;
open PrimitiveBddRules;
open DerivedBddRules;
open Binarymap;
open PairRules;
open pairTools;
open setLemmasTheory;
open muSyntaxTheory;
open muTheory;
open boolSyntax;
open Drule;
open Tactical;
open Conv;
open Rewrite;
open Tactic;
open boolTheory;
open listSyntax;
open stringTheory;
open stringBinTree;
open boolSimps;
open pureSimps;
open listSimps;
open numLib;
open holCheckTools
open ksTools

in

datatype 'a mu =  muTR of 'a (* the type var is for annotating nodes with whatever e.g. pointers into thm cache *)
        | muFL of 'a
        | muNot of 'a * ('a mu)
        | muAnd of 'a * (('a mu) * ('a mu))
        | muOr of 'a * (('a mu) * ('a mu))
        | muRV of 'a (* relational var *)
        | muAP of 'a (* atomic proposition *)
        | muDIAMOND of 'a * (string * ('a mu)) (* diamond *)
        | muBOX of 'a * (string *  ('a mu)) (* box *)
        | fpmu of 'a * 'a *  ('a mu)   (* lfp *)
        | fpnu of 'a * 'a * ('a mu); (* mfp *)

(* return all top level sigma formulas in f (if nu then return nu formulas, else return mu formulas) *)
fun top_sigma nu f =  
    let val (opr,args) = strip_comb f
    in case (fst(dest_const opr)) of
           "TR" => []
         | "FL"  => []
         | "Not" =>  top_sigma nu (List.hd args)
         | "And" => (top_sigma nu  (List.hd args))@ (top_sigma nu  (List.last args))
         | "Or" => (top_sigma nu  (List.hd args))@(top_sigma nu  (List.last args))
         | "RV" => []
         | "AP" => []
         | "DIAMOND" => top_sigma nu  (List.last args)
         | "BOX" => top_sigma nu  (List.last args)
         | "mu" => if (not nu) then [f] else []
         | "nu" => if nu then [f] else []
         | _         => (print "ERROR:"; print_term f; print "\n"; Raise Match) end

(* is f purely propositional *)
fun is_prop f =
    let val (opr,args) = strip_comb f
    in case (fst(dest_const opr)) of
           "TR" => true
         | "FL"  => true
         | "Not" => is_prop (List.hd args)
         | "And" => (is_prop (List.hd args)) andalso (is_prop (List.last args))
         | "Or" => (is_prop (List.hd args)) andalso (is_prop (List.last args))
         | "RV" => false
         | "AP" => true
         | "DIAMOND" => false
         | "BOX" => false
         | "mu" => false
         | "nu" => false
         | _         => (print "ERROR:"; print_term f; print "\n"; Raise Match) end

(* return list of top-level propositional subterms of f with their sizes (this may include f itself) *)
fun prop_subtms f =
    let val (opr,args) = strip_comb f
    in case (fst(dest_const opr)) of
           "TR" => [(f,1)]
         | "FL"  => [(f,1)]
         | "Not" => let val t = List.hd args
                        val S1 = prop_subtms t
                    in if ((not (List.null S1)) andalso (Portable.pointer_eq(fst(hd S1),t)))
                       then [(f,(snd(hd S1))+1)] else S1 end
         | "And" => let val t1 = List.hd args
                        val t2 = List.last args
                        val S1 = prop_subtms t1
                        val S2 = prop_subtms t2
                    in if (((not (List.null S1)) andalso (Portable.pointer_eq(fst(hd S1),t1)))
                           andalso ((not (List.null S2)) andalso (Portable.pointer_eq(fst(hd S2),t2))))
                       then [(f,(snd(hd S1))+(snd(hd S2))+1)] else S1@S2 end
         | "Or" => let val t1 = List.hd args
                        val t2 = List.last args
                        val S1 = prop_subtms t1
                        val S2 = prop_subtms t2
                    in if (((not (List.null S1)) andalso (Portable.pointer_eq(fst(hd S1),t1)))
                           andalso ((not (List.null S2)) andalso (Portable.pointer_eq(fst(hd S2),t2))))
                       then [(f,(snd(hd S1))+(snd(hd S2))+1)] else S1@S2 end
         | "RV" => []
         | "AP" => [(f,1)]
         | "DIAMOND" =>  prop_subtms (List.last args)
         | "BOX" =>  prop_subtms (List.last args)
         | "mu" => prop_subtms (List.last args)
         | "nu" => prop_subtms (List.last args)
         | _  => (print "ERROR:"; print_term f; print "\n"; Raise Match) end

(* return list of subterms of f with size >= n, with duplicates removed, in decreasing order of size *)
fun prop_subtmset f n = List.rev(fst(ListPair.unzip(Listsort.sort (fn((_,l),(_,r))=>Int.compare(l,r))
                                      (Binaryset.listItems(Binaryset.addList(Binaryset.empty
                                         (fn ((l,_),(r,_)) => Term.compare(l,r)),
                                          (List.filter (fn (t,sz)=> (sz>=n)) (prop_subtms f))))))));


(* RVNEG(f,Q) == in f, all free ocurrances of Q are negated *)
fun RVNEG ty rv f = 
   let val (opr,args) = strip_comb f
    in case (fst(dest_const opr)) of
           "TR" => f
         | "FL"  => f
         | "Not" => ``~ ^(RVNEG ty rv (List.hd args))``
         | "And" => ``^(RVNEG ty rv (List.hd args)) /\ ^(RVNEG ty rv (List.last args))`` 
         | "Or" => ``^(RVNEG ty rv (List.hd args)) \/ ^(RVNEG ty rv (List.last args))`` 
         | "RV" => if (Term.compare(rv,List.hd args)=EQUAL) 
		       then inst [alpha|->ty] ``~RV ^(List.hd args)`` 
		   else inst [alpha|->ty] ``RV ^(List.hd args)``
         | "AP" => f
         | "DIAMOND" => ``<<^(List.hd args)>> ^(RVNEG ty rv (List.last args))``
         | "BOX" => ``[[^(List.hd args)]] ^(RVNEG ty rv (List.last args))``
         | "mu" => if (Term.compare(rv,List.hd args)=EQUAL) then ``mu ^(List.hd args) .. ^(List.last args)`` 
                                                              else ``mu ^(List.hd args) .. ^(RVNEG ty rv (List.last args))`` 
         | "nu" => if (Term.compare(rv,List.hd args)=EQUAL) then ``mu ^(List.hd args) .. ^(List.last args)`` 
                                                              else ``mu ^(List.hd args) .. ^(RVNEG ty rv (List.last args))`` 
         | _         => (print "ERROR:"; print_term f; print "\n"; Raise Match) end

fun mu_neg f = ``Not ^f``;

fun is_RV mf = is_comb mf andalso (Term.compare(fst(dest_comb mf),inst[alpha|->hd(snd(dest_type(type_of mf)))] ``RV``)=EQUAL)

fun mu_RV state rv = mk_comb(inst[alpha|->mk_type("fun",[type_of state,bool])]``RV``,rv) 

fun mu_AP state p = ``AP ^(ksTools.mk_AP state p)``;

fun is_mu mf = is_comb mf andalso  (Term.compare(fst(strip_comb mf),inst[alpha|->hd(snd(dest_type(type_of mf)))] ``$mu``)=EQUAL)

fun is_nu mf = is_comb mf andalso  (Term.compare(fst(strip_comb mf),inst[alpha|->hd(snd(dest_type(type_of mf)))] ``$nu``)=EQUAL)

fun is_fp mf = is_nu mf orelse is_mu mf

fun mu_conj l r = ``And (^l) (^r)``

fun list_mu_conj l = 
if (List.null l) then ``TR`` 
else if (List.null (List.tl l)) then (List.hd l)
else mu_conj (List.hd l) (list_mu_conj (List.tl l))

fun mu_disj l r = ``Or(^l,^r)``

fun list_mu_disj l = 
if (List.null l) then ``FL`` 
else if (List.null (List.tl l)) then (List.hd l)
else mu_disj (List.hd l) (list_mu_disj (List.tl l))

fun list_mk_disj2 [] = ``F:bool``
|   list_mk_disj2 l = list_mk_disj l

fun mu_dmd act rest = ``<<^act>> ^rest``

fun list_mu_dmd (acth::acttl) rest = mu_dmd acth (list_mu_dmd acttl rest)
|   list_mu_dmd [] rest = rest

fun mu_box act rest = ``[[^act]] ^rest``

fun list_mu_box (acth::acttl) rest = mu_box acth (list_mu_box acttl rest)
|   list_mu_box [] rest = rest

fun mu_lfp bv rest = ``mu ^bv .. ^rest``

fun mu_gfp bv rest = ``nu ^bv .. ^rest``

val mu_T_tm = ``TR``;
val mu_F_tm = ``FL``;

(* give negation normal form of f *)
fun NNF f = 
  let val (opr,args) = strip_comb f
      val ty = List.hd(snd(dest_type (type_of f)))
    in case (fst(dest_const opr)) of
           "TR" => f
         | "FL"  => f
         | "And" => ``^(NNF (List.hd args)) /\ ^(NNF (List.last args))`` 
         | "Or" => ``^(NNF (List.hd args)) \/ ^(NNF (List.last args))`` 
         | "RV" => f
         | "AP" => f
         | "DIAMOND" => ``<<^(List.hd args)>> ^(NNF (List.last args))``
         | "BOX" => ``[[^(List.hd args)]] ^(NNF (List.last args))``
         | "mu" =>  ``mu ^(List.hd args) .. ^(NNF (List.last args))`` 
         | "nu" =>  ``mu ^(List.hd args) .. ^(NNF (List.last args))`` 
         | "Not" => 
              let val (opr,args) = strip_comb (List.hd args)
              in case (fst(dest_const opr)) of
              "TR" => ``FL:^(ty_antiq(type_of f))``
            | "FL"  => ``TR:^(ty_antiq(type_of f))``
            | "And" => ``(^(NNF (mu_neg(List.hd args)))) \/ (^(NNF (mu_neg(List.last args))))`` 
            | "Or" => ``(^(NNF (mu_neg(List.hd args)))) /\ (^(NNF (mu_neg(List.last args))))`` 
            | "RV" => f
            | "AP" => f
            | "DIAMOND" => ``[[^(List.hd args)]] ^(NNF (mu_neg(List.last args)))``
            | "BOX" => ``<<^(List.hd args)>> ^(NNF (mu_neg(List.last args)))``
            | "Not" => NNF (List.hd args)
            | "mu" =>  ``nu ^(List.hd args) .. ^(NNF(RVNEG ty (List.hd args) (mu_neg(List.last args))))`` 
            | "nu" =>  ``mu ^(List.hd args) .. ^(NNF(RVNEG ty (List.hd args) (mu_neg(List.last args))))`` 
            | _  => (print "ERROR:"; print_term f; print "\n"; Raise Match) end 
         | _ => (print "ERROR:"; print_term f; print "\n"; Raise Match) end

(* free vars of a mu formula *)
fun fv mf =
  let val (opr,args) = HolKernel.strip_comb mf;
      (*val (name,ty) = dest_const opr;*)
  in  case (fst (dest_const opr)) of
          "AP"      => []
        | "RV"      => [List.hd args]
        | "And"     => (fv (List.hd args))@(fv (List.last args))
        | "Or"      => (fv (List.hd args))@(fv (List.last args))
        | "Not"     => fv (List.hd args)
        | "TR"      => []
        | "FL"      => []
        | "DIAMOND" => fv (List.last args)
        | "BOX"     => fv (List.last args)
        | "mu"      => List.filter (fn v => not (Term.compare(v,List.hd args)=EQUAL)) (fv (List.last args))
        | "nu"      => List.filter (fn v => not (Term.compare(v,List.hd args)=EQUAL)) (fv (List.last args))
        | _         => Raise Match
  end

(* is mf an existential property i.e. ?f a. <a> f SUBF (NNF mf) *)
fun is_existential mf = 
    let val prop_ty = hd(snd(dest_type(type_of mf)))
    in not (List.null (find_terms (can (match_term (inst [alpha|->prop_ty] ``<<a>> f``))) (NNF mf))) end

fun is_universal mf = not (is_existential mf) 

(* Can this mf have a counterexample/witness. FIXME : This is not completely accurate e.g. AG /\ AG fails the test *)
(* However, we'll need to fi the trace generation code before formulas lie that can be traced *)
fun is_traceable mf = is_fp mf orelse (is_comb mf andalso is_fp (rand mf))

(* take f:mu and create a HOL term that replaces all :mu constants by bool names of the same type structure 
   this creates a nonsensical but purely boolean term out of f, and since we use exists and forall to replace the binders, 
   we can do alpha-equivalence analysis on the returned formula without having to implement alpha-equivalence for :mu *)
fun mk_hol_proxy f = 
 let val (opr,args) = HolKernel.strip_comb f
      (*val (name,ty) = dest_const opr;*)
     val ttp = mk_type("fun",[``:string``,bool])
     val ttq = mk_type("fun",[bool,bool])
  in  case (fst (dest_const opr)) of
          "AP"      => mk_comb(``(PP:^(ty_antiq ttp))``,(List.hd args)) 
        | "RV"      => mk_comb(``(QQ:^(ty_antiq ttq))``,mk_bool_var(fromHOLstring(List.hd args))) 
        | "And"     => mk_conj(mk_hol_proxy (List.hd args),mk_hol_proxy (List.last args))
        | "Or"      => mk_disj(mk_hol_proxy (List.hd args),mk_hol_proxy (List.last args))
        | "Not"     => mk_neg (mk_hol_proxy (List.hd args))
        | "TR"      => T
        | "FL"      => F
        | "DIAMOND" => mk_comb (mk_comb(``DD:string -> bool -> bool``,List.hd args),mk_hol_proxy (List.last args))
        | "BOX"     => mk_comb (mk_comb(``BB:string -> bool -> bool``,List.hd args),mk_hol_proxy (List.last args))
        | "mu"      => mk_exists(mk_bool_var(fromHOLstring(List.hd args)),mk_comb(``MM:bool -> bool``,mk_hol_proxy (List.last args)))
        | "nu"      => mk_forall(mk_bool_var(fromHOLstring(List.hd args)),mk_comb(``NN:bool -> bool``,mk_hol_proxy (List.last args)))
        | _         => Raise Match
  end

fun mu_unproxy f = 
let val (opr,args) = HolKernel.strip_comb f
    val nm = if is_const opr then fst (dest_const opr) else fst (dest_var opr)
in case nm of
        "PP"  => ``AP ^(List.hd args)`` 
      | "QQ"  => ``RV ^(fromMLstring(term_to_string2(List.hd args)))``
      | "/\\" => mu_conj (mu_unproxy (List.hd args)) (mu_unproxy (List.last args))
      | "\\/" => mu_disj (mu_unproxy (List.hd args)) (mu_unproxy (List.last args))
      | "~"   => mu_neg (mu_unproxy (List.hd args))
      | "T"   => ``TR``
      | "F"   => ``FL``
      | "DD"  => mu_dmd (List.hd args) (mu_unproxy (List.last args)) 
      | "BB"  => mu_box (List.hd args) (mu_unproxy (List.last args)) 
      | "?"   => mu_lfp (fromMLstring(term_to_string2(fst(dest_abs(List.hd args))))) 
	         (mu_unproxy (snd(dest_comb(snd(dest_abs(List.hd args))))))
      | "!"   => mu_gfp (fromMLstring(term_to_string2(fst(dest_abs(List.hd args))))) 
	         (mu_unproxy (snd(dest_comb(snd(dest_abs(List.hd args))))))
      | _ => Raise Match
end

(* this will rename bound variables so that alpha-equivalent terms can be cached via a strict term-matcher that knows nothing about
   alpha equivlance e.g. Term.compare *)
fun rename f = 
let val l1 = (find_terms (can (match_term ``mu Q .. t``)) f) @  (find_terms (can (match_term ``nu Q .. t``)) f)
    val l2 = List.filter (fn t => List.null (fv t)) l1
    val l2 = List.map mk_hol_proxy l2
    val fp = mk_hol_proxy f
    in List.foldl (fn (sf,f) => subst (List.map (fn t => (t |-> (mu_unproxy sf))) (List.map mu_unproxy (find_terms (aconv sf) fp))) f) f l2 end

(* given f, returns |- !Q. SUBFORMULA (~RV Q) (NNF f) = (RV Q = RV P1) ... where the P_i are free in f and occur -vely *)
fun NNF_RVNEG_CONV f =
    let val _ = print "NNF_RVNEG_CONV\n"
	val _ = print_term f val _ = print " f\n"(*DBG*)
	val fvl = fv f
	val rvnl = List.map (fn t => snd(dest_comb(snd(dest_comb t)))) ((find_terms (can (match_term (``~(RV a)``)))) (NNF f))
	val frvnl = Binaryset.foldl (fn (t,al) => t::al) [] 
	    (Binaryset.intersection((Binaryset.addList(Binaryset.empty Term.compare,fvl)),
				    (Binaryset.addList(Binaryset.empty Term.compare,rvnl))))
	val _ = List.app print_term frvnl val _ = print " frvnl\n"(*DBG*)
	val gl = ``!Q. SUBFORMULA (~(RV Q)) (NNF ^f) = ^(list_mk_disj2 (List.map (fn t => mk_eq(``Q:string``,t)) frvnl))``
	val _ = print_term gl val _ = print " goal\n"(*DBG*)
	val res = prove(gl,SIMP_TAC std_ss (MU_SUB_def::RVNEG_def::NNF_def::(tsimps "mu")) THEN PROVE_TAC [])
	val _ = print "NNF_RVNEG_CONV done\n"(*DBG*)
    in  res end


(* converts propositional mu formula to propositional formula *)
(* assumes AP's are of type :state_type->bool where the body is purely boolean  *)
(* FIXME: this will need to be fixed once we have AP's that are not over bools *)
fun boolify f =
    let val (opr,args) = strip_comb f
    in case (fst(dest_const opr)) of
           "TR" => ``T``
         | "FL"  => ``F``
         | "Not" => mk_neg(boolify(List.hd args))
         | "And" => mk_conj(boolify(List.hd args),boolify(List.last args))
         | "Or" => mk_disj(boolify (List.hd args),boolify (List.last args))
         | "AP" => pairSyntax.pbody (List.hd args)
         | _         => (print "ERROR, non-boolean mu term in boolify:"; print_term f; print "\n"; Raise Match) end

(* returns maximum quantifier depth *)
fun qdepth f =
    let val (opr,args) = strip_comb f
    in case (fst(dest_const opr)) of
           "TR" => 0
         | "FL"  => 0
         | "Not" => qdepth (List.hd args)
         | "And" => Int.max(qdepth (List.hd args),qdepth (List.last args))
         | "Or" => Int.max(qdepth (List.hd args),qdepth (List.last args))
         | "RV" => 0
         | "AP" => 0
         | "DIAMOND" => qdepth (List.last args)
         | "BOX" => qdepth (List.last args)
         | "mu" => 1+(qdepth (List.last args))
         | "nu" => 1+(qdepth (List.last args))
         | _         => (print "ERROR:"; print_term f; print "\n"; Raise Match) end


(* return a string term that is not the same as any in l, formed by priming mv enough times *)
fun mk_subs mv l =
        let fun mk_subs2 mv ll =
                let val cla = List.find (fn x => (Term.compare(mv,x)=EQUAL)) ll
                in if (Option.isSome cla) then fromMLstring((fromHOLstring mv)^"'") else mv end
        in List.foldl (fn (_,av) => mk_subs2 av l) mv l end

(* rename all bound vars so that no two are the same, or clash with a free var name *)
fun uniq mf l subs =
  let val (opr,args) = HolKernel.strip_comb mf;
      val prop_type = List.hd(snd(dest_type(type_of mf)))
      (*val (name,ty) = dest_const opr;*)
  in  case (fst (dest_const opr)) of
          "AP"      => (mf,l)
        | "RV"      => (inst [``:'a``|->prop_type] ``RV ^(List.foldr (fn (sb,av) => if (Term.compare(snd sb,av)=EQUAL)
                                                         then fst sb else av) (List.hd args) subs)``,l)
        | "And"     => let val (lf,ll) = uniq (List.hd args) l  subs;
                           val (rf,rl) = uniq (List.last args) ll  subs
                       in (``^lf /\ ^rf``,rl) end
        | "Or"      => let val (lf,ll) = uniq (List.hd args) l  subs;
                           val (rf,rl) = uniq (List.last args) ll  subs
                       in (``^lf \/ ^rf``,rl) end
        | "Not"     => let val (nf,nl) = uniq (List.hd args) l  subs in (``~(^nf)``,nl) end
        | "TR"      => (mf,l)
        | "FL"      => (mf,l)
        | "DIAMOND" => let val (nf,nl) = uniq (List.last args) l  subs in (``<<^(List.hd args)>> (^nf)``,nl) end
        | "BOX"     => let val (nf,nl) = uniq (List.last args) l  subs in (``[[^(List.hd args)]] (^nf)``,nl) end
        | "mu"      => if (Option.isSome (List.find (fn x => (Term.compare(List.hd args,x)=EQUAL)) l))
                        then let val nn = mk_subs (List.hd args) l
                                 val subs = subs@[(nn,List.hd args)]
                                 val (nf,nl) = uniq (List.last args) (l@[nn])  subs
                             in (``mu ^(nn) .. ^nf``,l@nl) end
                        else let val (nf,nl) = uniq (List.last args) ((List.hd args)::l) subs in (``mu ^(List.hd args) .. ^nf``,l@nl) end
        | "nu"      => if (Option.isSome (List.find (fn x => (Term.compare(List.hd args,x)=EQUAL)) l))
                        then let val nn = mk_subs (List.hd args) l
                                 val subs = subs@[(nn,List.hd args)]
                                 val (nf,nl) = uniq (List.last args) (l@[nn])  subs
                             in (``nu ^(nn) .. ^nf``,l@nl) end
                        else let val (nf,nl) = uniq (List.last args) ((List.hd args)::l) subs in (``nu ^(List.hd args) .. ^nf``,l@nl) end
        | _         => Raise Match
  end

 
end
end








