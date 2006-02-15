
(* various operations on terms of type mu, as well as on the ML datatype for mu formulas that is used by the checker *)

structure muSyntax =
struct

local

open Globals HolKernel Parse goalstackLib;

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

open Psyntax bossLib pairTheory pred_setTheory pred_setLib stringLib listTheory simpLib pairSyntax pairLib PrimitiveBddRules DerivedBddRules Binarymap PairRules pairTools boolSyntax Drule Tactical Conv Rewrite Tactic boolTheory listSyntax stringTheory boolSimps pureSimps listSimps numLib
open setLemmasTheory muSyntaxTheory muTheory stringBinTree commonTools ksTools

in

(* shadow syntax for efficiently working with mu formulae. 
   mk_cache translates HOL formula to it and muCheck recurses over it*)
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

val mu_ty = ``:'a mu``

fun get_prop_type f = (hd o snd o dest_type o type_of) f

val _ = set_trace "notify type variable guesses" 0;
val mu_rv_tm = ``muSyntax$RV``
val mu_neg_tm = ``muSyntax$Not``
val mu_ap_tm = ``muSyntax$AP``
val mu_and_tm = ``muSyntax$And``
val mu_or_tm = ``muSyntax$Or``
val mu_dmd_tm = ``muSyntax$DIAMOND``
val mu_box_tm = ``muSyntax$BOX``
val mu_mu_tm = ``muSyntax$mu``
val mu_nu_tm = ``muSyntax$nu``
val mu_T_tm = ``muSyntax$TR``
val mu_F_tm = ``muSyntax$FL``
val mu_ap_tm = ``muSyntax$AP``
val mu_sub_tm = ``muSyntax$SUBFORMULA``
val mu_nnf_tm = ``muSyntax$NNF``
val mu_imf_tm = ``muSyntax$IMF``
val mu_rvneg_tm = ``muSyntax$RVNEG``
val _ = set_trace "notify type variable guesses" 1;

fun is_RV f = (is_comb f andalso is_const (rator f) andalso String.compare("RV",(fst o dest_const o rator) f)=EQUAL)
fun is_mu mf = is_comb mf andalso  (Term.compare(fst(strip_comb mf),inst[alpha|->get_prop_type mf] mu_mu_tm)=EQUAL)
fun is_nu mf = is_comb mf andalso  (Term.compare(fst(strip_comb mf),inst[alpha|->get_prop_type mf] mu_nu_tm)=EQUAL)
fun is_fp mf = is_nu mf orelse is_mu mf

fun mu_RV p_ty rv = mk_comb(inst[alpha|->p_ty] mu_rv_tm,rv) 
fun mu_AP p = mk_comb(inst [alpha|->(type_of p)] mu_ap_tm,p)
fun mu_neg f = mk_comb(inst [alpha|->get_prop_type f] mu_neg_tm, f)
fun mu_conj l r = list_mk_comb(inst [alpha|->get_prop_type l] mu_and_tm,[l,r]) 
fun mu_disj l r = list_mk_comb(inst [alpha|->get_prop_type l] mu_or_tm,[l,r]) 
fun mu_dmd act rest = list_mk_comb(inst [alpha|->get_prop_type rest] mu_dmd_tm,[act,rest])(*``<<^act>> ^rest``*)
fun mu_box act rest = list_mk_comb(inst [alpha|->get_prop_type rest] mu_box_tm,[act,rest])(*``[[^act]] ^rest``*)
fun mu_lfp bv rest = list_mk_comb(inst [alpha|->get_prop_type rest] mu_mu_tm,[bv,rest])(*``mu ^bv .. ^rest``*)
fun mu_gfp bv rest = list_mk_comb(inst [alpha|->get_prop_type rest] mu_nu_tm,[bv,rest])(*``nu ^bv .. ^rest``*)

fun list_mu_conj l = 
    if (List.null l) then mu_T_tm 
    else if (List.null (List.tl l)) then (List.hd l)
    else mu_conj (List.hd l) (list_mu_conj (List.tl l))
fun list_mu_disj l = 
    if (List.null l) then mu_F_tm
    else if (List.null (List.tl l)) then (List.hd l)
    else mu_disj (List.hd l) (list_mu_disj (List.tl l))
fun list_mu_dmd (acth::acttl) rest = mu_dmd acth (list_mu_dmd acttl rest)
    | list_mu_dmd [] rest = rest
fun list_mu_box (acth::acttl) rest = mu_box acth (list_mu_box acttl rest)
  | list_mu_box [] rest = rest

val concRV = ``"Q"``

fun get_mu_ty_T_tm p_ty = inst [alpha|-> p_ty] mu_T_tm
fun get_mu_ty_F_tm p_ty = inst [alpha|-> p_ty] mu_F_tm
fun get_mu_ty_ap_tm p_ty = inst [alpha|-> p_ty] mu_ap_tm
fun get_mu_ty_rv_tm p_ty = inst [alpha|-> p_ty] mu_rv_tm
fun get_mu_ty_conj_tm p_ty = inst [alpha|-> p_ty] mu_and_tm
fun get_mu_ty_disj_tm p_ty = inst [alpha|-> p_ty] mu_or_tm
fun get_mu_ty_neg_tm p_ty = inst [alpha|-> p_ty] mu_neg_tm
fun get_mu_ty_dmd_tm p_ty = inst [alpha|-> p_ty] mu_dmd_tm
fun get_mu_ty_box_tm p_ty = inst [alpha|-> p_ty] mu_box_tm
fun get_mu_ty_rv_tm p_ty = inst [alpha|-> p_ty] mu_rv_tm
fun get_mu_ty_mu_tm p_ty = inst [alpha|-> p_ty] mu_mu_tm
fun get_mu_ty_nu_tm p_ty = inst [alpha|-> p_ty] mu_nu_tm
fun get_mu_ty_sub_tm p_ty = inst [alpha|-> p_ty] mu_sub_tm
fun get_mu_ty_nnf_tm p_ty = inst [alpha|-> p_ty] mu_nnf_tm
fun get_mu_ty_rvneg_tm p_ty = inst [alpha|-> p_ty] mu_rvneg_tm

fun get_ty_tms p_ty = 
    (get_mu_ty_T_tm p_ty,
     get_mu_ty_F_tm p_ty,
     get_mu_ty_ap_tm p_ty,
     get_mu_ty_rv_tm p_ty,
     get_mu_ty_neg_tm p_ty,
     get_mu_ty_conj_tm p_ty,
     get_mu_ty_disj_tm p_ty,
     get_mu_ty_dmd_tm p_ty,
     get_mu_ty_box_tm p_ty,
     get_mu_ty_mu_tm p_ty,
     get_mu_ty_nu_tm p_ty)

fun get_ty_cons p_ty = 
    (get_mu_ty_T_tm p_ty,
     get_mu_ty_F_tm p_ty,
     fn n => mk_comb(get_mu_ty_ap_tm p_ty,n),
     fn n => mk_comb(get_mu_ty_rv_tm p_ty,n),
     fn n => mk_comb(get_mu_ty_neg_tm p_ty,n),
     fn l => fn r => list_mk_comb(get_mu_ty_conj_tm p_ty,[l,r]),
     fn l => fn r => list_mk_comb(get_mu_ty_disj_tm p_ty,[l,r]),
     fn l => fn r => list_mk_comb(get_mu_ty_dmd_tm p_ty,[l,r]),
     fn l => fn r => list_mk_comb(get_mu_ty_box_tm p_ty,[l,r]),
     fn l => fn r => list_mk_comb(get_mu_ty_mu_tm p_ty,[l,r]),
     fn l => fn r => list_mk_comb(get_mu_ty_nu_tm p_ty,[l,r]))

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
         | _         => failwith("muSyntax.top_sigma: failed on term "^(term_to_string f)^"\n") end

(* return all top level sigma formulas in f (if nu then return nu formulas, else return mu formulas) *)
(* return only those formulas in which the RV v is free *)
fun top_sigma_free nu v f =  
    let val ts = top_sigma nu f
    in List.filter (fn f => HOLset.member(HOLset.addList(HOLset.empty Term.compare,ts),v)) ts end 

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
         | _  => failwith ("prop_subtms ERROR:"^(term_to_string f)^"\n") end

(* RVNEG(f,Q) == in f, all free ocurrances of Q are negated *)
fun RVNEG ty rv f = 
   let val (opr,args) = strip_comb f
    in case (fst(dest_const opr)) of
           "TR" => f
         | "FL"  => f
         | "Not" => mu_neg(RVNEG ty rv (List.hd args))
         | "And" => mu_conj (RVNEG ty rv (List.hd args)) (RVNEG ty rv (List.last args)) 
         | "Or" =>  mu_disj (RVNEG ty rv (List.hd args)) (RVNEG ty rv (List.last args)) 
         | "RV" => if (Term.compare(rv,List.hd args)=EQUAL) 
		   then mu_neg(mu_RV ty (hd args)) 
		   else mu_RV ty (hd args) 
         | "AP" => f
         | "DIAMOND" => mu_dmd (hd args) (RVNEG ty rv (last args)) 
         | "BOX" => mu_box (hd args) (RVNEG ty rv (last args)) 
         | "mu" => if (Term.compare(rv,List.hd args)=EQUAL) 
		   then mu_lfp (hd args) (last args) 
                   else mu_lfp (hd args) (RVNEG ty rv (last args)) 
         | "nu" => if (Term.compare(rv,List.hd args)=EQUAL) 
		   then mu_gfp (hd args) (last args) 
                   else mu_gfp (hd args) (RVNEG ty rv (last args)) 
         | _         => (print "ERROR:"; print_term f; print "\n"; Raise Match) end


(* return list of propositional subterms of f with size >= n, with duplicates/T/F removed, in decreasing order of size *)
fun prop_subtmset f n = let val p_ty = get_prop_type f
			in List.rev(fst(ListPair.unzip(Listsort.sort (fn((_,l),(_,r))=>Int.compare(l,r))
                                      (Binaryset.listItems(Binaryset.addList(Binaryset.empty
                                         (fn ((l,_),(r,_)) => Term.compare(l,r)),
                                          (List.filter (fn (t,sz)=> (sz>=n) 
								  andalso not (Term.compare(t,get_mu_ty_T_tm p_ty)=EQUAL) 
								  andalso not (Term.compare(t,get_mu_ty_F_tm p_ty)=EQUAL))
						       (prop_subtms f))))))))
			end

(* take a propositional mu formula and convert it to a single ap (but not a mu AP, just \state. prop_tm) *)
fun prop2ap f state = 
    let fun mk_ap f = 
	    let val (opr,args) = strip_comb f
		in case (fst(dest_const opr)) of
		       "TR" => T
		     | "FL"  => F
		     | "And" => mk_conj (mk_ap (hd args),mk_ap (last args))
		     | "Or" => mk_disj (mk_ap (hd args),mk_ap (last args))
		     | "AP" => (pairSyntax.pbody o hd) args
		     | "Not" => mk_neg (mk_ap (hd args))
		     | _ => failwith "Not a propositional formula"
	       end
	val ap = mk_AP state (mk_ap f)
    in ap end			 
  
(* give negation normal form of f *)
local fun NNF' (cons as (mu_t,mu_f,mu_ap,mu_rv,mu_neg,mu_conj,mu_disj,mu_dmd,mu_box,mu_mu,mu_nu)) f = 
  let val (opr,args) = strip_comb f
      val ty = List.hd(snd(dest_type (type_of f)))
    in case (fst(dest_const opr)) of
           "TR" => f
         | "FL"  => f
         | "And" => mu_conj(NNF' cons (List.hd args))(NNF' cons (List.last args)) 
         | "Or" => mu_disj(NNF' cons (List.hd args))(NNF' cons (List.last args)) 
         | "RV" => f
         | "AP" => f
         | "DIAMOND" => mu_dmd (List.hd args) (NNF' cons (List.last args))
         | "BOX" => mu_box (List.hd args) (NNF' cons (List.last args)) 
         | "mu" =>  mu_lfp (List.hd args) (NNF' cons (List.last args)) 
         | "nu" =>  mu_gfp (List.hd args) (NNF' cons (List.last args)) 
         | "Not" => 
              let val (opr,args) = strip_comb (List.hd args)
              in case (fst(dest_const opr)) of
              "TR" => mu_f
            | "FL"  => mu_t
            | "And" => mu_disj(NNF' cons (mu_neg(List.hd args)))(NNF' cons (mu_neg(List.last args)))
            | "Or" => mu_conj(NNF' cons (mu_neg(List.hd args)))(NNF' cons (mu_neg(List.last args)))
            | "RV" => f
            | "AP" => f
            | "DIAMOND" => mu_box (List.hd args) (NNF' cons (mu_neg(List.last args)))
            | "BOX" => mu_dmd (List.hd args) (NNF' cons (mu_neg(List.last args))) 
            | "Not" => NNF' cons (List.hd args)
            | "mu" =>  mu_gfp (List.hd args) (NNF' cons (RVNEG ty (List.hd args) (mu_neg(List.last args))))
            | "nu" => mu_lfp (List.hd args) (NNF' cons (RVNEG ty (List.hd args) (mu_neg(List.last args)))) 
            | _  => (print "ERROR:"; print_term f; print "\n"; Raise Match) end 
         | _ => (print "ERROR:"; print_term f; print "\n"; Raise Match) end
in fun NNF f = NNF' (get_ty_cons (get_prop_type f)) f 
end

local 
fun isv s p f = 
    let val (opr,args) = strip_comb f
    in case (fst(dest_const opr)) of
           "TR" => true
         | "FL"  => true
         | "Not" =>  isv s (not p) (List.hd args)
         | "And" => (isv s p (List.hd args)) andalso (isv s p (List.last args))
         | "Or" => (isv s p (List.hd args)) andalso (isv s p (List.last args))
         | "RV" => ((Binarymap.find(s,List.hd args)=p) handle ex => true)
         | "AP" => true
         | "DIAMOND" => isv s p (List.last args)
         | "BOX" => isv s p (List.last args)
         | "mu" => isv (Binarymap.insert(s,List.hd args,p)) p (List.last args)
         | "nu" => isv (Binarymap.insert(s,List.hd args,p)) p (List.last args)
         | _         => (print "ERROR:"; print_term f; print "\n"; Raise Match) end
(* check if f has bound variables occuring positively only *)
in fun is_valid f = isv (Binarymap.mkDict Term.compare) true f end

local 
fun isx p f =
    let val (opr,args) = strip_comb f
    in case (fst(dest_const opr)) of
           "TR" => false
         | "FL"  => false
         | "Not" =>  isx (not p) (List.hd args)
         | "And" => (isx p (List.hd args)) orelse (isx p (List.last args))
         | "Or" => (isx p (List.hd args)) orelse (isx p (List.last args))
         | "RV" => false
         | "AP" => false
         | "DIAMOND" => if p then true else isx p (List.last args)
         | "BOX" => isx p (List.last args)
         | "mu" => isx  p (List.last args)
         | "nu" => isx  p (List.last args)
         | _         => (print "ERROR:"; print_term f; print "\n"; Raise Match) end
(* is f an existential property i.e. ?g a. <a> g SUBF (NNF f) *)
(* in other words, at least one <<>> must occur positively *)
in fun is_existential f = isx true f end

fun is_universal mf = not (is_existential mf) 

(* Can this mf have a counterexample/witness: is it a top level fp or negated fp  *)
(* FIXME : This is not completely accurate e.g. AG /\ AG fails the test. 
   However, we'll need to fix the trace generation code before formulas like that can be traced *)
fun is_traceable mf = is_fp (NNF mf)

(* take f:mu and create a HOL term that replaces all :mu constants by bool names of the same type structure.
   This creates a nonsensical but purely boolean term out of f, and since we use exists and forall to replace the binders,
   we can do alpha-equivalence analysis on the returned formula without having to implement alpha-equivalence for :mu *)
fun mk_hol_proxy f = 
 let val (opr,args) = HolKernel.strip_comb f
     val ttp = stringLib.string_ty --> bool
     val ttq = bool --> bool 
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
        | "mu"      => mk_exists(mk_bool_var(fromHOLstring(List.hd args)),
				 mk_comb(``MM:bool -> bool``,mk_hol_proxy (List.last args)))
        | "nu"      => mk_forall(mk_bool_var(fromHOLstring(List.hd args)),
				 mk_comb(``NN:bool -> bool``,mk_hol_proxy (List.last args)))
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
    in List.foldl (fn (sf,f) => subst (List.map (fn t => (t |-> (mu_unproxy sf))) 
						(List.map mu_unproxy (find_terms (aconv sf) fp))) f) f l2 
    end

(* given f, returns |- !Q. SUBFORMULA (~RV Q) (NNF f) = (RV Q = RV P1) ... where the P_i are free in f and occur -vely *)
fun NNF_RVNEG_CONV f =
    let val _ = print "NNF_RVNEG_CONV\n"
	val _ = print_term f val _ = print " f\n"(*DBG*)
	val fvl = fv f
	val rvnl = List.map (fn t => snd(dest_comb(snd(dest_comb t)))) 
			    ((find_terms (can (match_term (``~(RV a)``)))) (NNF f))
	val frvnl = Binaryset.foldl (fn (t,al) => t::al) [] 
	    (Binaryset.intersection((Binaryset.addList(Binaryset.empty Term.compare,fvl)),
				    (Binaryset.addList(Binaryset.empty Term.compare,rvnl))))
	val _ = List.app print_term frvnl val _ = print " frvnl\n"(*DBG*)
	val gl = ``!Q. SUBFORMULA (~(RV Q)) (NNF ^f) = ^(list_mk_disj2 (List.map (fn t => mk_eq(``Q:string``,t)) frvnl))``
	val _ = print_term gl val _ = print " goal\n"(*DBG*)
	val res = prove(gl,SIMP_TAC std_ss (MU_SUB_def::RVNEG_def::NNF_def::(tsimps ``:'a mu``)) THEN PROVE_TAC [])
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


(* return a list of all terms of the form AP p that occur in f *)
fun find_APs f = let val p_ty  = get_prop_type f
		     val pvar = mk_var("p",p_ty)
		 in find_terms (can (match_term (mk_comb(get_mu_ty_ap_tm p_ty,pvar)))) f end

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

(* return the alternation depth of the given formula *)
fun alt_depth mf = 
   let val (opr,args) = strip_comb mf
    in case (fst(dest_const opr)) of
           "TR" => 0
         | "FL"  => 0
         | "Not" => alt_depth (List.hd args)
         | "And" => Int.max(alt_depth (List.hd args),alt_depth (List.last args))
         | "Or" =>  Int.max(alt_depth (List.hd args),alt_depth (List.last args))
         | "RV" => 0
         | "AP" => 0
         | "DIAMOND" => alt_depth (List.last args)
         | "BOX" => alt_depth (List.last args)
         | "mu" => listmax [1,alt_depth (List.last args),1+listmax (List.map alt_depth (top_sigma_free true (hd args) (last args)))]
         | "nu" => listmax [1,alt_depth (List.last args),1+listmax (List.map alt_depth (top_sigma_free false (hd args) (last args)))]
         | _         => failwith ("alt_depth Match:"^(term_to_string mf)) end

(* return the max same-quantifier nesting depth of the given formula *)
fun sameq_depth mf = 
   let val (opr,args) = strip_comb mf
    in case (fst(dest_const opr)) of
           "TR" => 0
         | "FL"  => 0
         | "Not" => sameq_depth (List.hd args)
         | "And" => Int.max(sameq_depth (List.hd args),sameq_depth (List.last args))
         | "Or" =>  Int.max(sameq_depth (List.hd args),sameq_depth (List.last args))
         | "RV" => 0
         | "AP" => 0
         | "DIAMOND" => sameq_depth (List.last args)
         | "BOX" => sameq_depth (List.last args)
         | "mu" => listmax [1,sameq_depth (List.last args),1+listmax (List.map sameq_depth (top_sigma_free false (hd args) (last args)))]
         | "nu" => listmax [1,sameq_depth (List.last args),1+listmax (List.map sameq_depth (top_sigma_free true (hd args) (last args)))]
         | _         => failwith ("sameq_depth Match:"^(term_to_string mf)) end
 
end
end
