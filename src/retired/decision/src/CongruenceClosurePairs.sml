(****************************************************************************)
(* FILE          : cong_pairs.sml                                           *)
(* DESCRIPTION   : Deciding the equational theory of pairs using congruence *)
(*                 closure.                                                 *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 10th March 1995                                          *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 15th August 1996                                         *)
(****************************************************************************)

structure CongruenceClosurePairs =
struct

local

open Exception Term Dsyntax Theory Drule Conv 
     Psyntax DecisionConv DecisionSupport DecisionNormConvs
     LazyThm LazyRules CongruenceClosure;

fun failwith function =
   raise HOL_ERR{origin_structure = "CongruenceClosurePairs",
                 origin_function = function,
                 message = ""};

in

(*--------------------------------------------------------------------------*)
(* mk_fst : term -> term                                                    *)
(* mk_snd : term -> term                                                    *)
(* dest_fst : term -> term                                                  *)
(* dest_snd : term -> term                                                  *)
(*                                                                          *)
(* Term constructors and destructors for FST and SND.                       *)
(*--------------------------------------------------------------------------*)

fun mk_fst tm =
   let val pair_ty = type_of tm
       val ty = (hd o #Args o Rsyntax.dest_type) pair_ty
       val fun_ty = Rsyntax.mk_type {Args = [pair_ty,ty],Tyop = "fun"}
   in  mk_comb (mk_const ("FST",fun_ty),tm)
   end
   handle HOL_ERR _ => failwith "mk_fst"
and mk_snd tm =
   let val pair_ty = type_of tm
       val ty = (hd o tl o #Args o Rsyntax.dest_type) pair_ty
       val fun_ty = Rsyntax.mk_type {Args = [pair_ty,ty],Tyop = "fun"}
   in  mk_comb (mk_const ("SND",fun_ty),tm)
   end
   handle HOL_ERR _ => failwith "mk_snd";

fun dest_fst tm =
   let val (f,x) = dest_comb tm
   in  if (#Name (Rsyntax.dest_const f) = "FST")
       then x
       else failwith ""
   end
   handle (HOL_ERR _) => failwith "dest_fst"
and dest_snd tm =
   let val (f,x) = dest_comb tm
   in  if (#Name (Rsyntax.dest_const f) = "SND")
       then x
       else failwith ""
   end
   handle (HOL_ERR _) => failwith "dest_snd";

(*--------------------------------------------------------------------------*)
(* FST_CONV : term -> thm                                                   *)
(* SND_CONV : term -> thm                                                   *)
(*                                                                          *)
(* Conversions for FST and SND:                                             *)
(*                                                                          *)
(*    FST_CONV `FST (x,y)` --> |- FST (x,y) = x                             *)
(*    SND_CONV `SND (x,y)` --> |- SND (x,y) = y                             *)
(*--------------------------------------------------------------------------*)

val FST_CONV =
   let val conv = REWR_CONV (pairTheory.FST)
   in
   fn tm => (let val (x,_) = dest_pair (dest_fst tm)
             in  mk_pre_thm (([],mk_eq (tm,x)),fn () => conv tm)
             end
             handle (HOL_ERR _) => failwith "FST_CONV")
   end
and SND_CONV =
   let val conv = REWR_CONV (pairTheory.SND)
   in
   fn tm => (let val (_,y) = dest_pair (dest_snd tm)
             in  mk_pre_thm (([],mk_eq (tm,y)),fn () => conv tm)
             end
             handle (HOL_ERR _) => failwith "SND_CONV")
   end;

(*--------------------------------------------------------------------------*)
(* PAIR_EQ_CONV : term -> thm                                               *)
(*                                                                          *)
(* Converts a term that has a pair type into an explicit pair:              *)
(*                                                                          *)
(*    PAIR_EQ_CONV `x` --> |- x = (FST x,SND x)                             *)
(*--------------------------------------------------------------------------*)

val PAIR_EQ_CONV =
   let val conv = REWR_CONV (GSYM (pairTheory.PAIR))
   in
   fn tm => (mk_pre_thm (([],mk_eq (tm,mk_pair (mk_fst tm,mk_snd tm))),
                         fn () => conv tm)
             handle (HOL_ERR _) => failwith "PAIR_EQ_CONV")
   end;

(*--------------------------------------------------------------------------*)
(* PAIR_CONV : term -> thm                                                  *)
(*                                                                          *)
(* A congruence closure refutation procedure for the theory of equality     *)
(* over pairs. Special meaning is attached to the functions `,', `FST' and  *)
(* `SND'. The procedure will also handle uninterpreted function symbols.    *)
(* For a term t, it attempts to prove the theorem |- t = F. The term t must *)
(* be a conjunction of literals where each literal is an equation or the    *)
(* negation of an equation between terms built up by function application   *)
(* from `,', FST, SND, and other constants and variables.                   *)
(*--------------------------------------------------------------------------*)

fun PAIR_CONV tm =
   let val ths = CONJUNCTS (ASSUME tm)
       val posths = filter (not o is_neg o concl) ths
       and negths = filter (is_neg o concl) ths
       val tms = itlist (fn eq => fn tms => lhs eq :: rhs eq :: tms)
                    (map concl posths @ map (dest_neg o concl) negths) []
       val pairths = mapfilter PAIR_EQ_CONV tms
       val eqths = pairths @ posths
       val tms' = itlist (fn eq => fn tms => rhs eq :: tms)
                     (map concl pairths) tms
       fun fst_and_snd tm = if (is_pair tm) then [mk_fst tm,mk_snd tm] else []
       val (graph,equivs,label_for_term,extras) =
          construct_congruence fst_and_snd tms'
       val equivs' = congruence_closure (graph,label_for_term) equivs eqths
       fun extrath (_,tm) =
          (case (#1 o dest_const o rator) tm
           of "FST" => FST_CONV tm
            | "SND" => SND_CONV tm
            | _ => failwith "extrath")
          handle HOL_ERR _ => failwith "extrath"
       val equivs'' = congruence_closure (graph,label_for_term) equivs'
                         (map extrath extras)
       val falseth = refute_diseqs (equivs'',label_for_term) negths
   in  IMP_F_EQ_F_RULE (DISCH tm falseth)
   end
   handle HOL_ERR _ => failwith "PAIR_CONV";

end;

end; (* CongruenceClosurePairs *)
