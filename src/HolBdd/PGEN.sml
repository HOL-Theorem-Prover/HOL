

local

open Globals HolKernel Parse basicHol90Lib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

open Psyntax;
open pairTheory;

(*---------------------------------------------------------------------------*
 *                                                                           *
 *     (x = (v1,...,vn))       |- M[(v1,...,vn)]                             *
 *    ---------------------------------------------                          *
 *      ?v1 ... vn. x = (v1,...,vn) |- M[x]                                  *
 *                                                                           *
 *---------------------------------------------------------------------------*)
fun VSTRUCT_ABS bind th =
  let fun CHOOSER v (tm,thm) =
        let val ex_tm = Dsyntax.mk_exists{Bvar=v,Body=tm}
        in (ex_tm, CHOOSE(v, ASSUME ex_tm) thm)
        end
      val L = rev (free_vars (Dsyntax.rhs bind))
  in snd(itlist CHOOSER L (bind, SUBS[SYM(ASSUME bind)] th))
  end;


(*---------------------------------------------------------------------------*
 *                                                                           *
 *              `x`   `<varstruct>`                                          *
 *        --------------------------------                                   *
 *          |- ?v1..vn. x = <varstruct>                                      *
 *                                                                           *
 *---------------------------------------------------------------------------*)
local val pthm = GSYM pairTheory.PAIR
      val mk_eq = Psyntax.mk_eq
      fun PERR s1 s2 = HOL_ERR{origin_structure = "<top-level>",
                               origin_function = s1, message = s2};
in
fun PAIR_EX x vstruct =
let fun pair_exists node value thm =
  if (is_var value)
  then EXISTS(Psyntax.mk_exists
               (value, Term.subst[node|->value] (concl thm)), node) thm
    else
    let val (vlist,{lhs,rhs}) = (I##Dsyntax.dest_eq)(strip_exists(concl thm))
        val v = genvar(type_of node)
        val template = list_mk_exists(vlist,mk_eq(lhs,Term.subst[node|->v] rhs))
        val expansion = ISPEC node pthm
        val (node1, node2) = Psyntax.dest_pair(Dsyntax.rhs(concl expansion))
        val pthm' = Thm.SUBST[v |-> expansion] template thm
        val (value1,value2) = Psyntax.dest_pair value
    in pair_exists node1 value1 (pair_exists node2 value2 pthm')
    end handle _ => raise PERR "PAIR_EX" ""
in
  pair_exists x vstruct (REFL x)
end end

in

(*---------------------------------------------------------------------------*
 * Generalize a free tuple (vstr) into a universally quantified variable (a).*
 * There must be a faster way! Note however that the notion of "freeness" for*
 * a tuple is different than for a variable: if variables in the tuple also  *
 * occur in any other place than an occurrences of the tuple, they aren't    *
 * "free" (which is thus probably the wrong word to use).                    *
 *---------------------------------------------------------------------------*)

fun PGEN a vstr th =
   GEN a (if (is_var vstr)
          then Thm.INST [vstr |-> a] th
          else PROVE_HYP (PAIR_EX a vstr)
                         (VSTRUCT_ABS (Dsyntax.mk_eq{lhs=a, rhs=vstr}) th))

exception PGEN_TAC_error;

fun PGEN_TAC vars (asl:Term.term list,tm) =
 let val (v,_) = Psyntax.dest_forall tm
     val tm'   = Term.beta_conv(Psyntax.mk_comb(Term.rand tm,vars))
 in
 ([(asl,tm')], fn [th] => PGEN v vars th | _ => raise PGEN_TAC_error)
 end;

end;
