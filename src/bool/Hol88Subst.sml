structure Hol88Subst :> Hol88Subst =
struct

open Lib Abbrev;
infix ##;


type ('a,'b)hol88subst = ('b * 'a) list

fun pair2recd (M,v) = {redex=v, residue=M}
fun recd2pair{redex,residue} = (residue,redex);

fun hol88subst_of s = map recd2pair s;
fun subst_of s = map pair2recd s;

val type_subst             = Type.type_subst o subst_of
fun match_type ty          = hol88subst_of o Type.match_type ty
val subst                  = Term.subst o subst_of
val inst                   = Term.inst o subst_of
fun subst_occs occs_list   = HolKernel.subst_occs occs_list o subst_of
fun match_term pat ob      = (hol88subst_of ## hol88subst_of) 
                             (Term.match_term pat ob)

fun SUBST s template th    = Thm.SUBST (subst_of s) template th
val INST                   = Thm.INST o subst_of
val INST_TYPE              = Thm.INST_TYPE o subst_of;
fun SUBST_CONV s templ tm  = Drule.SUBST_CONV (subst_of s) templ tm
val INST_TY_TERM           = Drule.INST_TY_TERM o (subst_of##subst_of);

end;
