structure Thry :> Thry = 
struct

open Lib USyntax;
infix 3 |->;

type thry = TypeBase.typeBase
type thm = Thm.thm
type term = Term.term
type hol_type = Type.hol_type

local fun mk_bind {redex,residue} = (redex |-> residue)
in fun mk_tfp_subst x = map mk_bind x
end;

fun match_term thry tm1 tm2 = 
   let val (th1,th2) = Term.match_term tm1 tm2
   in (mk_tfp_subst th1, mk_tfp_subst th2)
   end;

fun match_type thry ty1 ty2 = mk_tfp_subst(Type.match_type ty1 ty2);

fun typecheck thry = Lib.I

fun make_definition thry s tm = (Const_def.new_definition(s,tm), thry)

fun match_info db s = 
case (TypeBase.get db s)
 of SOME facts => SOME{case_const = TypeBase.case_const_of facts,
                       constructors = TypeBase.constructors_of facts}
  | NONE => NONE

fun induct_info db s = 
case (TypeBase.get db s)
 of SOME facts => SOME{nchotomy = TypeBase.nchotomy_of facts,
                       constructors = TypeBase.constructors_of facts}
  | NONE => NONE

fun extract_info db = 
 let val (rws,congs) = rev_itlist
     (fn tyinfo => fn (R,C) => 
         (TypeBase.case_def_of tyinfo::R, TypeBase.case_cong_of tyinfo::C))
     (TypeBase.listItems db) ([],[]) 
 in {case_congs=congs, case_rewrites=rws}
 end

end; (* Thry *)
