(* ===================================================================== *)
(* FILE          : const_def.sml                                         *)
(* DESCRIPTION   : Three variants on the principle of definition. The    *)
(*                 third argument to new_infix_definition is the         *)
(*                 precedence. Translated from hol88, except for the     *)
(*                 precedence stuff.                                     *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)

structure Const_def :> Const_def =
struct

open Exception Theory Type Term Dsyntax Lib
infix |-> -->;

fun ERR function message =
    Exception.HOL_ERR{origin_structure = "Const_def",
		      origin_function = function,
		      message = message}

local val tagr = ref (Tag.read"dummy")
      val _ = Thm.Const_def_init tagr
      val store_defnr = ref (fn ("",Lib.LEFT(""):(string,string list)Lib.sum,
                                 th,_:term) => th)
      val _ = Theory.expose_store_definition store_defnr
in
  val std_tag = !tagr
  val store_definition = !store_defnr
end;


local
fun check_varstruct tm =
   if (is_var tm) then [tm]
   else let val {fst,snd} = dest_pair tm
            val l1 = check_varstruct fst
            and l2 = check_varstruct snd
        in if (null_intersection l1 l2) then (l1@l2) else raise ERR "" ""
        end handle HOL_ERR _ => raise ERR"check_varstruct" "bad varstruct"
 val err = ERR"check_lhs" "bad lhs in def"
in
fun check_lhs tm =
  if (is_abs tm) then raise err else
  if (is_var tm orelse is_const tm) then [tm] else
  let val {Rator,Rand} = dest_comb tm
      val l1 = check_lhs Rator
      and l2 = check_varstruct Rand
  in
    if (null_intersection l1 l2) then (l1@l2) else raise err
  end
end;


(*---------------------------------------------------------------------------*
 * if `C ... = (...:ty)` then  (get_type `C ...` ty) gives the               *
 *  type of C.                                                               *
 *                                                                           *
 *---------------------------------------------------------------------------*)
fun get_type tm rightty =
   if (is_var tm orelse is_const tm) then rightty
   else if (is_comb tm)
        then let val {Rator,Rand} = dest_comb tm
             in get_type Rator (type_of Rand --> rightty)
             end
        else raise ERR"get_type" "bad lhs in def";


fun dest_atom tm = (dest_var tm handle HOL_ERR _ => dest_const tm)

fun check1 a rhs =
  if is_var a then a
  else
   let val (atom as {Name, ...}) = dest_const a
       val {theory,...} = Term.const_decl Name
       val _ = if (theory = Theory.current_theory()) then ()
               else raise ERR"DEF_EXISTS_RULE"
                     ("Attempt to redefine constant from ancestor\
                          \ theory: "^Lib.quote theory)
      fun has_name tm = (#Name(dest_atom tm) = Name) handle HOL_ERR _ => false
   in
     if null(Dsyntax.find_terms has_name rhs) then mk_var atom
     else raise ERR"DEF_EXISTS_RULE" "recursive definitions not allowed"
   end;


(*---------------------------------------------------------------------------
 * The derived rule
 *
 *   DEF_EXISTS_RULE : term -> thm
 *
 * proves that a function defined by a definitional equation exists.
 * The implementation below uses mk_thm, but this will be changed eventually.
 *---------------------------------------------------------------------------*)
fun DEF_EXISTS_RULE tm =
 let val (vars,body0)  = strip_forall tm
     fun DEF_EX_ERR s = ERR"DEF_EXISTS_RULE" s
     val {lhs,rhs} = dest_eq body0 handle HOL_ERR _ =>
            raise DEF_EX_ERR "proposed definition is not an equation"
     val lhsvars0 = check_lhs lhs
     val a0       = List.hd lhsvars0
     val v        = check1 a0 rhs
     val lhs'     = subst [a0 |-> v] lhs
     val body     = mk_eq{lhs=lhs', rhs=rhs}
     val lhsvars  = v::List.tl lhsvars0
     val name     = #Name (dest_var v)
     val ty       = get_type lhs (Term.type_of rhs)
     and rhsvars  = Term.free_vars rhs
     val inter    = intersect lhsvars rhsvars
 in
 if not(set_eq inter rhsvars)
 then let val vnames = map (#Name o dest_var) (set_diff rhsvars lhsvars)
          val vnamestr = commafy (map Lib.quote vnames)
      in
         raise DEF_EX_ERR ("unbound var(s) in rhs: "^String.concat vnamestr)
      end
 else if mem v rhsvars
      then raise DEF_EX_ERR"recursive definitions not allowed"
    else
    case set_diff (Term.type_vars_in_term rhs)
                  (Term.type_vars_in_term v)
     of [] => Thm.mk_oracle_thm std_tag ([],
                 mk_exists{Bvar=v,
                   Body=list_mk_forall
                      (union vars (List.tl lhsvars), body)})
      | extras => raise DEF_EX_ERR (String.concat
                   ("Unbound type variable(s) in definition: "
                    :: commafy (map (Lib.quote o Type.dest_vartype) extras)))
 end;


(*---------------------------------------------------------------------------*
 * The "definition" of exists. This is evidently a real definition, but it   *
 * can't be processed by the standard principle of definition (which depends *
 * on `?' being already defined). We could use a separate PoD to accept the  *
 * definition of `?', as was done in hol90, but it is simpler to just accept *
 * it "by inspection", as was done in hol88.                                 *
 *---------------------------------------------------------------------------*)
local val used = ref false
in
fun define_exists() =
  if !used
  then raise ERR"define_exists" "called >1 time"
  else let val alpha = mk_vartype "'a"
         val x = mk_var{Name="x",Ty=alpha}
         val _ = Theory.new_constant{Name="?", Ty = (alpha --> bool) --> bool}
         val P = mk_var{Name="P",Ty=alpha --> bool}
         val sel = mk_const{Name="@",Ty=(alpha --> bool)-->alpha}
         val exdef = mk_eq{lhs=mk_const{Name="?", Ty=(alpha-->bool) --> bool},
                           rhs=mk_abs{Bvar=P,
                                Body=mk_comb{Rator=P,
                                      Rand=mk_comb{Rator=sel,Rand=P}}}}
         val _ = used := true
       in
         store_definition("EXISTS_DEF",Lib.RIGHT["?"], Thm.REFL x, exdef)
       end
end;


fun new_gen_definition{name,def} = let
  val def_thm = DEF_EXISTS_RULE def
  val cname = (#Name o dest_var o #Bvar o dest_exists o Thm.concl) def_thm
in
  Const_spec.new_specification
  {name = name, consts = [cname], sat_thm = def_thm}
end;

fun new_definition(name,def) = new_gen_definition{name=name, def=def};

end; (* CONST_DEF *)
