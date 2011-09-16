structure Opentheory :> Opentheory = struct

open boolSyntax HolKernel Parse OpenTheoryMap OpenTheoryCommon

local open Thm Drule in
  fun DEDUCT_ANTISYM th1 th2 =
    IMP_ANTISYM_RULE
      (DISCH (concl th2) th1)
      (DISCH (concl th1) th2)
end

val ERR = mk_HOL_ERR "Opentheory"

type reader =
{ define_tyop  : {name:thy_tyop, ax:thm, args:hol_type list, rep:thy_const, abs:thy_const} ->
                 {rep_abs:thm, abs_rep:thm}
, define_const : thy_const -> term -> thm
, axiom        : thm Net.net -> (term list * term) -> thm
}

fun st_(st,{stack,dict,thms,...}) = {stack=st,dict=dict,thms=thms}
fun push (ob,st) = st_(ob::(#stack st),st)
local open Substring in
  val trimlr = fn s => string(trimr 1 (triml 1 (full s)))
  val trimr  = fn s => string(trimr 1 (full s))
end

fun raw_read_article {tyop_from_ot,const_from_ot} input {define_tyop,define_const,axiom} = let
  val ERR = ERR "read_article"
  fun unOTermls c = List.map (fn OTerm t => t | _ => raise ERR (c^" failed to pop a list of terms"))
  fun unOTypels c = List.map (fn OType t => t | _ => raise ERR (c^" failed to pop a list of types"))
  fun ot_to_const c s = Map.find(const_from_ot,string_to_otname s)
  handle Map.NotFound => raise ERR (c^": no map from "^s^" to a constant")
  fun ot_to_tyop  c s = Map.find(tyop_from_ot ,string_to_otname s)
  handle Map.NotFound => raise ERR (c^": no map from "^s^" to a type operator")
  val mk_vartype = mk_vartype o tyvar_from_ot o string_to_otname
  fun f "absTerm"(st as {stack=OTerm b::OVar v::os,...}) = st_(OTerm(mk_abs(v,b))::os,st)
    | f "absThm" (st as {stack=OThm th::OVar v::os,...}) = (st_(OThm(ABS v th)::os,st)
      handle HOL_ERR e => raise ERR "absThm: failed")
    | f "appTerm"(st as {stack=OTerm x::OTerm f::os,...})= st_(OTerm(mk_comb(f,x))::os,st)
    | f "appThm" (st as {stack=OThm xy::OThm fg::os,...})= let
        val (f,g) = dest_eq(concl fg)
        val (x,y) = dest_eq(concl xy)
        val fxgx  = AP_THM fg x
        val gxgy  = AP_TERM g xy
      in st_(OThm(TRANS fxgx gxgy)::os,st) end
    | f "assume"       (st as {stack=OTerm t::os,...})          = st_(OThm(ASSUME t)::os,st)
    | f "axiom"        (st as {stack=OTerm t::OList ts::os,thms,...}) = st_(OThm(axiom thms (unOTermls "axiom" ts,t))::os,st)
    | f "betaConv"     (st as {stack=OTerm t::os,...})          = st_(OThm(BETA_CONV t)::os,st)
    | f "cons"         (st as {stack=OList t::h::os,...})       = st_(OList(h::t)::os,st)
    | f "const"        (st as {stack=OName n::os,...})          = st_(OConst (ot_to_const "const" n)::os,st)
    | f "constTerm"    (st as {stack=OType Ty::OConst {Thy,Name}::os,...})
                     = st_(OTerm(mk_thy_const {Ty=Ty,Thy=Thy,Name=Name})::os,st)
    | f "deductAntisym"(st as {stack=OThm t1::OThm t2::os,...}) = st_(OThm(DEDUCT_ANTISYM t1 t2)::os,st)
    | f "def"         {stack=ONum k::x::os,dict,thms,...}       = {stack=x::os,dict=Map.insert(dict,k,x),thms=thms}
    | f "defineConst" (st as {stack=OTerm t::OName n::os,...})  = let
        val c = ot_to_const "defineConst" n
        val def = define_const c t
        handle Map.NotFound => raise ERR ("defineConst: no map from "^thy_const_to_string c^" to a definition function")
      in st_(OThm def::OConst c::os,st) end
    | f "defineTypeOp"  (st as {stack=OThm ax::OList ls::OName rep::OName abs::OName n::os,...}) = let
        val ls = List.map (fn OName s => mk_vartype s | _ => raise ERR "defineTypeOp failed to pop a list of names") ls
        val tyop = ot_to_tyop "defineTypeOp" n
        val ot_to_const = ot_to_const "defineTypeOp"
        val {abs_rep,rep_abs} = define_tyop {name=tyop,ax=ax,args=ls,rep=ot_to_const rep,abs=ot_to_const abs}
        val (abs,foo) = dest_comb(lhs(concl abs_rep))
        val (rep,_)   = dest_comb foo
        val {Thy,Name,...} = dest_thy_const rep val rep = {Thy=Thy,Name=Name}
        val {Thy,Name,...} = dest_thy_const abs val abs = {Thy=Thy,Name=Name}
      in st_(OThm rep_abs::OThm abs_rep::OConst rep::OConst abs::OTypeOp tyop::os,st) end
    | f "eqMp"   (st as {stack=OThm f::OThm fg::os,...})     = (st_(OThm(EQ_MP fg f)::os,st)
      handle HOL_ERR e => raise ERR "EqMp failed")
    | f "nil"    st                                          = push(OList [],st)
    | f "opType" (st as {stack=OList ls::OTypeOp {Thy,Tyop}::os,...})
               = st_(OType(mk_thy_type{Thy=Thy,Tyop=Tyop,Args=unOTypels "opType" ls})::os,st)
    | f "pop"    (st as {stack=x::os,...})                   = st_(os,st)
    | f "ref"    (st as {stack=ONum k::os,dict,...})         = st_(Map.find(dict,k)::os,st)
    | f "refl"   (st as {stack=OTerm t::os,...})             = st_(OThm(REFL t)::os,st)
    | f "remove" {stack=ONum k::os,dict,thms,...}            = let
        val (dict,x) = Map.remove(dict,k)
      in {stack=x::os,dict=dict,thms=thms} end
    | f "subst"  (st as {stack=OThm th::OList[OList tys,OList tms]::os,...}) = let
        val tys = List.map (fn OList [OName a, OType t] => {redex=mk_vartype a, residue=t}
                             | _ => raise ERR "subst failed to pop a list of [name,type] pairs") tys
        val tms = List.map (fn OList [OVar v, OTerm t] => {redex=v, residue=t}
                             | _ => raise ERR "subst failed to pop a list of [var,term] pairs") tms
        val th = INST_TYPE tys th
        val th = INST tms th
      in st_(OThm th::os,st) end
    | f "thm"    {stack=OTerm c::OList ls::OThm th::os,dict,thms,...} = let
        val th = EQ_MP (ALPHA (concl th) c) th
        handle HOL_ERR _ => raise ERR "thm: desired conclusion not alpha-equivalent to theorem's conclusion"
        fun ft (OTerm h, th) = let
          val c = concl th
          val th = DISCH h th
          val c' = concl th
        in
          if aconv c c' then
            Drule.ADD_ASSUM h th
          else let
            val (h',_) = boolSyntax.dest_imp c'
            val h'h = ALPHA h' h
            val th = Drule.SUBS_OCCS [([1],h'h)] th
          in Drule.UNDISCH th end
        end | ft _ = raise ERR "thm failed to pop a list of terms"
        val th = List.foldl ft th ls
      in {stack=os,dict=dict,thms=Net.insert(concl th,th)thms} end
    | f "typeOp"  (st as {stack=OName n::os,...})          = st_(OTypeOp (ot_to_tyop "typeOp" n)::os,st)
    | f "var"     (st as {stack=OType t::OName n::os,...}) = st_(OVar(mk_var(n,t))::os,st)
    | f "varTerm" (st as {stack=OVar t::os,...})           = st_(OTerm t::os,st)
    | f "varType" (st as {stack=OName n::os,...})          = st_(OType(mk_vartype n)::os,st)
    | f s (st as {stack,dict,thms,...}) = let val c = String.sub(s,0) open Char Option Int
      in if c = #"\"" then push(OName(trimlr s),st) else
         if isDigit c then push(ONum(valOf(fromString s)),st) else
         if c = #"#" then {stack=stack,dict=dict,thms=thms} else
         raise ERR ("Unknown command (or bad arguments): "^s)
      end
  fun loop (x as {line_num,...}) = case TextIO.inputLine input of
    NONE => x before TextIO.closeIn(input)
  | SOME line => let
      val {stack,dict,thms} = f (trimr line) x
    in loop {stack=stack,dict=dict,thms=thms,line_num=line_num+1} end
in #thms (loop {stack=[],dict=Map.mkDict(Int.compare),thms=Net.empty,line_num=1}) end

fun read_article s r =
  raw_read_article
    {tyop_from_ot=tyop_from_ot_map(),
     const_from_ot=const_from_ot_map()}
    (TextIO.openIn s) r
end
