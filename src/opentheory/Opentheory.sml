structure Opentheory :> Opentheory = struct

val ERR = Feedback.mk_HOL_ERR "Opentheory"

structure Map = Redblackmap
type thms   = Thm.thm Net.net
type types  = (string, Type.hol_type list -> Type.hol_type) Map.dict
type consts = (string, Type.hol_type -> Term.term) Map.dict

val empty_thms     = Net.empty
val empty_types    = Map.mkDict String.compare
val empty_consts   = Map.mkDict String.compare
val thmsFromList   = List.foldl (fn (th,n) => Net.insert(Thm.concl th,th) n) empty_thms
val typesFromList  = Map.fromList String.compare
val constsFromList = Map.fromList String.compare

datatype object
= ONum of int
| OName of string
| OList of object list
| OTypeOp of string
| OType of Type.hol_type
| OConst of string
| OVar of Term.term
| OTerm of Term.term
| OThm of Thm.thm

datatype command
= Num of int
| Name of string
| AbsTerm
| AbsThm
| AppTerm
| AppThm
| Assume
| Axiom
| BetaConv
| Cons
| Const
| ConstTerm
| DeductAntisym
| Def
| DefineConst
| DefineTypeOp
| EqMp
| Nil
| OpType
| Pop
| Ref
| Refl
| Remove
| Subst
| Thm
| TypeOp
| Var
| VarTerm
| VarType

fun st_ (st,{stack,dict,thms}) = {stack=st,dict=dict,thms=thms}
fun push (ob,state) = st_ (ob::(#stack state),state)

fun find_thm thms (h,c) = let
  val candidates = Net.index c thms
  fun equal thm = let
    val c' = Thm.concl thm
    val thm' = Drule.PART_MATCH Lib.I thm (#2(boolSyntax.strip_forall c))
  in Lib.set_eq h (Thm.hyp thm') end handle Feedback.HOL_ERR _ => false
  val SOME th = List.find equal candidates
in th end

fun find_const consts (n,t) = Map.find(consts,n) t
handle Map.NotFound => Term.mk_const(n,t)
handle Feedback.HOL_ERR _ => raise ERR "find_const" ("need "^n^" of type "^(Parse.type_to_string t))

local open Thm Drule in
fun DEDUCT_ANTISYM th1 th2 =
  IMP_ANTISYM_RULE
    (DISCH (concl th1) th2)
    (DISCH (concl th2) th1)
end

val unOTermls = List.map (fn OTerm t => t)
val unOTypels = List.map (fn OType t => t)
val unONamels = List.map (fn OName n => n)

fun find_type types (t,ls) = let
  val ls = unOTypels ls
in
  (Map.find(types,t)) ls
  handle Map.NotFound => let
    val s = Parse.type_to_string(Type.mk_type(t,ls))
    handle Feedback.HOL_ERR _ =>
    (* PolyML.makestring (t, (Map.listItems types)) *)
    ("TyOp = "^t^", Args = "^(String.concatWith ", " (List.map Parse.type_to_string ls)))
  in raise ERR "find_type" ("need "^s) end
end

exception Comment

fun
  parse_line "absTerm"       = AbsTerm
| parse_line "absThm"        = AbsThm
| parse_line "appTerm"       = AppTerm
| parse_line "appThm"        = AppThm
| parse_line "assume"        = Assume
| parse_line "axiom"         = Axiom
| parse_line "betaConv"      = BetaConv
| parse_line "cons"          = Cons
| parse_line "const"         = Const
| parse_line "constTerm"     = ConstTerm
| parse_line "deductAntisym" = DeductAntisym
| parse_line "def"           = Def
| parse_line "defineConst"   = DefineConst
| parse_line "defineTypeOp"  = DefineTypeOp
| parse_line "eqMp"          = EqMp
| parse_line "nil"           = Nil
| parse_line "opType"        = OpType
| parse_line "pop"           = Pop
| parse_line "ref"           = Ref
| parse_line "refl"          = Refl
| parse_line "remove"        = Remove
| parse_line "subst"         = Subst
| parse_line "thm"           = Thm
| parse_line "typeOp"        = TypeOp
| parse_line "var"           = Var
| parse_line "varTerm"       = VarTerm
| parse_line "varType"       = VarType
| parse_line s = let
    val c = String.sub(s,0)
  in if c = #"\"" then Name (String.substring(s,1,String.size s -2)) else
     if Char.isDigit c then Num (Option.valOf (Int.fromString s))
     else raise Comment
  end

fun read_article file {types,consts,thms} = let
  val find_asm   = find_thm thms
  val find_const = find_const consts
  val find_type  = find_type types
  fun f (Num i)  st = push(ONum i,st)
    | f (Name s) st = push(OName s,st)
    | f AbsTerm  (st as {stack=OTerm b::OVar v::os,...})  = st_(OTerm(Term.mk_abs(v,b))::os,st)
    | f AppTerm  (st as {stack=OTerm x::OTerm f::os,...}) = st_(OTerm(Term.mk_comb(f,x))::os,st)
    | f AppThm   (st as {stack=OThm xy::OThm fg::os,...}) = let
        val (f,g) = boolSyntax.dest_eq(Thm.concl fg)
        val (x,y) = boolSyntax.dest_eq(Thm.concl xy)
        val fxgx  = Thm.AP_THM fg x
        val gxgy  = Thm.AP_TERM g xy
      in st_(OThm(Thm.TRANS fxgx gxgy)::os,st) end
    | f Assume        (st as {stack=OTerm t::os,...})           = st_(OThm(Thm.ASSUME t)::os,st)
    | f Axiom         (st as {stack=OTerm t::OList ts::os,...}) = st_(OThm(find_asm(unOTermls ts,t))::os,st)
    | f BetaConv      (st as {stack=OTerm t::os,...})           = st_(OThm(Thm.BETA_CONV t)::os,st)
    | f Cons          (st as {stack=OList t::h::os,...})        = st_(OList(h::t)::os,st)
    | f Const         (st as {stack=OName n::os,...})           = st_(OConst n::os,st)
    | f ConstTerm     (st as {stack=OType t::OConst c::os,...}) = st_(OTerm(find_const (c,t))::os,st)
    | f DeductAntisym (st as {stack=OThm t1::OThm t2::os,...})  = st_(OThm(DEDUCT_ANTISYM t1 t2)::os,st)
    | f Def           {stack=ONum k::x::os,dict,thms}           = {stack=x::os,dict=Map.insert(dict,k,x),thms=thms}
    | f DefineConst   (st as {stack=OTerm t::OName n::os,...})  = let
        val t = boolSyntax.mk_eq(Term.mk_var(n,Term.type_of t),t)
        val def = Definition.new_definition(n,t)
        handle Feedback.HOL_ERR _ => raise ERR "read_article" ("DefineConst "^n^" by "^Parse.term_to_string t^" failed")
      in st_(OThm def::OConst n::os,st) end
    | f DefineTypeOp  (st as {stack=OThm th::OList ls::OName rep::OName abs::OName n::os,...}) = let
        val ls = unONamels ls
        val sorted = Lib.sort (Lib.curry (Lib.equal LESS o String.compare)) ls
        val s = let fun f (a,a',s) = if a = a' then s else let
                      val a = Type.mk_vartype a
                      val a' = Type.mk_vartype a'
                      val op |-> = Lib.|-> infix |->
                    in (a |-> a')::(a' |-> a)::s end
                in ListPair.foldlEq f [] (ls,sorted) end
        val th = Thm.INST_TYPE s th
        val Pt = Thm.concl th
        val (P,t) = Term.dest_comb(Pt)
        val th = Thm.EXISTS(boolSyntax.mk_exists(t,Pt),t) th
        val tyax = Definition.new_type_definition(n,th)
        val th = Drule.define_new_type_bijections {name=n^"_repfns",ABS=abs,REP=rep,tyax=tyax}
        val th1 = Drule.SPEC_ALL (Thm.CONJUNCT1 th)
        val th2 = Drule.SPEC_ALL (Thm.CONJUNCT2 th)
      in st_(OThm th2::OThm  th1::OConst rep::OConst abs::OTypeOp n::os,st) end
    | f EqMp   (st as {stack=OThm fg::OThm f::os,...})     = st_(OThm(Thm.EQ_MP fg f)::os,st)
    | f Nil    st                                          = push(OList [],st)
    | f OpType (st as {stack=OList ls::OTypeOp t::os,...}) = st_(OType(find_type(t,ls))::os,st)
    | f Pop    (st as {stack=x::os,...})                   = st_(os,st)
    | f Ref    (st as {stack=ONum k::os,dict,...})         = st_(Map.find(dict,k)::os,st)
    | f Refl   (st as {stack=OTerm t::os,...})             = st_(OThm(Thm.REFL t)::os,st)
    | f Remove {stack=ONum k::os,dict,thms}                = let
        val (dict,x) = Map.remove(dict,k)
      in {stack=x::os,dict=dict,thms=thms} end
    | f Subst  (st as {stack=OThm th::OList[OList tys,OList tms]::os,...}) = let
        val tys = List.map (fn OList [OName a, OType t] => {redex=Type.mk_vartype a, residue=t}) tys
        val tms = List.map (fn OList [OVar v, OTerm t] => {redex=v, residue=t}) tms
        val th = Thm.INST_TYPE tys th
        val th = Thm.INST tms th
      in st_(OThm th::os,st) end
    | f Thm    {stack=OTerm c::OList ls::OThm th::os,dict,thms} = let
        val th = Thm.EQ_MP (Thm.ALPHA (Thm.concl th) c) th
        fun ft (OTerm h, th) = let
          val c = Thm.concl th
          val th = Thm.DISCH h th
          val c' = Thm.concl th
        in
          if Term.aconv c c' then
            Drule.ADD_ASSUM h th
          else let
            val (h',_) = boolSyntax.dest_imp c'
            val h'h = Thm.ALPHA h' h
            val th = Drule.SUBS_OCCS [([1],h'h)] th
          in Drule.UNDISCH th end
        end
        val th = List.foldl ft th ls
      in {stack=os,dict=dict,thms=th::thms} end
    | f TypeOp  (st as {stack=OName n::os,...})          = st_(OTypeOp n::os,st)
    | f Var     (st as {stack=OType t::OName n::os,...}) = st_(OVar(Term.mk_var(n,t))::os,st)
    | f VarTerm (st as {stack=OVar t::os,...})           = st_(OTerm t::os,st)
    | f VarType (st as {stack=OName n::os,...})          = st_(OType(Type.mk_vartype n)::os,st)
  fun stripnl s = let open Substring in string(trimr 1 (full s)) end
  fun loop x = case TextIO.inputLine file of
    NONE => x before TextIO.closeIn(file)
  | SOME line => loop (f (parse_line (stripnl line)) x handle Comment => x)
in #thms (loop {stack=[],dict=Map.mkDict(Int.compare),thms=[]}) end
end
