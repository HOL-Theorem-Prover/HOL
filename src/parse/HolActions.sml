structure HolActions =
struct 
exception mlyAction of int
local open HolHeader in
val actions = 
fn (i392,defaultPos,stack,
    (tyvars):arg) =>
case (i392,stack)
of (0,(_,(HolMlyValue.PTRM PTRM,PTRM1left,PTRM1right))::rest671) => let 
val result=HolMlyValue.START((PTM (make_preterm PTRM)))
 in (LRTable.NT 0,(result,PTRM1left,PTRM1right),rest671) end
| (1,(_,(HolMlyValue.TYPE TYPE,_,TYPE1right))::(_,(_,colon1left,_))::
rest671) => let val result=HolMlyValue.START((TY TYPE))
 in (LRTable.NT 0,(result,colon1left,TYPE1right),rest671) end
| (2,(_,(HolMlyValue.TYSPEC TYSPEC,_,TYSPEC1right))::(_,(_,colon1left,_))
::rest671) => let val result=HolMlyValue.START((TY_SPEC TYSPEC))
 in (LRTable.NT 0,(result,colon1left,TYSPEC1right),rest671) end
| (3,(_,(HolMlyValue.SUFFIX SUFFIX,SUFFIX1left,SUFFIX1right))::rest671)
 => let val result=HolMlyValue.PTRM((SUFFIX))
 in (LRTable.NT 1,(result,SUFFIX1left,SUFFIX1right),rest671) end
| (4,(_,(HolMlyValue.SUFFIX SUFFIX,_,SUFFIX1right))::(_,(HolMlyValue.APP APP
,APP1left,_))::rest671) => let val result=HolMlyValue.PTRM((
prec_parse (rev(APP)@[SUFFIX])))
 in (LRTable.NT 1,(result,APP1left,SUFFIX1right),rest671) end
| (5,(_,(HolMlyValue.PTRM PTRM2,_,PTRM2right))::_::(_,(HolMlyValue.PTRM 
PTRM1,_,_))::_::(_,(HolMlyValue.APP APP,APP1left,_))::rest671) => let 
val result=HolMlyValue.PTRM((make_cond tyvars (rev APP) PTRM1 PTRM2))
 in (LRTable.NT 1,(result,APP1left,PTRM2right),rest671) end
| (6,(_,(HolMlyValue.APP APP,APP1left,APP1right))::rest671) => let val 
result=HolMlyValue.PTRM((prec_parse (rev APP)))
 in (LRTable.NT 1,(result,APP1left,APP1right),rest671) end
| (7,(_,(HolMlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(HolMlyValue.AEXP AEXP,
_,_))::(_,(HolMlyValue.APP APP,APP1left,_))::rest671) => let val result=
HolMlyValue.APP(([make_constrained(prec_parse(rev(AEXP::APP)))TYPE]))
 in (LRTable.NT 2,(result,APP1left,TYPE1right),rest671) end
| (8,(_,(HolMlyValue.AEXP AEXP,_,AEXP1right))::(_,(HolMlyValue.APP APP,
APP1left,_))::rest671) => let val result=HolMlyValue.APP((AEXP::APP))
 in (LRTable.NT 2,(result,APP1left,AEXP1right),rest671) end
| (9,(_,(HolMlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(HolMlyValue.AEXP AEXP,
AEXP1left,_))::rest671) => let val result=HolMlyValue.APP((
[make_constrained AEXP TYPE]))
 in (LRTable.NT 2,(result,AEXP1left,TYPE1right),rest671) end
| (10,(_,(HolMlyValue.AEXP AEXP,AEXP1left,AEXP1right))::rest671) => let 
val result=HolMlyValue.APP(([AEXP]))
 in (LRTable.NT 2,(result,AEXP1left,AEXP1right),rest671) end
| (11,(_,(HolMlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=HolMlyValue.AEXP((make_atom tyvars ident))
 in (LRTable.NT 3,(result,ident1left,ident1right),rest671) end
| (12,(_,(HolMlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,
symbolic_ident1right))::rest671) => let val result=HolMlyValue.AEXP((
make_atom tyvars symbolic_ident))
 in (LRTable.NT 3,(result,symbolic_ident1left,symbolic_ident1right),
rest671) end
| (13,(_,(HolMlyValue.aq aq,aq1left,aq1right))::rest671) => let val 
result=HolMlyValue.AEXP((make_aq aq))
 in (LRTable.NT 3,(result,aq1left,aq1right),rest671) end
| (14,(_,(HolMlyValue.string_ string_,string_1left,string_1right))::
rest671) => let val result=HolMlyValue.AEXP((make_string string_))
 in (LRTable.NT 3,(result,string_1left,string_1right),rest671) end
| (15,(_,(_,eq1left,eq1right))::rest671) => let val result=
HolMlyValue.AEXP((make_atom tyvars "="))
 in (LRTable.NT 3,(result,eq1left,eq1right),rest671) end
| (16,(_,(_,dcolon1left,dcolon1right))::rest671) => let val result=
HolMlyValue.AEXP((make_atom tyvars "::"))
 in (LRTable.NT 3,(result,dcolon1left,dcolon1right),rest671) end
| (17,(_,(_,_,rparen1right))::(_,(HolMlyValue.PTRM PTRM,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=HolMlyValue.AEXP((PTRM))
 in (LRTable.NT 3,(result,lparen1left,rparen1right),rest671) end
| (18,(_,(_,_,rbracket1right))::(_,(HolMlyValue.LIST LIST,_,_))::(_,(_,
lbracket1left,_))::rest671) => let val result=HolMlyValue.AEXP((
make_list tyvars LIST))
 in (LRTable.NT 3,(result,lbracket1left,rbracket1right),rest671) end
| (19,(_,(_,_,rbrace1right))::(_,(HolMlyValue.LIST LIST,_,_))::(_,(_,
lbrace1left,_))::rest671) => let val result=HolMlyValue.AEXP((
make_set tyvars LIST))
 in (LRTable.NT 3,(result,lbrace1left,rbrace1right),rest671) end
| (20,(_,(_,_,rbrace1right))::(_,(HolMlyValue.PTRM PTRM2,_,_))::_::(_,(
HolMlyValue.PTRM PTRM1,_,_))::(_,(_,lbrace1left,_))::rest671) => let val 
result=HolMlyValue.AEXP((make_set_abs tyvars (PTRM1,PTRM2)))
 in (LRTable.NT 3,(result,lbrace1left,rbrace1right),rest671) end
| (21,(_,(HolMlyValue.PTRM PTRM2,_,PTRM2right))::_::(_,(HolMlyValue.PTRM 
PTRM1,_,_))::_::(_,(HolMlyValue.BVL BVL,_,_))::(_,(HolMlyValue.binder binder
,binder1left,_))::rest671) => let val result=HolMlyValue.SUFFIX((
rbinder tyvars binder BVL PTRM1 PTRM2))
 in (LRTable.NT 4,(result,binder1left,PTRM2right),rest671) end
| (22,(_,(HolMlyValue.PTRM PTRM,_,PTRM1right))::_::(_,(HolMlyValue.BVL BVL,_
,_))::(_,(HolMlyValue.binder binder,binder1left,_))::rest671) => let val 
result=HolMlyValue.SUFFIX((bind_term binder BVL PTRM))
 in (LRTable.NT 4,(result,binder1left,PTRM1right),rest671) end
| (23,(_,(HolMlyValue.PTRM PTRM,_,PTRM1right))::_::(_,(HolMlyValue.BINDL 
BINDL,_,_))::(_,(_,let_1left,_))::rest671) => let val result=
HolMlyValue.SUFFIX((make_let tyvars BINDL PTRM))
 in (LRTable.NT 4,(result,let_1left,PTRM1right),rest671) end
| (24,(_,(_,_,rparen1right))::(_,(HolMlyValue.BV BV,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=HolMlyValue.BV((BV))
 in (LRTable.NT 6,(result,lparen1left,rparen1right),rest671) end
| (25,(_,(HolMlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=HolMlyValue.BV((make_binding_occ tyvars ident))
 in (LRTable.NT 6,(result,ident1left,ident1right),rest671) end
| (26,(_,(HolMlyValue.aq aq,aq1left,aq1right))::rest671) => let val 
result=HolMlyValue.BV((make_aq_binding_occ tyvars aq))
 in (LRTable.NT 6,(result,aq1left,aq1right),rest671) end
| (27,(_,(HolMlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(HolMlyValue.BV BV,
BV1left,_))::rest671) => let val result=HolMlyValue.BV((
make_vstruct tyvars [BV] (SOME TYPE)))
 in (LRTable.NT 6,(result,BV1left,TYPE1right),rest671) end
| (28,(_,(_,_,rparen1right))::(_,(HolMlyValue.VSTRUCT VSTRUCT,_,_))::_::(
_,(HolMlyValue.BV BV,_,_))::(_,(_,lparen1left,_))::rest671) => let val 
result=HolMlyValue.BV((make_vstruct tyvars (BV::VSTRUCT)NONE))
 in (LRTable.NT 6,(result,lparen1left,rparen1right),rest671) end
| (29,(_,(HolMlyValue.BV BV,BV1left,BV1right))::rest671) => let val 
result=HolMlyValue.VSTRUCT(([BV]))
 in (LRTable.NT 7,(result,BV1left,BV1right),rest671) end
| (30,(_,(HolMlyValue.VSTRUCT VSTRUCT,_,VSTRUCT1right))::_::(_,(
HolMlyValue.BV BV,BV1left,_))::rest671) => let val result=
HolMlyValue.VSTRUCT((BV::VSTRUCT))
 in (LRTable.NT 7,(result,BV1left,VSTRUCT1right),rest671) end
| (31,(_,(HolMlyValue.PTRM PTRM,_,PTRM1right))::_::(_,(HolMlyValue.BVL BVL,
BVL1left,_))::rest671) => let val result=HolMlyValue.BINDL(([(BVL,PTRM)])
)
 in (LRTable.NT 8,(result,BVL1left,PTRM1right),rest671) end
| (32,(_,(HolMlyValue.BINDL BINDL,_,BINDL1right))::_::(_,(HolMlyValue.PTRM 
PTRM,_,_))::_::(_,(HolMlyValue.BVL BVL,BVL1left,_))::rest671) => let val 
result=HolMlyValue.BINDL(((BVL,PTRM)::BINDL))
 in (LRTable.NT 8,(result,BVL1left,BINDL1right),rest671) end
| (33,(_,(HolMlyValue.BVL BVL,_,BVL1right))::(_,(HolMlyValue.BV BV,BV1left,_
))::rest671) => let val result=HolMlyValue.BVL((BV::BVL))
 in (LRTable.NT 5,(result,BV1left,BVL1right),rest671) end
| (34,(_,(HolMlyValue.BV BV,BV1left,BV1right))::rest671) => let val 
result=HolMlyValue.BVL(([BV]))
 in (LRTable.NT 5,(result,BV1left,BV1right),rest671) end
| (35,rest671) => let val result=HolMlyValue.LIST(([]))
 in (LRTable.NT 10,(result,defaultPos,defaultPos),rest671) end
| (36,(_,(HolMlyValue.PTRM PTRM,PTRM1left,PTRM1right))::rest671) => let 
val result=HolMlyValue.LIST(([PTRM]))
 in (LRTable.NT 10,(result,PTRM1left,PTRM1right),rest671) end
| (37,(_,(HolMlyValue.LIST LIST,_,LIST1right))::_::(_,(HolMlyValue.PTRM PTRM
,PTRM1left,_))::rest671) => let val result=HolMlyValue.LIST((PTRM::LIST))
 in (LRTable.NT 10,(result,PTRM1left,LIST1right),rest671) end
| (38,(_,(HolMlyValue.TYPE TYPE2,_,TYPE2right))::_::(_,(HolMlyValue.TYPE 
TYPE1,TYPE1left,_))::rest671) => let val result=HolMlyValue.TYPE((
make_type_app("fun", [TYPE1, TYPE2])))
 in (LRTable.NT 11,(result,TYPE1left,TYPE2right),rest671) end
| (39,(_,(HolMlyValue.TYPE TYPE2,_,TYPE2right))::_::(_,(HolMlyValue.TYPE 
TYPE1,TYPE1left,_))::rest671) => let val result=HolMlyValue.TYPE((
make_type_app("sum", [TYPE1, TYPE2])))
 in (LRTable.NT 11,(result,TYPE1left,TYPE2right),rest671) end
| (40,(_,(HolMlyValue.TYPE TYPE2,_,TYPE2right))::_::(_,(HolMlyValue.TYPE 
TYPE1,TYPE1left,_))::rest671) => let val result=HolMlyValue.TYPE((
make_type_app("prod",[TYPE1, TYPE2])))
 in (LRTable.NT 11,(result,TYPE1left,TYPE2right),rest671) end
| (41,(_,(HolMlyValue.type_ident type_ident,_,type_ident1right))::(_,(
HolMlyValue.TYPE_ARG TYPE_ARG,TYPE_ARG1left,_))::rest671) => let val 
result=HolMlyValue.TYPE((make_type_app(type_ident, TYPE_ARG)))
 in (LRTable.NT 11,(result,TYPE_ARG1left,type_ident1right),rest671)
 end
| (42,(_,(HolMlyValue.BASIC BASIC,BASIC1left,BASIC1right))::rest671) => 
let val result=HolMlyValue.TYPE((BASIC))
 in (LRTable.NT 11,(result,BASIC1left,BASIC1right),rest671) end
| (43,(_,(HolMlyValue.type_ident type_ident,_,type_ident1right))::(_,(
HolMlyValue.TYPE_ARG TYPE_ARG,TYPE_ARG1left,_))::rest671) => let val 
result=HolMlyValue.TYPE_ARG(([make_type_app (type_ident,TYPE_ARG)]))
 in (LRTable.NT 12,(result,TYPE_ARG1left,type_ident1right),rest671)
 end
| (44,(_,(_,_,type_rparen1right))::(_,(HolMlyValue.TYPE_LIST TYPE_LIST,_,
_))::_::(_,(HolMlyValue.TYPE TYPE,_,_))::(_,(_,type_lparen1left,_))::
rest671) => let val result=HolMlyValue.TYPE_ARG((TYPE::TYPE_LIST))
 in (LRTable.NT 12,(result,type_lparen1left,type_rparen1right),rest671
) end
| (45,(_,(HolMlyValue.BASIC BASIC,BASIC1left,BASIC1right))::rest671) => 
let val result=HolMlyValue.TYPE_ARG(([BASIC]))
 in (LRTable.NT 12,(result,BASIC1left,BASIC1right),rest671) end
| (46,(_,(HolMlyValue.type_var_ident type_var_ident,type_var_ident1left,
type_var_ident1right))::rest671) => let val result=HolMlyValue.BASIC((
Type.mk_vartype type_var_ident))
 in (LRTable.NT 14,(result,type_var_ident1left,type_var_ident1right),
rest671) end
| (47,(_,(HolMlyValue.type_ident type_ident,type_ident1left,
type_ident1right))::rest671) => let val result=HolMlyValue.BASIC((
make_atomic_type(type_ident,!Globals.in_type_spec)))
 in (LRTable.NT 14,(result,type_ident1left,type_ident1right),rest671)
 end
| (48,(_,(HolMlyValue.aq aq,aq1left,aq1right))::rest671) => let val 
result=HolMlyValue.BASIC((Term.dest_ty_antiq aq))
 in (LRTable.NT 14,(result,aq1left,aq1right),rest671) end
| (49,(_,(_,_,type_rparen1right))::(_,(HolMlyValue.TYPE TYPE,_,_))::(_,(_
,type_lparen1left,_))::rest671) => let val result=HolMlyValue.BASIC((TYPE
))
 in (LRTable.NT 14,(result,type_lparen1left,type_rparen1right),rest671
) end
| (50,(_,(HolMlyValue.TYPE_LIST TYPE_LIST,_,TYPE_LIST1right))::_::(_,(
HolMlyValue.TYPE TYPE,TYPE1left,_))::rest671) => let val result=
HolMlyValue.TYPE_LIST((TYPE::TYPE_LIST))
 in (LRTable.NT 13,(result,TYPE1left,TYPE_LIST1right),rest671) end
| (51,(_,(HolMlyValue.TYPE TYPE,TYPE1left,TYPE1right))::rest671) => let 
val result=HolMlyValue.TYPE_LIST(([TYPE]))
 in (LRTable.NT 13,(result,TYPE1left,TYPE1right),rest671) end
| (52,(_,(HolMlyValue.CLAUSES CLAUSES,_,CLAUSES1right))::_::(_,(
HolMlyValue.TYID TYID,TYID1left,_))::rest671) => let val result=
HolMlyValue.TYSPEC(({ty_name=TYID,clauses=CLAUSES}))
 in (LRTable.NT 15,(result,TYID1left,CLAUSES1right),rest671) end
| (53,(_,(HolMlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=HolMlyValue.TYID((
Globals.in_type_spec := SOME ident; ident))
 in (LRTable.NT 16,(result,ident1left,ident1right),rest671) end
| (54,(_,(HolMlyValue.CLAUSE CLAUSE,CLAUSE1left,CLAUSE1right))::rest671)
 => let val result=HolMlyValue.CLAUSES((
[Parse_support.make_type_clause CLAUSE]))
 in (LRTable.NT 17,(result,CLAUSE1left,CLAUSE1right),rest671) end
| (55,(_,(HolMlyValue.CLAUSES CLAUSES,_,CLAUSES1right))::_::(_,(
HolMlyValue.CLAUSE CLAUSE,CLAUSE1left,_))::rest671) => let val result=
HolMlyValue.CLAUSES((make_type_clause CLAUSE::CLAUSES))
 in (LRTable.NT 17,(result,CLAUSE1left,CLAUSES1right),rest671) end
| (56,(_,(HolMlyValue.string_ string_,string_1left,string_1right))::
rest671) => let val result=HolMlyValue.CLAUSE((
{constructor=string_ , args=[]}))
 in (LRTable.NT 18,(result,string_1left,string_1right),rest671) end
| (57,(_,(HolMlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=HolMlyValue.CLAUSE(({constructor=ident, args=[]}))
 in (LRTable.NT 18,(result,ident1left,ident1right),rest671) end
| (58,(_,(HolMlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,
symbolic_ident1right))::rest671) => let val result=HolMlyValue.CLAUSE((
{constructor=symbolic_ident, args=[]}))
 in (LRTable.NT 18,(result,symbolic_ident1left,symbolic_ident1right),
rest671) end
| (59,(_,(HolMlyValue.CARGS CARGS,_,CARGS1right))::_::(_,(HolMlyValue.ident 
ident,ident1left,_))::rest671) => let val result=HolMlyValue.CLAUSE((
{constructor=ident,args = CARGS}))
 in (LRTable.NT 18,(result,ident1left,CARGS1right),rest671) end
| (60,(_,(HolMlyValue.CARGS CARGS,_,CARGS1right))::_::(_,(
HolMlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,_))::
rest671) => let val result=HolMlyValue.CLAUSE((
{constructor=symbolic_ident,args=CARGS}))
 in (LRTable.NT 18,(result,symbolic_ident1left,CARGS1right),rest671)
 end
| (61,(_,(HolMlyValue.CARGS CARGS,_,CARGS1right))::_::(_,(HolMlyValue.TYPE 
TYPE,TYPE1left,_))::rest671) => let val result=HolMlyValue.CARGS((
TYPE::CARGS))
 in (LRTable.NT 19,(result,TYPE1left,CARGS1right),rest671) end
| (62,(_,(HolMlyValue.TYPE TYPE,TYPE1left,TYPE1right))::rest671) => let 
val result=HolMlyValue.CARGS(([TYPE]))
 in (LRTable.NT 19,(result,TYPE1left,TYPE1right),rest671) end
| (63,(_,(HolMlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,
symbolic_ident1right))::rest671) => let val result=HolMlyValue.COMMA((
if (symbolic_ident = ",")
        then () else raise HOL_PARSE_ERR{function = "",
                                   message = "expecting a \",\" in varstruct"}
))
 in (LRTable.NT 9,(result,symbolic_ident1left,symbolic_ident1right),
rest671) end
| _ => raise (mlyAction i392)
end

val void = HolMlyValue.VOID

val extract = fn a => 
              (fn HolMlyValue.START x => x
                | _ => let exception ParseInternal
	               in raise ParseInternal 
                       end) a 
end
