local open Location in
datatype Lab =
    INTlab of int
  | STRINGlab of string

fun mkTupleRow' n [] = []
  | mkTupleRow' n (x :: xs) =
      (INTlab n, x) :: mkTupleRow' (n+1) xs

fun mkTupleRow xs = mkTupleRow' 1 xs;

type QualifiedIdent =
{
  id: string,
  qual: string
};

type 'a global =
{
  info: 'a,               (* Description *)
  qualid: QualifiedIdent  (* Full name *)
};

type IdDesc =
{
  idLoc : Location,
  withOp : bool
};

type IdInfo = IdDesc global;

fun mkIdInfo (loc, qualid) withOp =
  { qualid = qualid,
    info = { idLoc=loc, withOp=withOp }}
;


type TyVar = IdInfo;

type 'a Row = (Lab * 'a) list; 

datatype Ty' =
    TYVARty of TyVar
  | RECty of Ty Row
  | CONty of Ty list * IdInfo
  | FNty of Ty * Ty
withtype Ty = Location * Ty';

fun tupleTy [t] = t
  | tupleTy ts =
      let open List
	  val loc = xxLR (hd ts) (last ts) 
      in
        (loc, RECty (mkTupleRow ts))
      end

datatype TyNameEqu = FALSEequ | TRUEequ | REFequ;

datatype ConBind = ConBind of IdInfo * Ty option

type TypBind = TyVar list * IdInfo * Ty

and TypDesc = TyVar list * IdInfo

and DatBind = TyVar list * IdInfo * ConBind list

and PrimValBind = IdInfo * Ty * int * string

type ValDesc = IdInfo * Ty;
type ExDesc = IdInfo * Ty option;

type LocString = Location * string;
type ModId = LocString;
type SigId = LocString;

datatype Spec' =
    VALspec of ValDesc list
  | PRIM_VALspec of PrimValBind list
  | TYPEDESCspec of TyNameEqu * TypDesc list
  | TYPEspec of TypBind list
  | DATATYPEspec of DatBind list * TypBind list option
  | DATATYPErepspec of IdInfo * IdInfo
  | EXCEPTIONspec of ExDesc list
  | LOCALspec of Spec * Spec
  | OPENspec of string list
  | INCLUDEspec of string list
  | EMPTYspec
  | SEQspec of Spec * Spec
  | STRUCTUREspec of ModDesc list
and ModDesc = MODDESCmoddesc of ModId * SigExp
and SigExp' = SIGIDsigexp of SigId
withtype Spec = Location * Spec'
and SigExp = Location * SigExp';

datatype Sig = 
    NamedSig of {locsigid : LocString, specs : Spec list}
  | AnonSig of Spec list;

end
