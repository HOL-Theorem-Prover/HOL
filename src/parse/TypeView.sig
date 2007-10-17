signature TypeView =
sig

  type kind = Kind.kind
  type hol_type = Type.hol_type
  type tyvar = Type.tyvar
  datatype TypeView = TyV_Var of tyvar
                    | TyV_Const of {Thy:string,Tyop:string,Kind:kind,Rank:int}
                    | TyV_App of hol_type * hol_type
                    | TyV_Abs of tyvar * hol_type
                    | TyV_All of tyvar * hol_type

  val fromType : hol_type -> TypeView
  val toType : TypeView -> hol_type

end
