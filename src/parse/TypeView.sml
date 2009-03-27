structure TypeView :> TypeView =
struct

open Type

  datatype TypeView = TyV_Var of tyvar
                    | TyV_Const of {Thy:string,Tyop:string,Kind:kind,Rank:int}
                    | TyV_App of hol_type * hol_type
                    | TyV_Abs of tyvar * hol_type
                    | TyV_All of tyvar * hol_type

  fun fromType ty =
      if is_vartype ty then TyV_Var (dest_vartype_opr ty)
      else if is_con_type ty then TyV_Const (dest_thy_con_type ty)
      else if is_app_type ty then TyV_App (dest_app_type ty)
      else if is_abs_type ty then let
          val (tyv, ty) = dest_abs_type ty
        in
          TyV_Abs (dest_vartype_opr tyv, ty)
        end
      else if is_univ_type ty then let
          val (tyv,ty) = dest_univ_type ty
        in
          TyV_All (dest_vartype_opr tyv, ty)
        end
      else raise Feedback.mk_HOL_ERR "TypeView" "fromType"
            ("not a var, const, app, abs, or univ type: " ^ Type.type_to_string ty)

  fun toType tyv =
      case tyv of
        TyV_Var tyv => mk_vartype_opr tyv
      | TyV_Const r => mk_thy_con_type { Thy = #Thy r, Tyop = #Tyop r, Kind = #Kind r, Rank = #Rank r }
      | TyV_App (ty1, ty2) => mk_app_type (ty1, ty2)
      | TyV_Abs (tyv, ty) => mk_abs_type (mk_vartype_opr tyv, ty)
      | TyV_All (tyv, ty) => mk_univ_type (mk_vartype_opr tyv, ty)

end;

