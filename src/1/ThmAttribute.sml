structure ThmAttribute :> ThmAttribute =
struct

  local open Symtab in end
  type attrfun = {name:string,attrname:string,thm:Thm.thm} -> unit
  structure Map = Symtab

  val funstore = ref (Map.empty : attrfun Map.table)

  fun register_attribute (kv as (s, f)) =
      let
        val oldm = !funstore
        val newm =
            case Map.lookup oldm s of
                NONE => Map.update kv oldm
              | SOME _ => (
                  Feedback.HOL_WARNING "ThmAttribute"
                    "register_attribute"
                    ("Replacing existing attribute function for "^s);
                  Map.update kv oldm
                )
      in
        funstore := newm
      end

  fun store_at_attribute (arg as {name,attrname,thm}) =
      case Map.lookup (!funstore) attrname of
          NONE => raise Feedback.mk_HOL_ERR "ThmAttribute"
                        "store_at_attribute"
                        ("No such attribute: " ^ attrname)
        | SOME f => f arg

end
