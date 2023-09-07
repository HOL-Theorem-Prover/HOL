structure ThmAttribute :> ThmAttribute =
struct

  local open Symtab in end
  type attrfun = {name:string,attrname:string,thm:Thm.thm} -> unit
  type attrfuns = {localf: attrfun, storedf : attrfun}
  structure Map = Symtab

  val funstore = ref (Map.empty : attrfuns Map.table)

  val reserved_attrnames = ["local", "unlisted", "nocompute", "schematic",
                            "notuserdef", "allow_rebind"]

  fun okchar c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'"
  fun illegal_attrname s = Lib.mem s reserved_attrnames orelse
                           String.isPrefix "induction=" s orelse
                           s = "" orelse
                           not (Char.isAlpha (String.sub(s,0))) orelse
                           not (CharVector.all okchar s)

  fun register_attribute (kv as (s, f)) =
      let
        val _ = not (illegal_attrname s) orelse
                raise Feedback.mk_HOL_ERR "ThmAttribute" "register_attribute"
                      ("Illegal attribute name: \""^s^"\"")
        val oldm = !funstore
        val newm =
            case Map.lookup oldm s of
                NONE => Map.update kv oldm
              | SOME _ => (
                  Feedback.HOL_WARNING "ThmAttribute"
                    "register_attribute"
                    ("Replacing existing attribute functions for "^s);
                  Map.update kv oldm
                )
      in
        funstore := newm
      end

  fun all_attributes () = Map.keys (!funstore)
  fun is_attribute a = Map.defined (!funstore) a
  fun at_attribute nm sel (arg as {name,attrname,thm}) =
      case Map.lookup (!funstore) attrname of
          NONE => raise Feedback.mk_HOL_ERR "ThmAttribute"
                        nm ("No such attribute: " ^ attrname)
        | SOME a => sel a arg
  val store_at_attribute = at_attribute "store_at_attribute" #storedf
  val local_attribute = at_attribute "local_attribute" #localf

  fun extract_attributes s = let
    open Substring
    val (bracketl,rest) = position "[" (full s)
  in
    if Theory.is_temp_binding s orelse isEmpty rest then (s,[])
    else let
      val (names,bracketr) = position "]" (slice(rest,1,NONE))
    in
      if size bracketr <> 1 then
        raise Feedback.mk_HOL_ERR "boolLib" "resolve_storename"
              ("Malformed theorem-binding specifier: "^s)
      else
        (string bracketl, String.fields (fn c => c = #",") (string names))
    end
  end

  fun toString (s, attrs) =
      if null attrs then s
      else s ^ "[" ^ String.concatWith "," attrs ^ "]"

  fun insert_attribute {attr} s =
      let val (s0,attrs) = extract_attributes s
      in
        toString (s0, attr::attrs)
      end


end
