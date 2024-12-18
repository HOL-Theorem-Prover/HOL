structure ThmAttribute :> ThmAttribute =
struct

  local open Symtab in end
  type attrfun = {name:string,attrname:string,args:string list,thm:Thm.thm} ->
                 unit
  type attrfuns = {localf: attrfun, storedf : attrfun}
  structure Map = Symtab

  val funstore = ref (Map.empty : attrfuns Map.table)
  fun all_attributes () = Map.keys (!funstore)
  fun is_attribute a = Map.defined (!funstore) a

  val reserved_words = ref ["induction"]
   (* "induction=name" is handled by tools/Holmake/HolParser, and so is basically
      invisible to all later code *)
  fun reserve_word s =
      if Lib.mem s (!reserved_words) then
        if !Globals.interactive then
          Feedback.HOL_WARNING "ThmAttribute" "reserve_word"
                               ("Word \"" ^ s ^ "\" already reserved")
        else
          raise Feedback.mk_HOL_ERR "ThmAttribute" "reserve_word"
                ("Word \"" ^ s ^ "\" already reserved")
      else if is_attribute s then
        raise Feedback.mk_HOL_ERR "ThmAttribute" "reserve_word"
              ("Word \"" ^ s ^ "\" already a standard attribute")
      else
        reserved_words := s :: (!reserved_words)

(*
 "unlisted", "nocompute", "schematic",
                            "tailrecursive"
*)

  fun okchar c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'"
  fun legal_attrsyntax s =
      s <> "" andalso
      Char.isAlpha (String.sub(s,0)) andalso
      CharVector.all okchar s

  fun register_attribute (kv as (s, f)) =
      let
        val _ = legal_attrsyntax s orelse
                raise Feedback.mk_HOL_ERR "ThmAttribute" "register_attribute"
                      ("Illegal attribute name: \""^s^"\"")
        val _ = not (Lib.mem s (!reserved_words)) orelse
                raise Feedback.mk_HOL_ERR "ThmAttribute" "register_attribute"
                      ("Name \""^s^"\" already reserved for other uses")

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

  fun at_attribute nm sel (arg as {name,attrname,args,thm}) =
      case Map.lookup (!funstore) attrname of
          NONE => raise Feedback.mk_HOL_ERR "ThmAttribute"
                        nm ("No such attribute: " ^ attrname)
        | SOME a => sel a arg
  val store_at_attribute = at_attribute "store_at_attribute" #storedf
  val local_attribute = at_attribute "local_attribute" #localf

  fun extract_attributes0 s = let
    open Substring
    val (bracketl,rest) = position "[" (full s)
  in
    if Theory.is_temp_binding s orelse isEmpty rest then (s,[])
    else let
      val (names,bracketr) = position "]" (slice(rest,1,NONE))
    in
      if size bracketr <> 1 then
        raise Feedback.mk_HOL_ERR "ThmAttribute" "extract_attributes"
              ("Malformed theorem-binding specifier: "^s)
      else
        (string bracketl,
         map Portable.remove_external_wspace
           (String.fields (fn c => c = #",") (string names)))
    end
  end

  fun dest_attribute_equality astr =
      let
        open Substring
        val (eql,rest) = position "=" (full astr)
        val key = Portable.remove_external_wspace (string eql)
      in
        if isEmpty rest then (key, [])
        else
          let val vs = string (slice(rest,1,NONE))
          in
            (key,
             map Portable.remove_external_wspace
                 (String.tokens Char.isSpace vs))
          end
      end

  fun extract_attributes s =
      let val (thmname,rawattrs) = extract_attributes0 s
          fun categorise (U,R,A) attrs =
              case attrs of
                  [] =>
                    {thmname = thmname, attrs = List.rev A, unknown = List.rev U,
                     reserved = List.rev R}
                | (a as (k,vs)) :: rest =>
                  if is_attribute k then categorise(U,R,a::A) rest
                  else if Lib.mem k (!reserved_words) then
                    categorise(U,a::R,A) rest
                  else categorise (a::U,R,A) rest
      in
        categorise([],[],[]) (map dest_attribute_equality rawattrs)
      end

  fun toString (s, attrs) =
      if null attrs then s
      else s ^ "[" ^ String.concatWith "," attrs ^ "]"

  fun insert_attribute {attr} s =
      let val (s0,attrs) = extract_attributes0 s
      in
        toString (s0, attr::attrs)
      end


end
