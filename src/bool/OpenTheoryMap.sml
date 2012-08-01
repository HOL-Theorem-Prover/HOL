structure OpenTheoryMap :> OpenTheoryMap =
struct
  val ERR = Feedback.mk_HOL_ERR "OpenTheoryMap"
  structure Map = Redblackmap
  type thy_tyop  = {Thy:string,Tyop:string}
  type thy_const = {Thy:string,Name:string}
  type otname    = string list * string
  type 'a to_ot  = ('a,otname) Map.dict
  type 'a from_ot= (otname,'a) Map.dict
  local open Lib val s = String.compare in
    val thy_tyop_cmp  : thy_tyop cmp  = lex_cmp (s,s) (#Tyop,#Thy)
    val thy_const_cmp : thy_const cmp = lex_cmp (s,s) (#Name,#Thy)
    val otname_cmp = pair_compare (list_compare s, s)
  end
  val the_tyop_to_ot   = ref (Map.mkDict thy_tyop_cmp)
  val the_tyop_from_ot = ref (Map.mkDict otname_cmp)
  val the_const_to_ot  = ref (Map.mkDict thy_const_cmp)
  val the_const_from_ot= ref (Map.mkDict otname_cmp)
  fun tyop_to_ot_map()   = !the_tyop_to_ot
  fun tyop_from_ot_map() = !the_tyop_from_ot
  fun const_to_ot_map()  = !the_const_to_ot
  fun const_from_ot_map()= !the_const_from_ot
  val component = String.translate (fn #"." => "\\." | #"\"" => "\\\"" | #"\\" => "\\\\" | c => String.str c)
  fun otname_to_string (sl,s) = foldl (fn (c,s) => String.concat [component c, ".", s]) (component s) (rev sl)
  val string_to_otname = let
    fun add c [] = [[c]]
      | add c (h::t) = ((c::h)::t)
    fun f [] acc = acc
      | f (#"\\" :: c :: cs) acc = f cs (add c acc)
      | f (#"." :: cs) acc = f cs ([]::acc)
      | f (c :: cs) acc = f cs (add c acc)
    open String
  in fn s => let
    val cs = List.map (implode o rev) (f (explode s) [])
  in (rev (tl cs), hd cs) end
    handle _ => raise ERR "string_to_otname" (s^" does not represent an OpenTheory name")
  end
  val ots = otname_to_string val sto = string_to_otname
  val unwanted = fn (["Unwanted"],_) => true | _ => false (* hack for making the map one-way for the Unwanted namespace *)
  type deltas = ({name:otname,tyop : thy_tyop }list*
                 {name:otname,const: thy_const}list)
  val read_deltas = let
    open Coding infix >* infix >->
    val r = StringData.reader
    val r = (r >* (r >* r))
    val r1 = many (map (fn (name,(Thy,Tyop)) => {name=sto name,tyop ={Thy=Thy,Tyop=Tyop}}) r)
    val r2 = many (map (fn (name,(Thy,Name)) => {name=sto name,const={Thy=Thy,Name=Name}}) r)
  in (r1 >-> literal " ") >* r2 end
  fun write_deltas (l1,l2) = let
    open Coding
    val e = StringData.encode
    fun f ({name,const={Thy,Name}},s) = String.concat[e (ots name),e Thy,e Name,s]
    val s2 = List.foldl f "" l2
    fun f ({name,tyop ={Thy,Tyop}},s) = String.concat[e (ots name),e Thy,e Tyop,s]
  in List.foldl f (" "^s2) l1 end
  val tyname = "OpenTheoryMap"
  val (mk,dest) = Theory.LoadableThyData.new {thydataty = tyname,
                                              merge = fn((a,b),(c,d))=>(c@a,d@b),
                                              read = Coding.lift read_deltas,
                                              write = write_deltas}
  fun tyopToString  {Thy,Tyop} = "(Thy="^Thy^",Tyop="^Tyop^")"
  fun constToString {Thy,Name} = "(Thy="^Thy^",Name="^Name^")"
  fun temp_OpenTheory_tyop_name0 src {tyop,name} = let
    val _ = case Map.peek(!the_tyop_to_ot,tyop) of NONE => ()
            | SOME oldn => if oldn = name then () else
              Feedback.HOL_WARNING "OpenTheoryMap" "OpenTheory_tyop_name"
                (src^" overrides "^tyopToString tyop^
                 " (was \""^(ots oldn)^"\"; now \""^(ots name)^"\"")
  in
    the_tyop_to_ot   := Map.insert(!the_tyop_to_ot  ,tyop,name);
    the_tyop_from_ot := Map.insert(!the_tyop_from_ot,name,tyop)
  end
  val temp_OpenTheory_tyop_name = temp_OpenTheory_tyop_name0 "OpenTheory_tyop_name call"
  fun temp_OpenTheory_const_name0 src {const,name} = let
    val _ =
        case Map.peek(!the_const_to_ot,const) of
          NONE => ()
        | SOME oldn =>
          if oldn = name then ()
          else
            Feedback.HOL_WARNING
                "OpenTheoryMap" "OpenTheory_const_name"
                (String.concat [src, " overrides ", constToString const,
                                " (was \"", ots oldn, "\"; now \"", ots name,
                                "\""])
  in
    the_const_to_ot   := Map.insert(!the_const_to_ot  ,const,name);
    if unwanted name then () else the_const_from_ot := Map.insert(!the_const_from_ot,name,const)
  end
  val temp_OpenTheory_const_name = temp_OpenTheory_const_name0 "OpenTheory_const_name call"
  fun OpenTheory_tyop_name r = let in
    temp_OpenTheory_tyop_name r;
    Theory.LoadableThyData.write_data_update {thydataty = tyname,
                                              data = mk ([r],[])}
  end
  fun OpenTheory_const_name r = let in
    temp_OpenTheory_const_name r;
    Theory.LoadableThyData.write_data_update {thydataty = tyname,
                                              data = mk ([],[r])}
  end
  fun onload thyname =
    case Theory.LoadableThyData.segment_data {thy = thyname, thydataty = tyname} of
      NONE => ()
    | SOME t => let
        val (l1,l2) = valOf (dest t)
        handle Option => ([],[]) before
                         Feedback.HOL_WARNING "OpenTheoryMap" "onload"
                          ("Data for theory "^thyname^" appears corrupted.")
        val src = "Theory "^thyname
      in
        List.app (temp_OpenTheory_tyop_name0  src) l1;
        List.app (temp_OpenTheory_const_name0 src) l2
      end
  val _ = map onload (Theory.ancestry "-")
  fun otmap td = let
    open TheoryDelta
  in
    case td of
      TheoryLoaded s => onload s
    | _ => ()
  end
  val _ = Theory.register_hook ("OpenTheory.onload", otmap)
end
