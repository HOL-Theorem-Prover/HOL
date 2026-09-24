structure HOLFlags :> HOLFlags =
struct

val ERR = Feedback.mk_HOL_ERR "HOLFlags"
val WARN = Feedback.HOL_WARNING "HOLFlags"

(* ----------------------------------------------------------------------
    Traces & numeric flags.

    When called a "trace" such flags tend to govern the verbosity of
    some output, often diagnostic: the higher the setting, the more
    verbosely the tool behaves.

    Other flags tweak the behaviour of tools, e.g., turning features
    on and off. These are also, somewhat inaccurately, called "traces"
    in the code.
   ---------------------------------------------------------------------- *)

type trace_name = {group:string, name:string}
type ctxt = Context.t

fun trace_name_toString {group,name} =
    if group = "" then name else group ^ "." ^ name

fun str2name s =
    let val (pfx,sfx) = Substring.position "." (Substring.full s)
    in
      if Substring.isEmpty sfx then
        {group = "", name = s}
      else
        {group = Substring.string pfx,
         name = Substring.string (Substring.slice(sfx,1,NONE))}
    end


type trace_record = {
  aliases : trace_name list,
  default: int,
  current : int,
  maximum: int
}

datatype TI = TR of trace_record | ALIAS of trace_name

(* use "kernel names" as a cheaty way to get pairs of strings as keys *)
type trace_map = TI KNametab.table

val tmap_slot = Context.Data.new {
      name = "HOLFlags",
      empty = KNametab.empty : trace_map,
      pp = fn _ => "<a trace_map>"
    }

fun gen_find_record (tmap : trace_map) (tnm as {group,name})  =
    case KNametab.lookup tmap {Thy=group,Name=name} of
        NONE => NONE
      | SOME (TR tr) => SOME (tnm, tr)
      | SOME (ALIAS a) => gen_find_record tmap a

fun global_tmap() = Context.Data.get tmap_slot (Context.snapshot())

fun find_record arg = gen_find_record (global_tmap()) arg


fun quote t = String.concat ["\"", trace_name_toString t, "\""]
fun kquote {Thy,Name} = trace_name_toString

local
   fun err f l = raise ERR f (String.concat l)
in
   fun registered_err f nm = err f ["No trace ", quote nm, " is registered"]

   fun gen_set_value tnm v tmap =
       if v < 0 then raise ERR "gen_set_value" "No trace can become negative"
       else
         case gen_find_record tmap tnm of
             NONE => raise ERR "gen_set_value" ("No such trace: "^quote tnm)
           | SOME ({group,name}, {maximum, current, default, aliases}) =>
             (if maximum > 0 andalso v > maximum then
                raise ERR "gen_set_value"
                      (Int.toString v ^ " greater than permitted maximum " ^
                       Int.toString maximum)
              else ();
              KNametab.update (
                {Name = name, Thy = group},
                TR {
                  maximum=maximum, current = v,
                  default = default, aliases = aliases
                }
              ) tmap
             )
end

fun gen_set_trace_C (tnm,value) =
    Context.Data.update tmap_slot (gen_set_value tnm value)

fun get_ttrace nm =
   case find_record nm of
      NONE => registered_err "get_tracefn" nm
    | SOME (_, r) => #current r

fun set_ttrace tnm newvalue =
    Context.Data.modify tmap_slot (gen_set_value tnm newvalue)
fun set_trace nm v = set_ttrace (str2name nm) v

fun gen_create_trace (tnm as {group, name}, {max, initial}) tmap =
    let
      val _ = initial >= 0 orelse raise ERR "gen_create_trace"
                                        "Can't have trace values less than zero"
      val _ = max >= 0 orelse raise ERR "gen_create_trace"
                                    "Can't have maximum values less than zero"
      val tnm = {group = group, name = name}
      val knm = {Thy = group, Name = name}
    in
      case KNametab.lookup tmap knm of
          NONE => ()
        | SOME _ =>
          WARN "gen_create_trace" ("Replacing trace with name " ^ quote tnm);
      KNametab.update
        (knm, TR{aliases = [],
                 default = initial,
                 current = initial,
                 maximum = max})
        tmap
    end

fun create_trace arg = (
  Context.Data.modify tmap_slot (gen_create_trace arg);
  {get = fn () => get_ttrace (#1 arg), set = set_ttrace (#1 arg)}
)

fun gen_register_alias_trace {original = original as {group,name}, alias} tmap =
  if original = alias then (
    WARN "register_alias_trace" "original and alias are equal; doing nothing";
    tmap
  ) else
    case gen_find_record tmap original of
        NONE => raise ERR "register_alias_trace"
                      ("Original trace: "^quote original^" doesn't exist")
      | SOME (_, {aliases,maximum,default,current}) =>
        let
          val alias_k = {Thy = #group alias, Name = #name alias}
          val original_k = {Thy=group,Name=name}
          val aliases' =
              if List.exists (fn s => s = alias) aliases then aliases
              else alias::aliases
          val recd = {aliases = aliases', maximum = maximum, default = default,
                      current = current}
          val record_alias = KNametab.update (original_k, TR recd) tmap
          val mk_alias =
              KNametab.update (alias_k, ALIAS original) record_alias
        in
          case KNametab.lookup record_alias alias_k of
              NONE => ()
            | SOME (ALIAS a) =>
                if a = original then ()
                else WARN "register_alias_trace"
                          ("Replacing existing alias binding for "^
                           quote alias ^ " |-> " ^ quote a)
            | SOME (TR _) =>
                raise ERR "register_alias_trace"
                      ("Cannot replace existing genuine trace info for "^
                       quote alias);
          mk_alias
        end

fun register_alias_trace arg =
    Context.Data.modify tmap_slot (gen_register_alias_trace arg)

datatype trace_elt =  (* for prettyprinting *)
  TraceElt of
    {name : trace_name, aliases : trace_name list,
     trace_level : int, default : int, max : int}


fun pp_trace_elt (TraceElt{name,aliases,trace_level,default,max}) =
    let open HOLPP
        fun pp_tname tnm = add_string (trace_name_toString tnm)
        val comma_space = [add_string",",add_break(1,0)]
        fun interval a b =
            map add_string ["[", Int.toString a, "..", Int.toString b, "]"]
        val alias_list = pr_list pp_tname comma_space aliases
        val name_plus_aliases =
            if null aliases then
               pp_tname name
            else block CONSISTENT 2
                   ([pp_tname name, add_break(0,0), add_string "["]
                    @ alias_list @ [add_string "]"])
    in block INCONSISTENT 2
         [name_plus_aliases, add_string ":", add_break(1,0),
          add_string (Int.toString trace_level), add_break(1,0),
          block CONSISTENT 0 (interval 0 max)]
    end

fun traces () =
   let
      fun foldthis ({Thy,Name}, ti) acc =
        case ti of
            ALIAS _ => acc
          | TR {current, default, maximum, aliases} =>
            TraceElt {name = {group=Thy,name=Name},
                      aliases = aliases,
                      trace_level = current,
                      default = default,
                      max = maximum} :: acc
   in
     KNametab.fold_rev foldthis (global_tmap()) []
   end

fun set_btrace nm b =
    set_ttrace nm (if b then 1 else 0)

fun get_btrace nm = get_ttrace nm = 1

fun create_btrace (tnm as {group,name}, initb) = (
  create_trace (tnm, {initial=if initb then 1 else 0, max=1});
  {get = fn () => get_btrace tnm, set = set_btrace tnm}
)



fun reset_trace nm =
    let val tnm = str2name nm
    in
      case find_record tnm of
          SOME (_, {default, ...}) => set_trace nm default
        | NONE => registered_err "reset_trace" tnm
    end

fun gen_reset_traces tmap =
    let
      fun foldthis (k, ti) =
          case ti of
              ALIAS _ => KNametab.update (k, ti)
            | TR{current,default,maximum,aliases} =>
              KNametab.update(k,
                              TR {current = default,
                                  maximum = maximum,
                                  aliases = aliases,
                                  default = default})
    in
      KNametab.fold foldthis tmap KNametab.empty
    end

fun reset_traces () =
    Context.Data.modify tmap_slot gen_reset_traces

val current_trace = get_ttrace o str2name

fun with_traces flags f x =
    let
      val base = global_tmap()
      fun foldthis ((nm,v), m) = gen_set_value (str2name nm) v m
      val tempv = List.foldl foldthis base flags
  in
     Context.Data.with_slot_value tmap_slot tempv f x
  end

fun trace flag = with_traces [flag]
(*
  val show_types              : bool ref
  val show_types_verbosely    : bool ref
  val show_numeral_types      : bool ref
  val show_assums             : bool ref
  val show_tags               : bool ref
  val show_axioms             : bool ref
  val show_scrub              : bool ref
  val linewidth               : int ref
  val max_print_depth         : int ref
  val max_print_length        : int ref
*)

val _ = List.map (fn gnm => create_btrace({group = "PP", name = gnm}, false)) [
      "types", "show_numeral_types", "show_assums", "show_tags", "show_axioms",
      "show_scrub"
    ]

(*
val linewidth_tnm = {group = "", name = "linewidth"}

val {get=linewidth,set=set_linewidth} =
    create_trace(linewidth_tnm, {max = 0, initial = 70})
*)

fun set_linewidth i = (Globals.linewidth := i)
fun linewidth () = !Globals.linewidth

fun mkboolreporter nm () = get_btrace {group="PP",name=nm}

val show_tags = mkboolreporter "show_tags"
val show_axioms = mkboolreporter "show_axioms"
val show_assums = mkboolreporter "show_assums"


end
