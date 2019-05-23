structure ThyDataSexp :> ThyDataSexp =
struct

open Feedback Term Thm Theory

val ERR = mk_HOL_ERR "ThyDataSexp"

val theory_debug_trace = get_tracefn "Theory.debug"

fun DPRINT f =
    if theory_debug_trace() <> 0 then
      print ("ThyDataSexp/DEBUG: " ^ f () ^ "\n")
    else ()

datatype t =
         Int of int
       | String of string
       | List of t list
       | Term of Term.term
       | Type of Type.hol_type
       | Thm of Thm.thm
       | Sym of string
       | Bool of bool
       | Char of char
       | Option of t option

fun pp_sexp typ tmp thp s =
  let
    open PP
    val pp = pp_sexp typ tmp thp
    fun safechar c = Char.isGraph c andalso c <> #"\""
  in
    case s of
        Int i => add_string (Int.toString i)
      | String s => add_string ("\"" ^ String.toString s ^ "\"")
      | List sl => block INCONSISTENT 1 (
                    add_string "(" ::
                    pr_list pp [add_break(1,0)] sl @
                    [add_string ")"]
                  )
      | Term tm => tmp tm
      | Type ty => typ ty
      | Thm th => thp th
      | Sym s => if CharVector.all safechar s then
                   add_string s
                 else add_string ("|\"" ^ String.toString s ^ "\"|")
      | Bool b => if b then add_string "'t" else add_string "'f"
      | Char c => add_string ("#\"" ^ Char.toString c ^ "\"")
      | Option NONE => add_string "NONE"
      | Option (SOME s) =>
          block INCONSISTENT 1 [
            add_string "(", add_string "SOME",
            add_break(1,0), pp s, add_string ")"
          ]
  end

val bare_toString =
    PP.pp_to_string 70 (pp_sexp (fn _ => PP.add_string "<type>")
                                (fn _ => PP.add_string "<term>")
                                (fn _ => PP.add_string "<thm>"))

fun uptodate s =
  case s of
      Term tm => Term.uptodate_term tm
    | Type ty => Type.uptodate_type ty
    | Thm th => Theory.uptodate_thm th
    | List sl => List.all uptodate sl
    | Option NONE => true
    | Option (SOME s0) => uptodate s0
    | _ => true

fun compare (s1, s2) =
  case (s1, s2) of
      (Int i1, Int i2) => Int.compare(i1,i2)
    | (Int _, _) => LESS
    | (_, Int _) => GREATER

    | (String s1, String s2) => String.compare(s1,s2)
    | (String _, _) => LESS
    | (_, String _) => GREATER

    | (List l1, List l2) => Lib.list_compare compare (l1, l2)
    | (List _, _) => LESS
    | (_, List _) => GREATER

    | (Term t1, Term t2) => Term.compare(t1,t2)
    | (Term _, _) => LESS
    | (_, Term _) => GREATER

    | (Type ty1, Type ty2) => Type.compare(ty1, ty2)
    | (Type _, _) => LESS
    | (_, Type _) => GREATER

    | (Thm th1, Thm th2) =>
      Lib.pair_compare (Lib.list_compare Term.compare, Term.compare)
                       ((hyp th1, concl th1), (hyp th2, concl th2))
    | (Thm _, _) => LESS
    | (_, Thm _) => GREATER

    | (Sym s1, Sym s2) => String.compare (s1, s2)
    | (Sym _, _) => LESS
    | (_, Sym _) => GREATER

    | (Bool b1, Bool b2) => Lib.bool_compare(b1, b2)
    | (Bool _, _) => LESS
    | (_, Bool _) => GREATER

    | (Char c1, Char c2) => Char.compare (c1, c2)
    | (Char _, _) => LESS
    | (_, Char _) => GREATER

    | (Option opt1, Option opt2) => Lib.option_compare compare (opt1, opt2)

fun update_alist (kv, es) =
  let
    val k = case kv of List[k,_] => k | _=> raise ERR "update_alist" "kv shape"
    fun recurse es =
      case es of
          [] => [kv]
        | (e as List [k',_])::rest =>
            if compare(k, k') = EQUAL then kv::rest
            else e :: recurse rest
        | _ => raise ERR "update_alist" "alist of bad shape"
  in
    recurse es
  end

fun alist_merge {old = s1, new = s2} =
  case (s1, s2) of
      (List dict, List updates) =>
      let
        val dict' = foldl update_alist dict updates
      in
        List dict'
      end
    | _ => raise ERR "alist_merge" "bad inputs"

fun append_merge {old, new} =
  case (old, new) of
      (List l1, List l2) => List (l1 @ l2)
    | _ => raise ERR "append_merge" "bad inputs"

fun sterms0 (s, acc) =
  case s of
      List sl => List.foldl sterms0 acc sl
    | Term tm => tm::acc
    | Thm th => concl th :: (hyp th @ acc)
    | Type ty => Term.mk_var("x", ty) :: acc
    | Option (SOME s0) => sterms0 (s0, acc)
    | _ => acc
fun sterms s = sterms0 (s, [])

open Coding
fun listwrite w l =
  IntData.encode (length l) ^ String.concat (List.map w l)
val >~ = op>-
infix 2 >~ >* >>
infix 0 ||
fun ntimes n r =
  if n <= 0 then return []
  else r >~ (fn h => ntimes (n-1) r >~ (fn t => return (h::t)))
fun listreader r =
  IntData.reader >~ (fn i => ntimes i r)

fun dlwrite (s, ilist) =
  StringData.encode s ^ listwrite IntData.encode ilist
val dlreader = StringData.reader >* listreader IntData.reader

fun tagwrite t =
  let
    val dep = Tag.dep_of t
    val (ocl, _) = Tag.dest_tag t
    val ((s,n), thydl) =
        case dep of
            Dep.DEP_SAVED p => p
          | _ => raise mk_HOL_ERR "ThyDataSexp" "tagwrite" "Bad dep"
  in
    StringData.encode s ^ IntData.encode n ^
    listwrite dlwrite thydl ^
    listwrite StringData.encode ocl
  end

val tagreader =
    let
      fun combine (s,(n,(dls,ocls))) : Thm.depdisk * string list =
        (((s,n), dls), ocls)
    in
      map combine
          (StringData.reader >* (
              IntData.reader >*
                (listreader dlreader >* listreader StringData.reader)))
    end

fun deps_saved th =
  case Tag.dep_of (Thm.tag th) of
      Dep.DEP_SAVED _ => true
    | _ => false

fun thmwrite tmw th0 =
  let
    val th = if deps_saved th0 then th0
             else Thm.save_dep (Theory.current_theory()) th0
  in
    tagwrite (Thm.tag th) ^
    listwrite (StringData.encode o tmw) (concl th :: hyp th)
  end
fun thmreader tmr =
  map Thm.disk_thm (tagreader >* listreader (map tmr StringData.reader))

fun write tmw s =
  case s of
      Int i => "I" ^ Coding.IntData.encode i
    | String s => "S" ^ Coding.StringData.encode s
    | List sl => "L" ^ listwrite (write tmw) sl
    | Term tm => "T" ^ StringData.encode (tmw tm)
    | Type ty => "Y" ^ StringData.encode (tmw (Term.mk_var("x", ty)))
    | Thm th => "H" ^ thmwrite tmw th
    | Sym s => "M" ^ StringData.encode s
    | Char c => "C" ^ CharData.encode c
    | Bool b => "B" ^ BoolData.encode b
    | Option NONE => "N"
    | Option (SOME s) => "S" ^ write tmw s

fun reader tmr s = (* necessary eta-expansion! *)
  let
    val core =
        literal "I" >> map Int (IntData.reader) ||
        literal "S" >> map String (StringData.reader) ||
        literal "L" >> map List (listreader (reader tmr)) ||
        literal "T" >> map (Term o tmr) (StringData.reader) ||
        literal "Y" >> map (Type o type_of o tmr) (StringData.reader) ||
        literal "H" >> map Thm (thmreader tmr) ||
        literal "M" >> map Sym StringData.reader ||
        literal "C" >> map Char CharData.reader ||
        literal "B" >> map Bool BoolData.reader ||
        literal "N" >> return (Option NONE) ||
        literal "S" >> map (Option o SOME) (reader tmr)
  in
    core s
  end

structure LTD = LoadableThyData
fun new {thydataty, load, other_tds, merge} =
  let
    val (todata, fromdata) =
        LTD.new{thydataty = thydataty, pp = bare_toString,
                merge = (fn (t1,t2) => merge {old = t1, new = t2}),
                terms = sterms, read = lift o reader, write = write}
    fun segment_data {thyname} =
      Option.join
        (Option.map fromdata
                    (LTD.segment_data{thy = thyname, thydataty = thydataty}))

    fun onload thyname =
      case segment_data{thyname = thyname} of
          NONE => ()
        | SOME s =>
            load {thyname = thyname, data = s}

    fun hook0 td =
      case segment_data {thyname = current_theory()} of
          NONE => DPRINT (fn _ => "No seg-data to update for " ^ thydataty ^
                                  "; return ()")
        | SOME d0 =>
          let
          in
            case other_tds(d0,td) of
                NONE => DPRINT (fn _ => "Seg-data for " ^ thydataty ^ " is " ^
                                        bare_toString d0 ^
                                        " but leaving it alone")
              | SOME newdata => (
                  DPRINT (fn _ => thydataty ^ " hook causes write of " ^
                                  bare_toString newdata);
                  LTD.set_theory_data {thydataty = thydataty,
                                       data = todata newdata}
              )
          end

    fun hook (TheoryDelta.TheoryLoaded s) = onload s
      | hook td = (DPRINT (fn _ => "Calling "^thydataty^"'s delta-hook");
                   hook0 td)

    fun export s =
      (load {thyname = current_theory(), data = s};
       LTD.write_data_update {thydataty = thydataty, data = todata s})

  in
    register_hook ("ThmSetData.onload." ^ thydataty, hook);
    List.app onload (ancestry "-");
    {export = export, segment_data = segment_data}
  end

end
