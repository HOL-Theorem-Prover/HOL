structure ThyDataSexp :> ThyDataSexp =
struct

open Feedback Term Thm Theory

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
  end

fun uptodate s =
  case s of
      Term tm => Term.uptodate_term tm
    | Type ty => Type.uptodate_type ty
    | Thm th => Theory.uptodate_thm th
    | List sl => List.all uptodate sl
    | _ => true

fun smerge sp =
  case sp of
      (List sl1, List sl2) => List (sl1 @ sl2)
    | (s1, s2) => List [Sym "merge", s1, s2]

fun sterms0 (s, acc) =
  case s of
      List sl => List.foldl sterms0 acc sl
    | Term tm => tm::acc
    | Thm th => concl th :: (hyp th @ acc)
    | Type ty => Term.mk_var("x", ty) :: acc
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

fun thmwrite tmw th =
    tagwrite (Thm.tag th) ^ listwrite tmw (concl th :: hyp th)
fun thmreader tmr =
  map Thm.disk_thm (tagreader >* listreader (map tmr StringData.reader))

fun write tmw s =
  case s of
      Int i => "I" ^ Coding.IntData.encode i
    | String s => "S" ^ Coding.StringData.encode s
    | List sl => "L" ^ listwrite (write tmw) sl
    | Term tm => "T" ^ tmw tm
    | Type ty => "Y" ^ tmw (Term.mk_var("x", ty))
    | Thm th => "H" ^ thmwrite tmw th
    | Sym s => "M" ^ StringData.encode s
    | Char c => "C" ^ CharData.encode c
    | Bool b => "B" ^ BoolData.encode b

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
        literal "B" >> map Bool BoolData.reader
  in
    core s
  end

structure LTD = LoadableThyData
fun new {thydataty, load, other_tds} =
  let
    val (todata, fromdata) =
        LTD.new{thydataty = thydataty, merge = smerge,
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
          NONE => ()
        | SOME d0 =>
            LTD.set_theory_data {thydataty = thydataty,
                                 data = todata (other_tds(d0,td))}

    fun hook (TheoryDelta.TheoryLoaded s) = onload s
      | hook td = hook0 td

    fun export s =
      (load {thyname = current_theory(), data = s};
       LTD.write_data_update {thydataty = thydataty, data = todata s})

  in
    register_hook ("ThmSetData.onload." ^ thydataty, hook);
    List.app onload (ancestry "-");
    {export = export, segment_data = segment_data}
  end

end
