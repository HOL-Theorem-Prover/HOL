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
       | SharedString of string
       | List of t list
       | Term of Term.term
       | Type of Type.hol_type
       | Thm of Thm.thm
       | Sym of string
       | Bool of bool
       | Char of char
       | Option of t option
       | KName of KernelSig.kernelname

fun pp_sexp typ tmp thp s =
  let
    open PP
    val pp = pp_sexp typ tmp thp
    fun safechar c = Char.isGraph c andalso c <> #"\""
  in
    case s of
        Int i => add_string (Int.toString i)
      | String s => add_string ("\"" ^ String.toString s ^ "\"")
      | SharedString s => add_string ("shared\"" ^ String.toString s ^"\"")
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
      | KName {Thy,Name} =>
          block CONSISTENT 1 [
            add_string "{",
            block CONSISTENT 0 [
              add_string "Thy = ", add_break (1, 2),
              add_string ("\"" ^ String.toString Thy ^ "\""),
              add_string ","
            ],
            add_break (1,0),
            block CONSISTENT 0 [
              add_string "Name = ", add_break(1,2),
              add_string ("\"" ^ String.toString Name ^ "\"")
            ], add_string "}"
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

    | (SharedString s1, SharedString s2) => String.compare(s1,s2)
    | (SharedString _, _) => LESS
    | (_, SharedString _) => GREATER

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
    | (Option _, _) => LESS
    | (_, Option _) => GREATER

    | (KName {Thy=th1,Name=n1}, KName{Thy=th2,Name=n2}) =>
      Lib.pair_compare (String.compare, String.compare) ((th1,n1), (th2,n2))


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

fun sterms0 (s, acc as (strs,tms)) =
  case s of
      List sl => List.foldl sterms0 acc sl
    | SharedString s => (s::strs,tms)
    | Term tm => (strs,tm::tms)
    | Thm th => (strs, concl th :: (hyp th @ tms))
    | Type ty => (strs, Term.mk_var("x", ty) :: tms)
    | Option (SOME s0) => sterms0 (s0, acc)
    | KName{Thy,Name} => (Thy::Name::strs,tms)
    | _ => acc
fun sterms s = sterms0 (s,([],[]))

infix >~ >> ||
fun (f >~ g) = Option.mapPartial g o f
fun (f >> g) = Option.map g o f
fun (f || g) = fn x => case f x of NONE => g x | res => res

val list_decode = HOLsexp.list_decode
val string_decode = HOLsexp.string_decode
val symbol_decode = HOLsexp.symbol_decode
val pair_decode = HOLsexp.pair_decode
val pair4_decode = HOLsexp.pair4_decode
val int_decode = HOLsexp.int_decode
val tagged_decode = HOLsexp.tagged_decode
fun dlwrite (s, ilist) =
    let open HOLsexp
    in
      pair_encode (String, list_encode Integer) (s,ilist)
    end
val dlreader = pair_decode (string_decode, list_decode int_decode)

fun tagwrite t =
  let
    val dep = Tag.dep_of t
    val (ocl, _) = Tag.dest_tag t
    val ((s,n), thydl) =
        case dep of
            Dep.DEP_SAVED p => p
          | _ => raise mk_HOL_ERR "ThyDataSexp" "tagwrite" "Bad dep"
    open HOLsexp
  in
    pair4_encode (String, Integer, list_encode dlwrite, list_encode String)
                 (s, n, thydl, ocl)
  end

val tagreader =
    let
      fun combine (s,n,dls,ocls) : Thm.depdisk * string list =
        (((s,n), dls), ocls)
    in
      pair4_decode (string_decode, int_decode, list_decode dlreader,
                    list_decode string_decode) >>
      combine
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
    HOLsexp.pair_encode (tagwrite, HOLsexp.list_encode (HOLsexp.String o tmw))
                        (Thm.tag th, concl th :: hyp th)
  end
fun thmreader tmr =
    pair_decode (tagreader, list_decode (string_decode >> tmr)) >> Thm.disk_thm

fun tag s enc x = HOLsexp.tagged_encode s enc x
fun write (wrt as {strings,terms}) s =
  case s of
      Int i => HOLsexp.Integer i
    | String s => HOLsexp.String s
    | SharedString s => tag "tag-str" (HOLsexp.Integer o strings) s
    | List sl => HOLsexp.list_encode (write wrt) sl
    | Term tm => tag "tag-tm" HOLsexp.String (terms tm)
    | Type ty => tag "tag-ty" HOLsexp.String (terms (Term.mk_var("x", ty)))
    | Thm th => tag "tag-th" (thmwrite terms) th
    | Sym s => HOLsexp.Symbol s
    | Char c => tag "tag-ch" (HOLsexp.Integer o Char.ord) c
    | Bool b => tag "tag-b" (fn b => if b then HOLsexp.Symbol "t"
                                     else HOLsexp.Symbol "f") b
    | Option NONE => tag "tag-none" (fn () => HOLsexp.Nil) ()
    | Option (SOME s) => tag "tag-some" (write wrt) s
    | KName {Thy,Name} => tag "tag-knm"
                              (HOLsexp.pair_encode (HOLsexp.Integer o strings,
                                                    HOLsexp.Integer o strings))
                              (Thy,Name)

fun reader (rd as {strings,terms}) s = (* necessary eta-expansion! *)
  let
    fun opt_chr i = if i < 256 then SOME (Char.chr i) else NONE
    val core =
        (int_decode >> Int) ||
        (string_decode >> String) ||
        (symbol_decode >> (fn s => if s = "nil" then List [] else Sym s)) ||
        (tagged_decode "tag-str" (int_decode >> strings >> SharedString)) ||
        (tagged_decode "tag-tm" string_decode >> terms >> Term) ||
        (tagged_decode "tag-ty" string_decode >> terms >> type_of >> Type) ||
        (tagged_decode "tag-th" (thmreader terms) >> Thm) ||
        (tagged_decode "tag-ch" int_decode >~ opt_chr >> Char) ||
        (tagged_decode "tag-b"
                       (fn d => if d = HOLsexp.Symbol "f" then SOME (Bool false)
                                else if d = HOLsexp.Symbol "t" then
                                  SOME (Bool true)
                                else NONE)) ||
        (tagged_decode "tag-some" (reader rd) >> SOME >> Option) ||
        (tagged_decode "tag-none" (fn d => if d = HOLsexp.Nil then
                                         SOME (Option NONE)
                                       else NONE)) ||
        (tagged_decode "tag-knm"
                       (pair_decode (int_decode >> strings,
                                     int_decode >> strings)) >~
                       (fn (thy,name) => SOME (KName {Thy=thy,Name=name}))) ||
        (list_decode (reader rd) >> List)
  in
    core s
  end

structure LTD = LoadableThyData
fun new {thydataty, load, other_tds, merge} =
  let
    val (todata, fromdata) =
        LTD.new{thydataty = thydataty, pp = bare_toString,
                merge = (fn (t1,t2) => merge {old = t1, new = t2}),
                terms = #2 o sterms, strings = #1 o sterms,
                read = reader, write = write}
    fun segment_data {thyname} =
      Option.join
        (Option.map fromdata
                    (LTD.segment_data{thy = thyname, thydataty = thydataty}))

    fun onload thyname =
      case segment_data{thyname = thyname} of
          NONE => load {thyname = thyname, data = NONE}
        | SOME s =>
            load {thyname = thyname, data = SOME s}

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
      (load {thyname = current_theory(), data = SOME s};
       LTD.write_data_update {thydataty = thydataty, data = todata s})

    fun set t =
        LTD.set_theory_data{thydataty = thydataty, data = todata t}

  in
    register_hook ("ThmSetData.onload." ^ thydataty, hook);
    List.app onload (ancestry "-");
    {export = export, segment_data = segment_data, set = set}
  end

fun bind NONE f = NONE
  | bind (SOME a) f = f a

fun mmap f [] = SOME []
  | mmap f (h::t) =
    bind (f h) (fn h' => bind (mmap f t) (fn t' => SOME (h'::t')))

fun list_decode d t =
    case t of
        List ts => mmap d ts
      | _ => NONE

fun mk_list m ts = List (map m ts)

fun string_decode (String s) = SOME s
  | string_decode _ = NONE

fun int_decode (Int i) = SOME i
  | int_decode _ = NONE

fun char_decode (Char c) = SOME c
  | char_decode _ = NONE

fun kname_decode (KName v) = SOME v
  | kname_decode _ = NONE

fun type_decode (Type ty) = SOME ty
  | type_decode _ = NONE

fun term_decode (Term tm) = SOME tm
  | term_decode _ = NONE

fun bool_decode (Bool b) = SOME b
  | bool_decode _ = NONE

fun fail t = NONE
fun first decoders =
    case decoders of
        [] => fail
      | d::ds => d || first ds

fun require_tag s t =
    case t of
        Sym s' => if s = s' then SOME () else NONE
      | _ => NONE

type 'a dec = t -> 'a option
type 'a enc = 'a -> t

fun option_encode enc NONE = Option NONE
  | option_encode enc (SOME x) = Option (SOME (enc x))
fun option_decode dec t =
    case t of
        Option NONE => SOME NONE
      | Option (SOME x) =>
          (case dec x of NONE => NONE | SOME v => SOME (SOME v))
      | _ => NONE


val pair_decode : 'a dec * 'b dec -> ('a*'b) dec =
    fn (d1,d2) => fn t =>
       case t of
           List [e1,e2] => Option.mapPartial
                             (fn r1 => Option.map (fn r2 => (r1,r2)) (d2 e2))
                             (d1 e1)
         | _ => NONE
fun pair_encode (e1,e2) (x,y) = List [e1 x, e2 y]

fun pair3_encode (e1,e2,e3) (x,y,z) = List [e1 x, e2 y, e3 z]
fun pair3_decode (d1,d2,d3) t =
    case t of
        List [t1, t2, t3] => (case (d1 t1, d2 t2, d3 t3) of
                                  (SOME x, SOME y, SOME z) => SOME (x,y,z)
                                | _ => NONE)
      | _ => NONE

fun pair4_encode (e1,e2,e3,e4) (a,b,c,d) = List [e1 a, e2 b, e3 c, e4 d]
fun pair4_decode (d1,d2,d3,d4) t =
    case t of
        List [t1,t2,t3,t4] =>
        (case (d1 t1, d2 t2, d3 t3, d4 t4) of
             (SOME a, SOME b, SOME c, SOME d) => SOME(a,b,c,d)
           | _ => NONE)
      | _ => NONE

fun tag_decode s d t =
    case t of
        List [Sym s', t0] => if s = s' then d t0 else NONE
      | List (Sym s' :: rest) => if s = s' then d (List rest) else NONE
      | _ => NONE

fun tag_encode s e x =
    case e x of
        List [t] => List [Sym s, List [t]]
      | List els => List (Sym s :: els)
      | t => List [Sym s, t]

end
