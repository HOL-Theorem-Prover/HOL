structure RawTheoryReader :> RawTheoryReader =
struct

open RawTheory_dtype

open HOLsexp
infixr 1 $
fun f $ x = f x
exception TheoryReader of string
val prsexp = HOLPP.pp_to_string 70 HOLsexp.printer

fun dtag s t =
    case dest_tagged s t of
        NONE => raise TheoryReader ("Expecting tag "^s)
      | SOME t => t

fun dtaglist tags t =
    case strip_list t of
        (_, SOME last) => raise TheoryReader
                                ("Extraneous at end of list: " ^prsexp t)
      | (els, NONE) =>
        let
          fun recurse tags els A =
              case (tags,els) of
                  ([],[]) => List.rev A
                | ([], e::_) => raise TheoryReader ("Extra list element: "^
                                                    prsexp e)
                | (t::_, []) => raise TheoryReader ("No data for tag " ^ t)
                | (t::ts, e::es) =>
                  let val e = dtag t e
                  in
                    recurse ts es (e::A)
                  end
        in
          recurse tags els []
        end

fun force s dec t =
    case dec t of
        NONE => raise TheoryReader ("Couldn't decode \""^s^"\": "^prsexp t)
      | SOME t => t

fun string_to_class "A" = SOME Axm
  | string_to_class "T" = SOME Thm
  | string_to_class "D" = SOME Def
  | string_to_class _ = NONE

val dec_thyname : raw_name decoder =
    map_decode
        (fn (s,n1,n2) => {thy = s, tstamp1 = n1, tstamp2 = n2}) $
        pair3_decode (string_decode,
                      Option.map Arbnum.fromString o string_decode,
                      Option.map Arbnum.fromString o string_decode)

(* ----------------------------------------------------------------------
    raw types and terms
   ---------------------------------------------------------------------- *)

fun raw_type_encode (TYV s) = String s
  | raw_type_encode (TYOP {opn,args}) = List(map Integer (opn::args))

fun raw_type_decode s =
    case string_decode s of
        SOME str => SOME (TYV str)
      | _ => case list_decode int_decode s of
                 NONE => NONE
               | SOME [] => NONE
               | SOME (opn::args) => SOME (TYOP {opn=opn, args = args})


fun raw_term_encode stm =
    case stm of
        TMV (s,i) => List[String s, Integer i]
      | TMC (i,j) => List[Integer i, Integer j]
      | TMAp(i,j) => List[Symbol "ap", Integer i, Integer j]
      | TMAbs(i,j) => List[Symbol "ab", Integer i, Integer j]
fun raw_term_decode s =
    let
      val (els, last) = strip_list s
    in
      if last <> NONE then NONE
      else
        case els of
            [String s, Integer i] => SOME (TMV (s,i))
          | [Integer i, Integer j] => SOME (TMC(i,j))
          | [Symbol "ap", Integer i, Integer j] => SOME (TMAp(i,j))
          | [Symbol "ab", Integer i, Integer j] => SOME (TMAbs(i,j))
          | _ => NONE
    end



(* ----------------------------------------------------------------------
    decoding raw theorems
   ---------------------------------------------------------------------- *)

fun decclass 0 = Axm
  | decclass 1 = Def
  | decclass 2 = Thm
  | decclass i = raise TheoryReader ("Bad theorem class: "^Int.toString i)

val dep_decode : int raw_dep decoder = let
  fun depmunge dilist =
      case dilist of
          [] => NONE
        | (n,[i]) :: rest => SOME{me = (n,i), deps = rest}
        | _ => NONE
in
  bind_decode
    (list_decode (pair_decode(int_decode, list_decode int_decode)))
    depmunge
end
val deptag_decode = pair_decode(dep_decode, list_decode string_decode)

fun munge_dep_strings lookup {me,deps} =
    let fun mfst (x,y) = (lookup x, y)
    in
      {me = mfst me, deps = map mfst deps}
    end

fun loc_decode ilist =
    case ilist of
        [] => SOME rlUnknown
      | exactp :: lnum :: path =>
        SOME (rlLocated {path = path, linenum = lnum, exact = exactp <> 0})
      | _ => NONE

val info_decode = let
  fun bind ilist =
      case ilist of
          ctag :: privtag :: rest =>
          Option.map (fn rl =>
                         {class = decclass ctag,
                          private = privtag <> 0,
                          loc = rl})
                     (loc_decode rest)
        | _ => NONE
in
  bind_decode (list_decode int_decode) bind
end

val thm_decode : int raw_thm decoder =
    let
      fun thmmunge(i,(di,tags),{class,private,loc},tms) =
          case tms of
              [] => NONE
            | c::hyps =>
              SOME {
                name = i, deps = di, tags = tags, concl = c,
                hyps = hyps,class=class,private=private,loc=loc
              }
    in
      Option.mapPartial thmmunge o
      pair4_decode (int_decode, deptag_decode, info_decode,
                    list_decode string_decode)
    end

fun munge_thm_strings lookup (rthm : int raw_thm) =
    let val {name,deps,tags,class,private,loc,concl,hyps} = rthm
    in
      {name = lookup name,
       deps = munge_dep_strings lookup deps,
       tags = tags,
       class = class,
       private = private,
       loc = loc,
       concl = concl,
       hyps = hyps}
    end

val dec_strings =
    map_decode Vector.fromList $
    tagged_decode "string-table" (list_decode string_decode)

val core_decode =
      map_decode
        (fn ((strt,idt,tyt,tmt), ((utys,ntys), (utms,ntms), thms)) =>
            {tables = {stringt = strt, idt = idt, typet = tyt, termt = tmt},
             exports = {
               unnamed_types = utys,
               named_types = ntys,
               unnamed_terms = utms,
               named_terms =
                 map (fn (n,t) => {name = n, encoded_term = t}) ntms,
               thms = map (munge_thm_strings (fn i => Vector.sub(strt,i))) thms
             }
        })
        (tagged_decode "core-data" (
            pair_decode(
              tagged_decode "tables" (
                pair4_decode(
                  dec_strings,
                  tagged_decode
                    "id-table"
                    (list_decode (pair_decode(int_decode, int_decode))),
                  tagged_decode "type-table" (list_decode raw_type_decode),
                  tagged_decode "term-table" (list_decode raw_term_decode)
                )
              ),
              tagged_decode "exports" (
                pair3_decode(
                  pair_decode( (* types *)
                    list_decode int_decode,
                    list_decode (pair_decode(string_decode, int_decode))
                  ),
                  pair_decode( (* terms *)
                    list_decode string_decode,
                    list_decode (pair_decode(string_decode, string_decode))
                  ),
                  (* theorems *) list_decode thm_decode
                )
              )
            )
          )
        )

fun decode s =
    let
      val raw_data = dtag "theory" s
      val (thyparentage, rest) =
          case raw_data of
              Cons(t1,t2) => (t1,t2)
            | _ => raise TheoryReader "No thy-parentage prefix"
      val (thy_data, parents_data) =
          case thyparentage of
              Cons p => p
            | _ => raise TheoryReader "thyparentage not a pair"
      val fullthy as {thy,...} = force "thyname" dec_thyname thy_data
      val parents = force "parents" (list_decode dec_thyname) parents_data
      val ({tables,exports}, incorporate_data, thydata_data) =
          force "toplevel_decode" (
            pair3_decode (
              core_decode,
              tagged_decode "incorporate" SOME,
              tagged_decode "loadable-thydata" SOME
            )
          ) rest
      val (new_types, new_consts) =
          force "incorporate_decode" (
            pair_decode(
              tagged_decode "incorporate-types" (
                list_decode (pair_decode (string_decode, int_decode))
              ),
              tagged_decode "incorporate-consts" (
                list_decode (pair_decode (string_decode, int_decode))
              )
            )
          ) incorporate_data
    in
      SOME {
        name = fullthy, parents = parents,
        tables = tables,
        exports = exports,
        newsig = {types = new_types, consts = new_consts},
        thydata = thydata_data
      }
    end

fun load_raw_thydata {thyname, path} : raw_theory =
    case decode (fromFile path) of
        NONE => raise TheoryReader ("Invalid file at "^path)
      | SOME v => v


end
