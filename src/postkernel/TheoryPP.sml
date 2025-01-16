(*---------------------------------------------------------------------------*
 *                                                                           *
 *            HOL theories interpreted by SML structures.                    *
 *                                                                           *
 *---------------------------------------------------------------------------*)

structure TheoryPP :> TheoryPP =
struct

type thm      = Thm.thm;
type term     = Term.term
type hol_type = Type.hol_type
type shared_writemaps = {strings : string -> int, terms : Term.term -> string}
type shared_readmaps = {strings : int -> string, terms : string -> Term.term}
type thminfo = DB_dtype.thminfo
type struct_info_record = {
   theory      : string*Arbnum.num*Arbnum.num,
   parents     : (string*Arbnum.num*Arbnum.num) list,
   types       : (string*int) list,
   constants   : (string*hol_type) list,
   all_thms    : (string * thm * thminfo) list,
   struct_ps   : (unit -> PP.pretty) option list,
   struct_pcps : (unit -> PP.pretty) list,
   mldeps      : string list,
   thydata     : string list * Term.term list *
                 (string,shared_writemaps -> HOLsexp.t)Binarymap.dict
 }

open Feedback Lib Portable Dep;

val ERR = mk_HOL_ERR "TheoryPP";

val temp_binding_pfx = "@temp"
val is_temp_binding = String.isPrefix temp_binding_pfx
fun temp_binding s = temp_binding_pfx ^ s
fun dest_temp_binding s =
  if is_temp_binding s then
    String.extract(s, size temp_binding_pfx, NONE)
  else raise ERR "dest_temp_binding" "String not a temp-binding"


val pp_sig_hook = ref (fn () => ());

val concat = String.concat;
val sort = Lib.sort (fn s1:string => fn s2 => s1<=s2);
val psort =
    Lib.sort (fn (s1:string,_:Thm.thm,_) => fn (s2,_:Thm.thm,_) => s1<=s2);
fun Thry s = s^"Theory";
fun ThrySig s = Thry s

fun with_parens pfn x =
  let open Portable PP
  in [add_string "(", pfn x, add_string ")"]
  end

fun pp_type mvartype mtype ty =
 let open Portable Type PP
     val pp_type = pp_type mvartype mtype
 in
  if is_vartype ty
  then case dest_vartype ty
        of "'a" => add_string "alpha"
         | "'b" => add_string "beta"
         | "'c" => add_string "gamma"
         | "'d" => add_string "delta"
         |  s   => add_string (mvartype^quote s)
  else
  case dest_thy_type ty
   of {Tyop="bool",Thy="min", Args=[]} => add_string "bool"
    | {Tyop="ind", Thy="min", Args=[]} => add_string "ind"
    | {Tyop="fun", Thy="min", Args=[d,r]} =>
          block INCONSISTENT 1 [
            add_string "(",
            pp_type d,
            add_string " -->",
            add_break (1,0),
            pp_type r,
            add_string ")"
          ]
   | {Tyop,Thy,Args} =>
          block INCONSISTENT (size mtype) [
            add_string mtype,
            add_string (quote Tyop),
            add_break (1,0),
            add_string (quote Thy),
            add_break (1,0),
            add_string "[",
            block INCONSISTENT 1 (
              pr_list pp_type [add_string ",", add_break (1,0)] Args
            ),
            add_string "]"
          ]
 end

val include_docs = ref true
val _ = Feedback.register_btrace ("TheoryPP.include_docs", include_docs)

fun classify As Ds Ts [] = (As,Ds,Ts)
  | classify As Ds Ts ((r as (s,th,i:thminfo))::rest) =
    let open DB_dtype
    in
      case #class i of
          Axm => classify (r::As) Ds Ts rest
        | Def => classify As (r::Ds) Ts rest
        | Thm => classify As Ds (r::Ts) rest
    end


fun pp_sig pp_thm info_record = let
  open PP
  val {name,parents,all_thms,sig_ps} = info_record
  val parents'     = sort parents
  val rm_temp      = List.filter (fn (s, _, _) => not (is_temp_binding s))
  val all_thms'    = rm_temp all_thms
  val (axioms,definitions,theorems) = classify [] [] [] all_thms'
  val axioms'      = psort axioms
  val definitions' = psort definitions
  val theorems'    = psort theorems
  fun vblock(header, ob_pr, obs) =
    block CONSISTENT 2 [
      add_string ("(*  "^header^ "  *)"), NL,
      block CONSISTENT 0 (pr_list ob_pr [NL] obs)
    ]
  fun pparent s = String.concat ["structure ",Thry s," : ",ThrySig s]
  val parentstring = "Parent theory of "^Lib.quote name
  fun pr_parent s = block CONSISTENT 0 [
                     add_string (String.concat ["[", s, "]"]),
                     add_break(1,0),
                     add_string parentstring]
  fun pr_parents [] = []
    | pr_parents slist =
        [block CONSISTENT 0 (pr_list pr_parent [NL, NL] slist), NL, NL]

  fun pr_thm class (s,th) =
     block CONSISTENT 3 [
       add_string (String.concat ["[", s, "]"]),
       add_string ("  "^class), NL, NL,
       if null (Thm.hyp th) andalso
          (Tag.isEmpty (Thm.tag th) orelse Tag.isDisk (Thm.tag th))
       then pp_thm th
       else
         with_flag(Globals.show_tags,true)
                  (with_flag(Globals.show_assums, true) pp_thm) th
     ]
      handle e => (print ("Failed to print theorem in theory export: "^s^"\n");
                   print (General.exnMessage e ^ "\n");
                   raise e)
  fun pr_thms _ [] = []
    | pr_thms heading plist =
       [block CONSISTENT 0 (pr_list (pr_thm heading) [NL,NL] plist), NL, NL]
  fun pr_sig_ps NONE = []  (* won't be fired because of filtering below *)
    | pr_sig_ps (SOME pp) = [pp()]
  fun pr_sig_psl [] = []
    | pr_sig_psl l =
       [NL, NL,
        block CONSISTENT 0
              (pr_list (block CONSISTENT 0 o pr_sig_ps) [NL, NL] l)]

  val filter_visible =
      List.mapPartial (fn (s, th, {private=false,...}:thminfo) => SOME (s,th)
                      |            _                 => NONE)
  fun pr_docs() =
      if !include_docs then
        (!pp_sig_hook();
         [block CONSISTENT 3 (
             [add_string "(*", NL] @
             pr_parents parents' @
             pr_thms "Axiom" (filter_visible axioms') @
             pr_thms "Definition" (filter_visible definitions') @
             pr_thms "Theorem" (filter_visible theorems')
           ), NL,
          add_string "*)", NL])
      else []
  fun pthms (heading, ths) =
    vblock(heading,
           (fn (s,th,{private,...}:thminfo) =>
               block CONSISTENT 0
                     (if is_temp_binding s orelse private then []
                      else
                        [add_string("val "^ s ^ " : thm")])),
           ths)
in
  block CONSISTENT 0 (
    [add_string ("signature "^ThrySig name^" ="), NL,
     block CONSISTENT 2 [
       add_string "sig", NL,
       block CONSISTENT 0 (
         [add_string"type thm = Thm.thm"] @
         (if null axioms' then []
          else [NL, NL, pthms ("Axioms",axioms')]) @
         (if null definitions' then []
          else [NL, NL, pthms("Definitions", definitions')]) @
         (if null theorems' then []
          else [NL, NL, pthms ("Theorems", theorems')]) @
         pr_sig_psl (filter (fn NONE => false | _ => true) sig_ps)
       )
     ], NL
    ] @
    pr_docs() @
    [add_string"end", NL]
  )
end;

(*---------------------------------------------------------------------------
 *  Print a theory as a module.
 *---------------------------------------------------------------------------*)

val stringify = Lib.mlquote

fun is_atom t = Term.is_var t orelse Term.is_const t
fun strip_comb t = let
  fun recurse acc t = let
    val (f, x) = Term.dest_comb t
  in
    recurse (x::acc) f
  end handle HOL_ERR _ => (t, List.rev acc)
in
  recurse [] t
end

infix >>
open smpp

fun mlower s m =
  case m ((), []) of
      NONE => raise Fail ("Couldn't print Theory" ^ s)
    | SOME(_, (_, ps)) => PP.block PP.CONSISTENT 0 ps


fun pp_struct (info_record : struct_info_record) = let
  open Term Thm
  val {theory as (name,i1,i2), parents=parents0, thydata, mldeps, all_thms,
       types,constants,struct_ps, struct_pcps} = info_record
  val parents1 =
    List.mapPartial (fn (s,_,_) => if "min"=s then NONE else SOME (Thry s))
                    parents0
  val jump = add_newline >> add_newline
  fun pblock(ob_pr, obs) =
      case obs of
        [] => nothing
      |  _ =>
         block CONSISTENT 0
           (
           add_string "local open " >>
           block INCONSISTENT 0 (pr_list ob_pr (add_break (1,0)) obs) >>
           add_break(1,0) >>
           add_string "in end;"
           )

  fun pparent (s,i,j) = Thry s

  fun pr_bind(s, th, {private,...}:thminfo) = let
    val addsbl = pr_list add_string (add_break(1,2))
  in
    if is_temp_binding s orelse private then nothing
    else
      (* this rigmarole is necessary to allow ML bindings where the name is
         a datatype constructor or an infix, or both *)
      block CONSISTENT 0
        (block INCONSISTENT 0 (addsbl ["fun","op",s,"_","=","()"]) >>
         add_break(1,0) >>
         block INCONSISTENT 0 (addsbl ["val","op",s,"=","TDB.find",mlquote s]))
  end

  val bind_theorems =
     block CONSISTENT 0 (
       if null all_thms then nothing
       else
         block CONSISTENT 0 (pr_list pr_bind add_newline all_thms) >>
         add_newline
     )

  fun pr_ps NONE = nothing
    | pr_ps (SOME pp) = block CONSISTENT 0 (lift pp ())

  fun pr_psl l =
       block CONSISTENT 0
         (pr_list pr_ps (add_newline >> add_newline) l)
  fun pr_pcl l =
      block CONSISTENT 0 (
        pr_list (fn pf => block CONSISTENT 0 (lift pf ()))
                (add_newline >> add_newline)
                l
      )
  val datfile =
      mlquote (
        holpathdb.reverse_lookup {
          path = OS.Path.concat(OS.FileSys.getDir(), name ^ "Theory.dat")
        }
      )
  val m =
      block CONSISTENT 0 (
       add_string (String.concatWith " "
                       ["structure",Thry name,":>", ThrySig name,"="]) >>
       add_newline >>
       block CONSISTENT 2 (
          add_string "struct" >> jump >>
          block CONSISTENT 0 (
            block CONSISTENT 0 (
             add_string ("val _ = if !Globals.print_thy_loads") >>
             add_break (1,2) >>
             add_string
               ("then TextIO.print \"Loading "^ Thry name ^ " ... \"") >>
             add_break (1,2) >>
             add_string "else ()") >> jump >>
             add_string "open Type Term Thm"  >> add_newline >>
             pblock (add_string,
               Listsort.sort String.compare parents1 @ mldeps) >>
             add_newline >> add_newline >>
             block CONSISTENT 0 (
              add_string "structure TDB = struct" >> add_break(1,2) >>
              add_string "val thydata = " >> add_break(1,4) >>
              block INCONSISTENT 0 (
                add_string "TheoryReader.load_thydata {" >> add_break (1,2) >>
                block CONSISTENT 0 (
                  block INCONSISTENT 2 (
                    add_string "thyname =" >> add_break(1,2) >>
                    add_string (mlquote name ^ ",")
                  ) >> add_break (1,0) >>
                  block INCONSISTENT 2 (
                    add_string "path =" >> add_break(1,2) >>
                    add_string ("holpathdb.subst_pathvars "^datfile)
                  ) >>
                  add_break(1,~2) >> add_string "}"
                )
              ) >> add_break(1,2) >>
              add_string ("fun find s = #1 (valOf (Symtab.lookup thydata s))") >>
              add_break(1,0) >> add_string "end"
            ) >> jump >>
            bind_theorems >>
            add_newline >>
            pr_psl struct_ps
          )
        ) >> add_break(0,0) >>
        add_string "val _ = if !Globals.print_thy_loads then TextIO.print \
                   \\"done\\n\" else ()" >> add_newline >>
        add_string ("val _ = Theory.load_complete "^ stringify name) >>
        jump >>
        pr_pcl struct_pcps >>
        add_string "end" >> add_newline)
in
  mlower ": struct" m
end

(*---------------------------------------------------------------------------
 *  Print theory data separately.
 *---------------------------------------------------------------------------*)

fun pp_thydata (info_record : struct_info_record) = let
  open Term Thm
  val {theory as (name,i1,i2), parents=parents0,
       thydata = (thydata_strings,thydata_tms, thydata), mldeps,
       all_thms,types,constants,...} = info_record
  val parents1 =
      List.mapPartial (fn (s,_,_) => if "min"=s then NONE else SOME (Thry s))
                      parents0
  open SharingTables

  val share_data = build_sharing_data {
        named_terms = [], named_types = [], unnamed_terms = [],
        unnamed_types = [],
        theorems = all_thms
      }
  val share_data = add_strings thydata_strings share_data
  val share_data = add_terms thydata_tms share_data

  local open HOLsexp in
  fun enc_thid(s,i,j) =
    List[String s, String (Arbnum.toString i), String (Arbnum.toString j)]
  val enc_thid_and_parents =
      curry (pair_encode(enc_thid, list_encode enc_thid))
  end (* local *)

  fun enc_incorporate_types types =
      let open HOLsexp
      in
        tagged_encode "incorporate-types"
                      (list_encode (pair_encode(String,Integer))) types
      end

  fun enc_incorporate_constants constants =
      let open HOLsexp
      in
        tagged_encode "incorporate-consts"
                      (list_encode
                         (pair_encode(String, Integer o write_type share_data)))
                      constants
      end

  fun chunks w s =
    if String.size s <= w then [s]
    else String.substring(s, 0, w) :: chunks w (String.extract(s, w, NONE))

  val enc_cpl = HOLsexp.pair_encode(HOLsexp.String, fn x => x)

  fun list_loadable shared_writers thydata_map =
    Binarymap.foldl
      (fn (k, data, rest) => (k, data shared_writers) :: rest)
      []
      thydata_map
  fun enc_loadable shared_writers thydata_map =
      let open HOLsexp in
        tagged_encode "loadable-thydata" (list_encode enc_cpl)
                      (list_loadable shared_writers thydata_map)
      end
  val thysexp =
      let open HOLsexp
      in
        List [
          Symbol "theory",
          enc_thid_and_parents theory parents0,
          enc_sdata share_data,
          tagged_encode "incorporate" (
            pair_encode(enc_incorporate_types, enc_incorporate_constants)
          ) (types, constants),
          enc_loadable {terms = write_term share_data,
                        strings = write_string share_data}
                       thydata
        ]
      end
in
  mlower ": dat" (lift HOLsexp.printer thysexp)
end handle e as Interrupt => raise e
         | e => raise ERR "pp_thydata"
                      ("Caught exception: " ^ General.exnMessage e)



end;  (* TheoryPP *)
