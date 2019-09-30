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
val psort = Lib.sort (fn (s1:string,_:Thm.thm) => fn (s2,_:Thm.thm) => s1<=s2);
fun thm_atoms acc th = Term.all_atomsl (Thm.concl th :: Thm.hyp th) acc

fun thml_atoms thlist acc =
    case thlist of
      [] => acc
    | (th::ths) => thml_atoms ths (thm_atoms acc th)

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

fun pp_sig pp_thm info_record = let
  open PP
  val {name,parents,axioms,definitions,theorems,sig_ps} = info_record
  val parents'     = sort parents
  val rm_temp      = List.filter (fn (s, _) => not (is_temp_binding s))
  val axioms'      = psort axioms |> rm_temp
  val definitions' = psort definitions |> rm_temp
  val theorems'    = psort theorems |> rm_temp
  val thml         = axioms@definitions@theorems
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

  fun pr_docs() =
      if !include_docs then
        (!pp_sig_hook();
         [block CONSISTENT 3 (
             [add_string "(*", NL] @
             pr_parents parents' @
             pr_thms "Axiom" axioms' @
             pr_thms "Definition" definitions' @
             pr_thms "Theorem" theorems'
           ), NL,
          add_string "*)", NL])
      else []
  fun pthms (heading, ths) =
    vblock(heading,
           (fn (s,th) => block CONSISTENT 0
                               (if is_temp_binding s then []
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

fun pp_struct info_record = let
  open Term Thm
  val {theory as (name,i1,i2), parents=parents0,
       thydata = (thydata_tms, thydata), mldeps,
       axioms,definitions,theorems,types,constants,struct_ps} = info_record
  val parents1 =
    List.mapPartial (fn (s,_,_) => if "min"=s then NONE else SOME (Thry s))
                    parents0
  val thml = axioms@definitions@theorems
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

  fun pr_bind(s, th) = let
    val (tg, asl, w) = (Thm.tag th, Thm.hyp th, Thm.concl th)
    val addsbl = pr_list add_string (add_break(1,2))
  in
    if is_temp_binding s then nothing
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
       if null thml then nothing
       else
         block CONSISTENT 0 (pr_list pr_bind add_newline thml) >>
         add_newline
     )

  fun pr_ps NONE = nothing
    | pr_ps (SOME pp) = block CONSISTENT 0 (lift pp ())

  fun pr_psl l =
       block CONSISTENT 0
         (pr_list pr_ps (add_newline >> add_newline) l)
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
                add_string "TheoryReader.load_thydata" >> add_break (1,2) >>
                add_string (mlquote name) >> add_break (1,2) >>
                add_string ("(holpathdb.subst_pathvars "^datfile^")")
              ) >> add_break(1,2) >>
              add_string ("fun find s = Redblackmap.find (thydata,s)") >>
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
        add_string "end" >> add_newline)
in
  mlower ": struct" m
end

(*---------------------------------------------------------------------------
 *  Print theory data separately.
 *---------------------------------------------------------------------------*)


fun pp_thydata info_record = let
  open Term Thm
  val {theory as (name,i1,i2), parents=parents0,
       thydata = (thydata_tms, thydata), mldeps,
       axioms,definitions,theorems,types,constants,struct_ps} = info_record
  val parents1 =
      List.mapPartial (fn (s,_,_) => if "min"=s then NONE else SOME (Thry s))
                      parents0
  val thml = axioms@definitions@theorems
  val all_term_atoms_set =
      thml_atoms (map #2 thml) empty_tmset |> Term.all_atomsl thydata_tms
  open SharingTables
  fun dotypes (ty, (idtable, tytable)) = let
    val (_, idtable, tytable) = make_shared_type ty idtable tytable
  in
    (idtable, tytable)
  end
  val (idtable, tytable) =
      List.foldl dotypes (empty_idtable, empty_tytable) (map #2 constants)
  fun doterms (c, tables) = #2 (make_shared_term c tables)
  val (idtable, tytable, tmtable) =
      HOLset.foldl doterms (idtable, tytable, empty_termtable)
                   all_term_atoms_set

  val jump = add_newline >> add_newline
  fun pp_ty_dec (s,n) =
      add_string (stringify s ^ " " ^ Int.toString n)
  fun pp_const_dec (s, ty) =
      add_string (stringify s ^ " " ^
                  Int.toString (Map.find(#tymap tytable, ty)))
  fun pp_sml_list pfun L =
    block INCONSISTENT 0
      (
      add_string "[" >> add_break (0,0) >>
      pr_list pfun (add_string "," >> add_break (1,0)) L >>
      add_break (0,0) >>
      add_string "]"
      )

  fun pp_thid(s,i,j) = add_string
    (String.concatWith " " [stringify s, Arbnum.toString i, Arbnum.toString j])

  fun pp_thid_and_parents theory parents =
    block CONSISTENT 0
    (pp_thid theory >> add_newline >> pp_sml_list pp_thid parents)

  fun pp_incorporate_types types =
    block CONSISTENT 0 (pp_sml_list pp_ty_dec types)

  fun pp_incorporate_constants constants =
    block CONSISTENT 0 (pp_sml_list pp_const_dec constants)

  fun pparent (s,i,j) = Thry s
  val term_to_string = Term.write_raw (fn t => Map.find(#termmap tmtable, t))

  fun pp_tm tm = add_string ("\"" ^ (term_to_string tm) ^ "\"")

  fun pp_dep ((s,n),dl) =
  let
    fun f (thy,l) =
        add_string (mlquote thy) >> add_break(1,0) >>
        pr_list (add_string o Int.toString) (add_break(1,0)) l
  in
    add_string "[" >>
    block INCONSISTENT 1 (
      add_string (mlquote s) >> add_break (1,0) >>
      add_string (Int.toString n) >>
      (if not (null dl) then
        add_string "," >> add_break(1,0) >>
        pr_list f (add_string "," >> add_break (1,0)) dl
      else nothing)
    ) >> add_string "]"
  end

  fun dest_dep d = case d of
    DEP_SAVED (did,thydl) => (did,thydl)
  | DEP_UNSAVED dl     => raise ERR "string_of_dep" ""

  fun pp_tag tag =
  let
    val dep = Tag.dep_of tag
    val ocl = fst (Tag.dest_tag tag)
  in
    pp_dep (dest_dep dep) >> add_newline >>
    pp_sml_list (add_string o mlquote) ocl
  end

  fun pr_thm(s, th) = let
    val (tag, asl, w) = (Thm.tag th, Thm.hyp th, Thm.concl th)
  in
    if is_temp_binding s then nothing
    else
      block CONSISTENT 0
        (add_string (mlquote s) >> add_newline >>
         pp_tag tag >> add_newline >>
         pp_sml_list pp_tm (w::asl))
  end

  val pp_theorems =
    block CONSISTENT 0
      (if null thml then nothing else pr_list pr_thm add_newline thml)

  fun pr_db (class,th) =
    block CONSISTENT 0
      (add_string (stringify th) >> add_break(1,0) >> add_string class)
  fun dblist () =
     let
       fun check tys =
           List.mapPartial (fn (s, _) => if is_temp_binding s then NONE
                                         else SOME (tys, s))
       val axl  = check "Axm" axioms
       val defl = check "Def" definitions
       val thml = check "Thm" theorems
     in
       block CONSISTENT 0 (pp_sml_list pr_db (axl@defl@thml))
     end

  fun chunks w s =
    if String.size s <= w then [s]
    else String.substring(s, 0, w) :: chunks w (String.extract(s, w, NONE))

  fun pr_cpl (a,b) =
    block CONSISTENT 0
      (add_string (stringify a) >> add_break(1,0) >>
       pr_list (add_string o stringify) (add_break (1,0)) (chunks 65 b))

  fun list_loadable tmwrite thymap =
    Binarymap.foldl (fn (k, data, rest) => (k, data tmwrite) :: rest)
      [] thymap
  fun pr_loadable tmwrite thymap =
    block CONSISTENT 0 (pp_sml_list pr_cpl (list_loadable tmwrite thymap))
  val m =
    block CONSISTENT 0
      (
      add_string "THEORY_AND_PARENTS" >> add_newline >>
      pp_thid_and_parents theory parents0 >> jump >>
      add_string "INCORPORATE_TYPES" >> add_newline >>
      pp_incorporate_types types >> jump >>
      add_string "IDS" >> add_newline >>
      lift theoryout_idtable idtable >> jump >>
      add_string "TYPES" >> add_newline >>
      lift theoryout_typetable tytable >> jump >>
      add_string "INCORPORATE_CONSTS" >> add_newline >>
      pp_incorporate_constants constants >> jump >>
      add_string "TERMS" >> add_newline >>
      lift theoryout_termtable tmtable >> jump >>
      add_string "THEOREMS" >> add_newline >>
      pp_theorems >> jump >>
      add_string "CLASSES" >> add_newline >>
      dblist () >> jump >>
      add_string "LOADABLE_THYDATA" >> add_newline >>
      pr_loadable term_to_string thydata >> jump
      )
in
  mlower ": dat" m
end;



end;  (* TheoryPP *)
