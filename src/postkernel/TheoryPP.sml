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

open Feedback Lib Portable;

val ERR = mk_HOL_ERR "TheoryPP";

val pp_sig_hook = ref (fn () => ());

val concat = String.concat;
val sort = Lib.sort (fn s1:string => fn s2 => s1<=s2);
val psort = Lib.sort (fn (s1:string,_:Thm.thm) => fn (s2,_:Thm.thm) => s1<=s2);
val thid_sort = Lib.sort (fn (s1:string,_,_) => fn (s2,_,_) => s1<=s2);
fun thm_atoms acc th = Term.all_atomsl (Thm.concl th :: Thm.hyp th) acc

fun thml_atoms thlist acc =
    case thlist of
      [] => acc
    | (th::ths) => thml_atoms ths (thm_atoms acc th)

fun Thry s = s^"Theory";
fun ThrySig s = Thry s

fun with_parens pfn pp x =
  let open Portable
  in add_string pp "("; pfn pp x; add_string pp ")"
  end

fun pp_type mvartype mtype pps ty =
 let open Portable Type
     val pp_type = pp_type mvartype mtype pps
     val {add_string,add_break,begin_block,end_block,
          add_newline,flush_ppstream,...} = with_ppstream pps
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
    | {Tyop="fun", Thy="min", Args=[d,r]}
       => (add_string "(";
           begin_block INCONSISTENT 0;
             pp_type d;
             add_break (1,0);
             add_string "-->";
             add_break (1,0);
             pp_type r;
           end_block ();
           add_string ")")
   | {Tyop,Thy,Args}
      => let in
           add_string mtype;
           begin_block INCONSISTENT 0;
           add_string (quote Tyop);
           add_break (1,0);
           add_string (quote Thy);
           add_break (1,0);
           add_string "[";
           begin_block INCONSISTENT 0;
           pr_list pp_type (fn () => add_string ",")
           (fn () => add_break (1,0)) Args;
           end_block ();
           add_string "]";
           end_block ()
         end
 end

val include_docs = ref true
val _ = Feedback.register_btrace ("TheoryPP.include_docs", include_docs)

fun pp_sig pp_thm info_record ppstrm = let
  val {name,parents,axioms,definitions,theorems,sig_ps} = info_record
  val {add_string,add_break,begin_block,end_block,
       add_newline,flush_ppstream,...} = Portable.with_ppstream ppstrm
  val pp_thm       = pp_thm ppstrm
  val parents'     = sort parents
  val axioms'      = psort axioms
  val definitions' = psort definitions
  val theorems'    = psort theorems
  val thml         = axioms@definitions@theorems
  fun vblock(header, ob_pr, obs) =
    (begin_block CONSISTENT 2;
     add_string ("(*  "^header^ "  *)");
     add_newline();
     pr_list ob_pr (fn () => ()) add_newline obs;
     end_block())
  fun pparent s = String.concat ["structure ",Thry s," : ",ThrySig s]
  val parentstring = "Parent theory of "^Lib.quote name
  fun pr_parent s = (begin_block CONSISTENT 0;
                     add_string (String.concat ["[", s, "]"]);
                     add_break(1,0);
                     add_string parentstring; end_block())
  fun pr_parents [] = ()
    | pr_parents slist =
      ( begin_block CONSISTENT 0;
        pr_list pr_parent (fn () => ())
                (fn () => (add_newline(); add_newline()))
               slist;
        end_block();
        add_newline(); add_newline())

  fun pr_thm class (s,th) =
    (begin_block CONSISTENT 3;
     add_string (String.concat ["[", s, "]"]);
     add_string ("  "^class);
     add_newline(); add_newline();
     if null (Thm.hyp th) andalso
         (Tag.isEmpty (Thm.tag th) orelse Tag.isDisk (Thm.tag th))
       then pp_thm th
       else with_flag(Globals.show_tags,true)
             (with_flag(Globals.show_assums, true) pp_thm) th;
     end_block())
  fun pr_thms _ [] = ()
    | pr_thms heading plist =
       ( begin_block CONSISTENT 0;
         pr_list (pr_thm heading) (K ())
                 (fn () => (add_newline(); add_newline()))
                 plist;
         end_block();
         add_newline(); add_newline())
  fun pr_sig_ps NONE = ()  (* won't be fired because of filtering below *)
    | pr_sig_ps (SOME pp) = (begin_block CONSISTENT 0;
                             pp ppstrm; end_block());
  fun pr_sig_psl [] = ()
    | pr_sig_psl l =
       (add_newline(); add_newline();
        begin_block CONSISTENT 0;
        pr_list pr_sig_ps (fn () => ())
               (fn () => (add_newline(); add_newline())) l;
        end_block());

  fun pr_docs() =
      if !include_docs then
        (!pp_sig_hook();
         begin_block CONSISTENT 3;
         add_string "(*"; add_newline();
         pr_parents parents';
         pr_thms "Axiom" axioms';
         pr_thms "Definition" definitions';
         pr_thms "Theorem" theorems';
         end_block(); add_newline(); add_string "*)"; add_newline())
      else ()
  fun pthms (heading, ths) =
    vblock(heading,
           (fn (s,th) => (begin_block CONSISTENT 0;
                          add_string(concat["val ",s, " : thm"]);
                          end_block())),  ths)
in
  begin_block CONSISTENT 0;
  add_string ("signature "^ThrySig name^" ="); add_newline();
  begin_block CONSISTENT 2;
  add_string "sig"; add_newline();
  begin_block CONSISTENT 0;
  add_string"type thm = Thm.thm";
  if null axioms' then ()
  else (add_newline(); add_newline(); pthms ("Axioms",axioms'));
  if null definitions' then ()
  else (add_newline(); add_newline(); pthms("Definitions", definitions'));
  if null theorems' then ()
  else (add_newline(); add_newline(); pthms ("Theorems", theorems'));
  pr_sig_psl (filter (fn NONE => false | _ => true) sig_ps);
  end_block();
  end_block();
  add_newline();
  pr_docs();  (* end of if-then-else *)
  add_string"end"; add_newline();
  end_block();
  flush_ppstream()
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

fun strip_rbinop t = let
  open Term
  val (f, args) = strip_comb t
  val _ = length args = 2 orelse raise ERR "foo" "foo"
  val _ = is_atom f orelse raise ERR "foo" "foo"
  fun recurse acc arg_t = let
    val (f', args') = strip_comb arg_t
  in
    if length args' = 2 andalso f' = f then
      recurse (hd args' :: acc) (hd (tl args'))
    else List.rev(arg_t :: acc)
  end
in
  (f, recurse [hd args] (hd (tl args)))
end

infix >>
fun (f1 >> f2) pps = (f1 pps ; f2 pps)

fun block state brkdepth f pps = (HOLPP.begin_block pps state brkdepth ;
                                  f pps;
                                  HOLPP.end_block pps)
fun add_string s pps = HOLPP.add_string pps s
val add_newline = HOLPP.add_newline
fun add_break ipr pps = HOLPP.add_break pps ipr
fun pr_list f g h obs pps = Portable.pr_list (fn x => f x pps)
                                             (fn () => g pps)
                                             (fn () => h pps)
                                             obs
val flush = HOLPP.flush_ppstream
fun nothing pps = ()

fun pr_thydata thyname thymap = let
  fun keyval commap (k,v) =
      block CONSISTENT 2 (add_string (k^" =") >> add_break(1,2) >>
                          add_string ("\""^String.toString v^"\"" ^
                                      (if commap then "," else "")))
  fun one_entry (s, data) =
      (add_string "val _ = Theory.LoadableThyData.temp_encoded_update {" >>
       add_break(0,2) >>
       block CONSISTENT 0
         (keyval true ("thy", thyname) >>
          add_break(1,0) >>
          keyval true ("thydataty", s) >>
          add_break(1,0) >>
          keyval false ("data", data)) >>
       add_break(0,0) >>
       add_string "}" >>
       add_newline)
in
  Binarymap.foldl (fn (k, data, rest) => one_entry (k,data) >> rest)
                  nothing
                  thymap
end

fun pp_struct info_record = let
  open Term Thm
  val {theory as (name,i1,i2), parents=parents0, thydata,
       axioms,definitions,theorems,types,constants,struct_ps} = info_record
  val parents1 = filter (fn (s,_,_) => not ("min"=s)) parents0
  val thml = axioms@definitions@theorems
  val all_term_atoms_set = thml_atoms (map #2 thml) empty_tmset
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
  fun pp_ty_dec (s,n) =
      add_string ("("^stringify s^", "^Int.toString n^")")
  fun pp_const_dec (s, ty) =
      add_string ("("^stringify s^", "^
                  Int.toString (Map.find(#tymap tytable, ty)) ^ ")")
  fun pblock(header, ob_pr, obs) =
      case obs of
        [] => nothing
      |  _ =>
         block CONSISTENT 0
               (add_string ("(*  Parents *)") >>
                add_newline >>
                add_string "local open " >>
                block INCONSISTENT 0
                (pr_list ob_pr nothing (add_break (1,0)) obs) >>
                add_newline >>
                add_string "in end;")
  fun pp_sml_list pfun L =
    block CONSISTENT 0
          (add_string "[">>
           block INCONSISTENT 0
             (pr_list pfun (add_string",") (add_break(1,0)) L) >>
           add_string "]")
  fun pp_thid(s,i,j) =
       block CONSISTENT 0
         (add_string"(">>
          add_string (stringify s)>>
          add_string",">>
          add_break(0,0)>>
          add_string("Arbnum.fromString \""^Arbnum.toString i^"\"")>>
          add_string",">>
          add_break(0,0)>>
          add_string("Arbnum.fromString \""^Arbnum.toString j^"\"")>>
          add_string")")
  fun pp_incorporate_upto_types theory parents types =
      (block CONSISTENT 8
         (add_string "val _ = Theory.link_parents">> add_break(1,0)>>
          pp_thid theory>> add_break(1,0)>>
          pp_sml_list pp_thid parents >>
          add_string ";")>>
       add_newline>>
       block CONSISTENT 5
         (add_string ("val _ = Theory.incorporate_types "^stringify name)>>
          add_break(1,0)>>
          pp_sml_list pp_ty_dec types>>
          add_string ";")>>
       add_newline)
  fun pp_incorporate_constants constants =
      (block CONSISTENT 3
         (add_string ("val _ = Theory.incorporate_consts "^
                      stringify name^" ")>>
          add_string "tyvector">>
          add_break(1,0)>>
          pp_sml_list pp_const_dec constants>>
          add_string ";")>>
       add_newline)

  fun pparent (s,i,j) = Thry s

  fun pp_tm tm =
      (add_string "read\"">>
       add_string (Term.write_raw
                     (fn t => Map.find(#termmap tmtable, t))
                     tm)>>
       add_string "\"")
  fun pr_bind(s, th) = let
    val (tg, asl, w) = (Thm.tag th, Thm.hyp th, Thm.concl th)
  in
    block INCONSISTENT 2
      (add_string "val">>
       add_break(1,0)>> add_string ("op "^s) >> add_break(1,0)>>
       add_string "=">> add_break(1,0)>>
       add_string "DT(">>
       block INCONSISTENT 0
          (C Tag.pp_to_disk tg>>
           add_string ",">> add_break(1,0)>>
           pp_sml_list pp_tm (w::asl))>>
       add_string")")
  end

  fun stringbrk s = (add_string s >> add_break(1,0))
  val bind_theorems =
      if null thml then nothing
      else
        block CONSISTENT 0
           (stringbrk "local" >>
            block CONSISTENT 0
              (stringbrk"val DT = Thm.disk_thm" >>
               stringbrk"val read = Term.read_raw tmvector") >>
            add_newline >>
            add_string"in" >> add_newline >>
            block CONSISTENT 0
               (pr_list pr_bind nothing add_newline thml) >>
            add_newline >>
            add_string"end")

  fun pr_dbtriple (class,th) =
     block CONSISTENT 1
        (add_string"(" >> add_string (stringify th) >> add_string"," >>
         add_break (0,0) >> add_string th >> add_string"," >>
         add_break(0,0) >> add_string class >> add_string ")")

  fun dblist () =
     let val axl  = map (fn (s,_) => ("DB.Axm",s)) axioms
         val defl = map (fn (s,_) => ("DB.Def",s)) definitions
         val thml = map (fn (s,_) => ("DB.Thm",s)) theorems
     in
        block INCONSISTENT 0
          (add_string "val _ = DB.bindl" >> add_break(1,0) >>
           add_string (stringify name) >> add_break(1,0) >>
           pp_sml_list pr_dbtriple (axl@defl@thml) >>
           add_newline)
     end
  fun pr_ps NONE = nothing
    | pr_ps (SOME pp) = block CONSISTENT 0 pp

  fun pr_psl l =
       block CONSISTENT 0
         (pr_list pr_ps nothing (add_newline >> add_newline) l)

  fun output_idtable s tab pps = SharingTables.output_idtable pps s tab
  fun output_typetable recd tab pps =
      SharingTables.output_typetable pps recd tab
  fun output_termtable recd tab pps =
      SharingTables.output_termtable pps recd tab

in
  block CONSISTENT 0
      (add_string (String.concat
                     ["structure ",Thry name," :> ", ThrySig name," ="]) >>
       add_newline >>
       block CONSISTENT 2
         (add_string "struct" >> add_newline >>
          block CONSISTENT 0
            (add_string ("val _ = if !Globals.print_thy_loads then \
                         \print \"Loading "^
                         Thry name^" ... \" else ()") >> add_newline >>
             add_string "open Type Term Thm" >> add_newline >>
             add_string "infixr -->" >> add_newline >>
             add_newline >>
             add_string"fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}" >>
             add_newline >>
             add_string"fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}" >>
             add_newline >>
             add_string"fun V s q = mk_var(s,q)" >> add_newline >>
             add_string"val U     = mk_vartype" >>  add_newline >>
             pblock ("Parents", add_string o pparent,
                     thid_sort parents1) >>
             add_newline >>
             pp_incorporate_upto_types theory parents0 types >> add_newline >>
             output_idtable "idvector" idtable >>
             output_typetable {idtable_nm = "idvector",
                               tytable_nm = "tyvector"} tytable >>
             pp_incorporate_constants constants >> add_newline >>
             output_termtable {idtable_nm = "idvector",
                               tytable_nm = "tyvector",
                               termtable_nm = "tmvector"} tmtable >>
             bind_theorems >> add_newline >>
             dblist() >> add_newline >>
             pr_psl struct_ps >>
             pr_thydata name thydata)) >>
         add_break(0,0) >>
         add_string "val _ = if !Globals.print_thy_loads then print \
                    \\"done\\n\" else ()" >> add_newline >>
         add_string ("val _ = Theory.load_complete \""^String.toString name^
                    "\"") >>
         add_newline >>
         add_string"end" >> add_newline) >>
      flush
   end

end;  (* TheoryPP *)
