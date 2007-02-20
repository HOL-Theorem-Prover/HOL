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
fun thm_atoms acc th k = let
  open Term
  fun term_atoms acc t k =
      if is_var t then k (HOLset.add(acc, t))
      else if is_const t then k (HOLset.add(acc, t))
      else if is_comb t then let
          val (f,x) = dest_comb t
        in
          term_atoms acc f (fn a' => term_atoms a' x k)
        end
      else let
          val (v, body) = dest_abs t
        in
          term_atoms (HOLset.add(acc, v)) body k
        end
  fun terml_atoms tlist k acc =
      case tlist of
        [] => k acc
      | (t::ts) => term_atoms acc t (terml_atoms ts k)
in
  terml_atoms (Thm.concl th :: Thm.hyp th) k acc
end

fun thml_atoms thlist acc =
    case thlist of
      [] => acc
    | (th::ths) => thm_atoms acc th (thml_atoms ths)

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
    (!pp_sig_hook();
     begin_block CONSISTENT 3;
     add_string "(*"; add_newline();
     pr_parents parents';
     pr_thms "Axiom" axioms';
     pr_thms "Definition" definitions';
     pr_thms "Theorem" theorems';
     end_block(); add_newline(); add_string "*)"; add_newline())
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


fun pp_struct info_record ppstrm =
 let open Term Thm
     val {theory as (name,i1,i2), parents=parents0,
        axioms,definitions,theorems,types,constants,struct_ps} = info_record
     val parents1 = filter (fn (s,_,_) => not ("min"=s)) parents0
     val {add_string,add_break,begin_block,end_block, add_newline,
          flush_ppstream,...} = Portable.with_ppstream ppstrm
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
         case obs
         of [] => ()
          |  _ =>
            ( begin_block CONSISTENT 0;
              add_string ("(*  Parents *)");
              add_newline();
              add_string "local open ";
              begin_block INCONSISTENT 0;
              pr_list ob_pr (fn () => ()) (fn () => add_break (1,0)) obs;
              end_block();
              add_newline(); add_string "in end;";
              end_block())
     fun pp_sml_list pfun L =
       (begin_block CONSISTENT 0; add_string "[";
        begin_block INCONSISTENT 0;
        pr_list pfun (fn () => add_string",") (fn () => add_break(1,0)) L;
        end_block(); add_string "]"; end_block())
     fun pp_thid(s,i,j) =
          (begin_block CONSISTENT 0; add_string"(";
            add_string (stringify s); add_string",";
            add_break(0,0);
            add_string("Arbnum.fromString \""^Arbnum.toString i^"\"");
            add_string","; add_break(0,0);
            add_string("Arbnum.fromString \""^Arbnum.toString j^"\"");
            add_string")"; end_block())
     fun pp_incorporate_upto_types theory parents types =
         (begin_block CONSISTENT 8;
            add_string "val _ = Theory.link_parents"; add_break(1,0);
            pp_thid theory; add_break(1,0); pp_sml_list pp_thid parents;
            add_string ";" ;end_block(); add_newline();
          begin_block CONSISTENT 5;
            add_string ("val _ = Theory.incorporate_types "^stringify name);
            add_break(1,0); pp_sml_list pp_ty_dec types;add_string ";" ;
          end_block(); add_newline())
     fun pp_incorporate_constants constants =
         (begin_block CONSISTENT 3;
          add_string ("val _ = Theory.incorporate_consts "^stringify name^" ");
          add_string "tyvector";
          add_break(1,0); pp_sml_list pp_const_dec constants;
          add_string ";" ; end_block(); add_newline())

     fun pparent (s,i,j) = Thry s

     fun pp_tm tm =
         (add_string "read\"";
          add_string (RawParse.pp_raw_term
                        (fn t => Map.find(#termmap tmtable, t))
                        tm);
          add_string "\"")
     fun pr_bind(s, th) = let
       val (tg, asl, w) = (Thm.tag th, Thm.hyp th, Thm.concl th)
     in
       begin_block INCONSISTENT 2;
       add_string "val"; add_break(1,0); add_string s; add_break(1,0);
       add_string "="; add_break(1,0);
       add_string "DT("; begin_block INCONSISTENT 0;
                       Tag.pp_to_disk ppstrm tg;
                       add_string ","; add_break(1,0);
                       pp_sml_list pp_tm (w::asl);
                       end_block(); add_string")";
       end_block()
     end

     fun stringbrk s = (add_string s; add_break(1,0))
     fun bind_theorems () =
         if null thml then ()
         else
           (begin_block CONSISTENT 0;
            stringbrk "local";
            begin_block CONSISTENT 0;
            stringbrk"val DT = Thm.disk_thm";
            stringbrk"fun read s = RawParse.readTerm tmvector s";
            end_block();
            add_newline();
            add_string"in"; add_newline();
            begin_block CONSISTENT 0;
            pr_list pr_bind (fn () => ()) add_newline thml;
            end_block();
            add_newline();
            add_string"end"; end_block())

     fun pr_dbtriple (class,th) =
        (begin_block CONSISTENT 1;
         add_string"("; add_string (stringify th); add_string",";
         add_break (0,0); add_string th; add_string","; add_break(0,0);
         add_string class; add_string ")"; end_block())

     fun dblist () =
        let val axl  = map (fn (s,_) => ("DB.Axm",s)) axioms
            val defl = map (fn (s,_) => ("DB.Def",s)) definitions
            val thml = map (fn (s,_) => ("DB.Thm",s)) theorems
        in
           begin_block INCONSISTENT 0;
           add_string "val _ = DB.bindl"; add_break(1,0);
           add_string (stringify name); add_break(1,0);
           pp_sml_list pr_dbtriple (axl@defl@thml);
           add_newline();
           end_block()
        end
     fun pr_ps NONE = ()
       | pr_ps (SOME pp) = (begin_block CONSISTENT 0; pp ppstrm; end_block());
     fun pr_psl l =
          (begin_block CONSISTENT 0;
            pr_list pr_ps (fn () => ())
              (fn () => (add_newline(); add_newline())) l;
            end_block());

   in
      begin_block CONSISTENT 0;
      add_string (String.concat
           ["structure ",Thry name," :> ", ThrySig name," ="]);
      add_newline();
      begin_block CONSISTENT 2;
      add_string "struct"; add_newline();
      begin_block CONSISTENT 0;
      add_string ("val _ = if !Globals.print_thy_loads then print \"Loading "^
                  Thry name^" ... \" else ()"); add_newline();
      add_string "open Type Term Thm"; add_newline();
      add_string "infixr -->"; add_newline();
      add_newline();
      add_string"fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}";
      add_newline();
      add_string"fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}";
      add_newline();
      add_string"fun V s q = mk_var(s,q)";     add_newline();
      add_string"val U     = mk_vartype";              add_newline();
      pblock ("Parents", add_string o pparent,
              thid_sort parents1);
      add_newline();
      pp_incorporate_upto_types theory parents0 types; add_newline();
      output_idtable ppstrm "idvector" idtable;
      output_typetable ppstrm {idtable_nm = "idvector",
                               tytable_nm = "tyvector"} tytable;
      pp_incorporate_constants constants; add_newline();
      output_termtable ppstrm {idtable_nm = "idvector",
                               tytable_nm = "tyvector",
                               termtable_nm = "tmvector"} tmtable;
      bind_theorems (); add_newline();
      dblist(); add_newline();
      pr_psl struct_ps;
      end_block();
      end_block();
      add_break(0,0);
      add_string "val _ = if !Globals.print_thy_loads then print \"done\\n\" else ()"; add_newline();
      add_string"end"; add_newline();
      end_block();
      flush_ppstream()
   end;

end;  (* TheoryPP *)
