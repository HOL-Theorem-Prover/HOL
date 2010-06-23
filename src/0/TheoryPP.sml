(*---------------------------------------------------------------------------*
 *                                                                           *
 *            HOL theories interpreted by SML structures.                    *
 *                                                                           *
 *---------------------------------------------------------------------------*)

structure TheoryPP : RawTheoryPP =
struct

type thm      = KernelTypes.thm;
type term     = KernelTypes.term
type hol_type = KernelTypes.hol_type
type num = Arbnum.num

open Feedback Lib Portable;

val ERR = mk_HOL_ERR "TheoryPP";

val concat = String.concat;
val sort = Lib.sort (fn s1:string => fn s2 => s1<=s2);
val psort = Lib.sort (fn (s1:string,_:Thm.thm) => fn (s2,_:Thm.thm) => s1<=s2);
fun thid_sort x = Lib.sort (fn (s1:string,_,_) => fn (s2,_,_) => s1<=s2) x;
fun thm_terms th = Thm.concl th :: Thm.hyp th;

(*---------------------------------------------------------------------------*)
(* Print a type                                                              *)
(*---------------------------------------------------------------------------*)

fun Thry s = s^"Theory";
fun ThrySig s = Thry s

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

fun with_parens pfn pp x =
  let open Portable
  in add_string pp "("; pfn pp x; add_string pp ")"
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
        (Tag.isDisk (Thm.tag th) orelse Tag.isEmpty (Thm.tag th))
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
    (begin_block CONSISTENT 3;
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
 * Set up a sharing table.
 *---------------------------------------------------------------------------*)

val table_size = 311
val hash = Lib.hash table_size;

val share_table = Array.array(table_size, [] :(Term.term * int)list);
val taken = ref 0;

fun reset_share_table () =
  (taken := 0;
   Lib.for_se 0 (table_size-1) (fn i => Array.update(share_table,i,[])));

fun hash_type ty n =
  hash(Type.dest_vartype ty) (0,n)
  handle HOL_ERR _ =>
     let val {Tyop,Thy,Args} = Type.dest_thy_type ty
     in itlist hash_type Args (hash Thy (0, hash Tyop (0,n)))
     end;

fun hash_atom tm n =
  let val (Name,Ty) = Term.dest_var tm
  in hash_type Ty (hash Name (0,n))
  end handle HOL_ERR _ =>
       let val {Name,Thy,Ty} = Term.dest_thy_const tm
       in hash_type Ty (hash Thy (0, hash Name (0,n)))
       end;


(*---------------------------------------------------------------------------
 * Add an atom to the atom hash table, checking to see if it is already there
 * first.
 *---------------------------------------------------------------------------*)

fun add tm =
  let val i = hash_atom tm 0
      val els = Array.sub(share_table, i)
      fun loop [] =
               (Array.update(share_table, i, (tm,!taken)::els);
                taken := !taken + 1)
        | loop ((x,index)::rst) = if x=tm then () else loop rst
  in
    loop els
  end;


(*---------------------------------------------------------------------------*)
(* Get the vector index of an atom.                                          *)
(*---------------------------------------------------------------------------*)

fun index tm =
  let val i = hash_atom tm 0
      val els = Array.sub(share_table, i)
      fun loop [] = raise ERR "index" "not found in table"
        | loop ((x,index)::rst) = if x=tm then index else loop rst
  in
    loop els
  end;

val pp_raw = Term.pp_raw_term index;

local open Portable Feedback
in
fun check V thml =
  let val _ = HOL_MESG "Checking consistency of sharing scheme"
      fun chk tm =
         if (Vector.sub(V, index tm) = tm)
          then ()
           else (HOL_MESG "FAILURE in sharing scheme!";
                 raise ERR "check" "failure in sharing scheme")
  in List.app (app (Term.trav chk) o thm_terms o snd) thml;
     HOL_MESG "Completed successfully"
  end
end;


fun share_thy check_share thms =
  let val _ = reset_share_table()
      val _ = List.app (app (Term.trav add) o thm_terms o snd) thms
      val L0 = Array.foldr (op @) [] share_table
      val L1 = Lib.sort (fn (_,i0) => fn (_,i1) => i0<=i1) L0
      val slist = map fst L1
      val _ = if check_share then check (Vector.fromList slist) thms else ()
  in
    slist
  end;

(*---------------------------------------------------------------------------
 * Need to replace a backslash by two backslashes because one of them
 * disappears when sent through "output". (Occurrences of " inside a string
 * have a similar problem.) Also need to add string quotes at each end
 * of the string.
 *---------------------------------------------------------------------------*)

local val backslash = #"\\"
      val double_quote = #"\""
      fun needs_backslash s =
        let fun loop i =
             let val c = String.sub(s,i)
             in (c = backslash) orelse (c = double_quote) orelse loop (i+1)
             end handle Subscript => false
        in loop 0
        end
      fun add_backslashes s =
        let fun add i A = add (i+1)
              (let val c = String.sub(s,i)
               in if (c = backslash) orelse (c = double_quote)
                  then  (c:: #"\\" ::A)
                  else c::A end)
               handle Subscript => String.implode(rev(double_quote::A))
        in add 0 [#"\""]
        end
in
fun stringify s =
  if Lexis.ok_identifier s orelse not(needs_backslash s)
  then Lib.quote s
  else add_backslashes s
end;


(*---------------------------------------------------------------------------
 *  Print a theory as a module.
 *---------------------------------------------------------------------------*)

infix >>
fun (f1 >> f2) pps = (f1 pps ; f2 pps)

fun block state brkdepth f pps = (HOLPP.begin_block pps state brkdepth ;
                                  f pps;
                                  HOLPP.end_block pps)
fun add_string s pps = HOLPP.add_string pps s
val add_newline = HOLPP.add_newline
fun add_break ipr pps = HOLPP.add_break pps ipr
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

fun pp_struct info_record ppstrm =
 let open Term
     val {theory as (name,i1,i2), parents=parents0, thydata,
          axioms,definitions,theorems,types,constants,struct_ps} = info_record
     val parents1 = filter (fn (s,_,_) => not ("min"=s)) parents0
     val {add_string,add_break,begin_block,end_block, add_newline,
          flush_ppstream,...} = Portable.with_ppstream ppstrm
     val pp_tm = pp_raw ppstrm
     val pp_ty = with_parens (pp_type "U" "T") ppstrm
     val pp_tag = Tag.pp_to_disk ppstrm
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
     fun pp_ty_dec(s,i) =
          (begin_block CONSISTENT 0; add_string"(";
            add_string (stringify s); add_string",";
            add_break(0,0); add_string(Lib.int_to_string i);
            add_string")"; end_block())
     fun pp_const_dec(s,ty) =
          (begin_block INCONSISTENT 1; add_string"(";
            add_string (stringify s); add_string",";
            add_break(0,0); pp_ty ty;
            add_string")"; end_block())
     fun pp_incorporate theory parents types constants =
         (begin_block CONSISTENT 0;
          begin_block CONSISTENT 8;
            add_string "val _ = Theory.link_parents"; add_break(1,0);
            pp_thid theory; add_break(1,0); pp_sml_list pp_thid parents;
            add_string ";" ;end_block(); add_newline();
          begin_block CONSISTENT 5;
            add_string ("val _ = Theory.incorporate_types "^stringify name);
            add_break(1,0); pp_sml_list pp_ty_dec types;add_string ";" ;
          end_block(); add_newline();
          begin_block CONSISTENT 3;
            add_string ("val _ = Theory.incorporate_consts "^stringify name);
            add_break(1,0); pp_sml_list pp_const_dec constants;
            add_string ";" ;
          end_block(); add_newline();
          end_block())
     fun pparent (s,i,j) = Thry s
     fun pr_var v =
         let val (Name,Ty) = dest_var v
         in add_string "V";
            begin_block INCONSISTENT 0;
            add_string(stringify Name); add_break(1,0);
            pp_ty Ty; end_block()
         end
     fun pr_const c =
         let val {Name,Thy,Ty} = dest_thy_const c
         in add_string "C";
            begin_block INCONSISTENT 0;
            add_string(stringify Name); add_break(1,0);
            add_string(stringify Thy); add_break(1,0);
            pp_ty Ty; end_block()
         end
     fun pr_atom a =
           (begin_block INCONSISTENT 2;
            if is_var a then pr_var a else pr_const a;
            end_block())
        handle HOL_ERR _ => raise ERR"pp_struct.pr_atom" "not atomic"
     fun pr_bind (s,th) =
      let val (tg,asl,w) = (Thm.tag th, Thm.hyp th, Thm.concl th)
      in
         begin_block INCONSISTENT 2;
         add_string"val"; add_break(1,0); add_string ("op "^s);
         add_break (1,0);
         add_string "="; add_break (1,0);
         add_string"DT("; begin_block INCONSISTENT 0;
                        pp_tag tg; add_string","; add_break(1,0);
                        pp_sml_list pp_tm asl; add_string","; add_break(1,0);
                        pp_tm w; end_block();
         add_string")";
         end_block()
      end
     val thml = axioms@definitions@theorems
     val slist = share_thy false thml

     fun bind_theorems () = if null thml then ()
      else (
        begin_block CONSISTENT 0;
        add_string "local"; add_break(1,0);
        begin_block CONSISTENT 0;
        add_string "val share_table = Vector.fromList"; add_break(1,0);
        pp_sml_list pr_atom slist; add_newline();
        add_string"val DT = Thm.disk_thm share_table";
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
      add_string"fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}";
      add_newline();
      add_string"fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}";
      add_newline();
      add_string"fun V s q = mk_var(s,q)";     add_newline();
      add_string"val U     = mk_vartype";              add_newline();
   (*   add_string("val _ = print \"Loading theory: "^Thry name^"\\n\""); *)
      add_newline();
      pblock ("Parents", add_string o pparent,
              thid_sort parents1);
      add_newline();
      pp_incorporate theory parents0 types constants; add_newline();
      bind_theorems (); add_newline();
      dblist(); add_newline();
      pr_psl struct_ps;
      pr_thydata name thydata ppstrm;
      end_block();
      end_block();
      add_string "val _ = if !Globals.print_thy_loads then print \"done\\n\" else ()"; add_newline();
      add_string ("val _ = Theory.load_complete \""^String.toString name^ "\"");
      add_newline();
      add_break(0,0); add_string"end"; add_newline();
      end_block();
      flush_ppstream()
   end;

end;  (* TheoryPP *)
