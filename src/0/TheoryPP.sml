(*---------------------------------------------------------------------------
 * HOL theories interpreted by SML structures.
 *
 *---------------------------------------------------------------------------*)
structure TheoryPP :> TheoryPP =
struct

type hol_type = Type.hol_type
type thm      = Thm.thm;

open Exception Lib;
open Portable;

fun PP_THEORY_ERR f m =
       HOL_ERR{origin_structure = "TheoryPP",
               origin_function = f, message = m};


(*---------------------------------------------------------------------------*
 * Get "trav" from Term.                                                     *
 *---------------------------------------------------------------------------*)
local val trav_ref = ref(fn _:Term.term->unit => fn _:Term.term => ())
      val _ = Term.TheoryPP_init trav_ref
in
  val trav = !trav_ref
end;


val concat = String.concat;
val sort = Lib.sort (fn s1:string => fn s2 => s1<=s2);
val psort = Lib.sort (fn (s1:string,_:Thm.thm) => fn (s2,_:Thm.thm) => s1<=s2);
val thid_sort = Lib.sort (fn (s1:string,_:int,_:int) => fn (s2,_,_) => s1<=s2);
fun thm_terms th = Thm.concl th :: Thm.hyp th;


fun Thry s = s^"Theory";
fun ThrySig s = Thry s

type thm_printer = ppstream -> thm -> unit
type type_printer = ppstream -> hol_type -> unit
type HOLprinters = {pp_thm : thm_printer, pp_type : type_printer}

fun print_type_to_SML mvartype mtype pps ty = let
  open Portable Type
  val print_type_to_SML = print_type_to_SML mvartype mtype pps
in
  if (is_vartype ty) then
    add_string pps (mvartype^quote (dest_vartype ty))
  else let
    val {Tyop, Args} = dest_type ty
  in
    add_string pps mtype;
    begin_block pps CONSISTENT 0;
    add_string pps (quote Tyop);
    add_break pps (1,0);
    add_string pps "[";
    begin_block pps CONSISTENT 0;
    pr_list print_type_to_SML (fn () => add_string pps ",")
    (fn () => add_break pps (1,0)) Args;
    end_block pps;
    add_string pps "]";
    end_block pps
  end
end

fun with_parens pfn pp x = let
  open Portable
in
  add_string pp "("; pfn pp x; add_string pp ")"
end



fun pp_theory_sig thm_printer ppstrm info_record = let
  val {name,parents,axioms,definitions,theorems,sig_ps} = info_record
  val pp_thm =
    case thm_printer of
      SOME ppfn => ppfn ppstrm
    | NONE => (fn thm => add_string ppstrm "No theorem printer installed")
  val {add_string,add_break,begin_block,end_block,
          add_newline,flush_ppstream,...} =
                 Portable.with_ppstream ppstrm
  val parents' = sort parents
  val axioms' = psort axioms
  val definitions' = psort definitions
  val theorems' = psort theorems
  val thml = axioms@definitions@theorems
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
    (begin_block CONSISTENT 0;
     add_string (String.concat ["[", s, "]"]);
     add_break(2,0);
     add_string class;
     add_break(2,0);
     Lib.with_flag(Globals.show_tags,true)
     (Lib.with_flag(Globals.show_assums, true) pp_thm) th;
     end_block())
  fun pr_thms _ [] = ()
    | pr_thms heading plist =
    ( begin_block CONSISTENT 0;
     pr_list (pr_thm heading)
     (fn () => ())
     (fn () => (add_newline(); add_newline()))
     plist;
     end_block();
     add_newline(); add_newline())
  fun pr_sig_ps NONE = ()  (* won't be fired because of filtering below *)
    | pr_sig_ps (SOME pp) =
    (begin_block CONSISTENT 0; pp ppstrm; end_block());

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

fun hash_type ty n = hash(Type.dest_vartype ty) (0,n)
  handle HOL_ERR _ => let val {Tyop,Args} = Type.dest_type ty
              in itlist hash_type Args (hash Tyop (0,n))  end;


fun dest_atom tm =
  (Term.dest_var tm handle HOL_ERR _ => Term.dest_const tm)
  handle HOL_ERR _ => raise PP_THEORY_ERR"dest_atom" "not an atom";

fun hash_atom tm n =
    let val {Name,Ty} = dest_atom tm
    in hash_type Ty (hash Name (0,n))
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
        | loop ((x,index)::rst) = if (x=tm) then () else loop rst
  in
    loop els
  end;


(*---------------------------------------------------------------------------
 * Get the vector index of an atom.
 *---------------------------------------------------------------------------*)

fun index tm =
  let val i = hash_atom tm 0
      val els = Array.sub(share_table, i)
      fun loop [] = raise PP_THEORY_ERR"index" "not found in table"
        | loop ((x,index)::rst) = if (x=tm) then index else loop rst
  in
    loop els
  end;


val pp_raw = Term.pp_raw_term index;

local val output = Portable.output
      val std_out = Portable.std_out
      val flush_out = Portable.flush_out
in
fun check V thml =
  let val _ = Lib.mesg true "Checking consistency of sharing scheme"
      fun chk tm =
         if (Vector.sub(V, index tm) = tm)
          then ()
           else (Lib.mesg true "FAILURE in sharing scheme!";
                 raise PP_THEORY_ERR"check" "failure in sharing scheme")
  in List.app (app (trav chk) o thm_terms o snd) thml;
     Lib.mesg true "Completed successfully"
  end
end;


fun share_thy check_share thms =
  let val _ = reset_share_table()
      val _ = List.app (app (trav add) o thm_terms o snd) thms
      val L0 = Array.foldr (op @) [] share_table
      val L1 = Lib.sort (fn (_,i0) => fn (_,i1) => i0<=i1) L0
      val slist = map fst L1
      val _ = if check_share then check (Vector.fromList slist) thms else ()
  in
    slist
  end;

(*---------------------------------------------------------------------------
 * One needs to replace a backslash by two backslashes because one of them
 * disappears when sent through "output". (Occurrences of " inside a string
 * have a similar problem.) One also needs to add string quotes at each end
 * of the string.
 *---------------------------------------------------------------------------*)
local fun needs_backslash s =
         let fun loop i =
             let val c = String.sub(s,i)
             in (c = #"\\") orelse (c = #"\"") orelse loop (i+1)
             end handle Subscript => false
         in loop 0 end
fun add_backslashes s =
        let fun add i A = add (i+1)
              (let val c = String.sub(s,i)
               in if ((c = #"\\") orelse (c = #"\"")) then  (c:: #"\\" ::A)
                  else c::A end)
               handle Subscript => String.implode(rev (#"\""::A))
        in add 0 [#"\""]
        end
in
fun stringify s =
 if (Lexis.ok_identifier s orelse not(needs_backslash s))
 then Lib.quote s
 else add_backslashes s;
end;


(*---------------------------------------------------------------------------
 *  Print a theory as a module.
 *---------------------------------------------------------------------------*)

val swap_fregs_def = "\n\
\fun swap_grefs () = let\n\
\  val tmpvalue = !internal_grammar_ref\n\
\in\n\
\  internal_grammar_ref := (Parse.type_grammar(), Parse.term_grammar());\n\
\  Parse.temp_set_grammars tmpvalue\n\
\end\n"

fun pp_theory_struct ppstrm prelude_string info_record = let
  open Term
   val {theory as (name,i1,i2), parents,
        axioms,definitions,theorems,types,constants,struct_ps} = info_record
     val {add_string,add_break,begin_block,end_block, add_newline,
          flush_ppstream,...} = Portable.with_ppstream ppstrm
     val pp_tm = pp_raw ppstrm
     val pp_ty = with_parens (print_type_to_SML "U" "T") ppstrm
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
            add_break(0,0); add_string(Lib.int_to_string i); add_string",";
            add_break(0,0); add_string(Lib.int_to_string j);
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
     fun pr_fields{Name,Ty} =
         (begin_block CONSISTENT 0;
          add_string(stringify Name); add_break(1,0);
          pp_ty Ty; end_block())
     fun pr_atom a =
           (begin_block INCONSISTENT 2;
            add_string (if (is_var a) then "V " else "C ");
            pr_fields (dest_var a handle HOL_ERR _ => dest_const a);
            end_block())
        handle HOL_ERR _ =>
           raise PP_THEORY_ERR"pp_theory_struct.pr_atom" "not atomic"
     fun pr_bind (s,th) =
      let val (tg,asl,w) = (Thm.tag th, Thm.hyp th, Thm.concl th)
      in
         begin_block INCONSISTENT 2;
         add_string"val"; add_break(1,0); add_string s; add_break (1,0);
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

     fun bind_theorems () = if (null thml) then ()
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
      add_string (concat ["structure ",Thry name," :> ", ThrySig name," ="]);
      add_newline();
      begin_block CONSISTENT 2;
      add_string "struct"; add_newline();
      begin_block CONSISTENT 0;
      add_string"type thm = Thm.thm"; add_newline();
      add_string"fun C s q = Term.mk_const{Name=s,Ty=q}"; add_newline();
      add_string"fun V s q = Term.mk_var{Name=s,Ty=q}"; add_newline();
      add_string"fun T s args = Type.mk_type{Tyop = s, Args = args}";
   (*   add_string("val _ = print \"Loading theory: "^Thry name^"\\n\""); *)
      add_newline();
      add_string"val U = Type.mk_vartype"; add_newline();
      add_newline();
      add_string prelude_string;
      add_newline();
      pblock ("Parents", add_string o pparent, thid_sort parents);
      add_newline();
      pp_incorporate theory parents types constants; add_newline();
      bind_theorems (); add_newline();
      dblist(); add_newline();
      pr_psl struct_ps;
      end_block();
      end_block();
      add_break(0,0); add_string"end"; add_newline();
      end_block();
      flush_ppstream()
   end;

end;
