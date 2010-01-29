(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(*   A database of lemmas. This is currently accessible in the               *)
(*   following ways:                                                         *)
(*                                                                           *)
(*     - strings used to denote (part of) the name of the binding,           *)
(*       or the full name of the theory of interest. Case is not             *)
(*       significant.                                                        *)
(*                                                                           *)
(*     - a general matcher on the term structure of theorems.                *)
(*                                                                           *)
(*     - matching (higher order) on the term structure of theorems.          *)
(*                                                                           *)
(*     - looking up a specific theorem in a specific segment.                *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

structure DB :> DB =
struct

open HolKernel;
type theory = Hol_pp.theory;

val ERR = mk_HOL_ERR "DB";

datatype class = Thm | Axm | Def
fun indef_class2string Thm = "a theorem"
  | indef_class2string Axm = "an axiom"
  | indef_class2string Def = "a definition"


(*---------------------------------------------------------------------------
    The pair of strings is theory * bindname
 ---------------------------------------------------------------------------*)

type data    = (string * string) * (thm * class)


(*---------------------------------------------------------------------------
   Map keys to canonical case
 ---------------------------------------------------------------------------*)

fun toLower s =
 let open Char CharVector in tabulate(size s, fn i => toLower(sub(s,i))) end

(*---------------------------------------------------------------------------
     Persistence: bindl is used to populate the database when a theory
     is loaded.
 ---------------------------------------------------------------------------*)

structure Map = struct open Redblackmap end
(* the keys are lower-cased, but the data also stores the keys, and there
   the key infomration is kept in its original case *)

(* the submap is a map from lowercased item-name to those items with the
   same name.  There is a list of them because item-names are really
   case-sensitive *)
type submap = (string, data list) Map.dict
val empty_sdata_map = Map.mkDict String.compare

(* the dbmap is a map from lowercased theory-name to a submap (as above)
   and a map from exact theory name to a list of items.  These items are
   stored in the order they were made.  For the sake of clarity, call the
   latter sort of map an ordermap. *)
type dbmap = (string, submap * submap) Map.dict

local val DBref = ref (Map.mkDict String.compare) : dbmap ref
      fun lemmas() = !DBref
      fun add_to_submap m (newdata as ((s1, s2), x)) =
          let val s2key = toLower s2
              val oldvalue = case Map.peek(m, s2key) of
                               NONE => []
                             | SOME items => items
          in
            Map.insert(m, s2key, newdata :: oldvalue)
          end
      fun add_to_ordermap om thyname blist =
          let val oldvalue = case Map.peek(om, thyname) of
                               NONE => []
                             | SOME items => items
          in
            Map.insert(om, thyname, blist @ oldvalue)
          end
      fun functional_bindl db thy blist =
          (* used when a theory is loaded from disk *)
          let val thykey = toLower thy
              val (submap, ordermap) =
                  case Map.peek(db, thykey) of
                    NONE => (empty_sdata_map, empty_sdata_map)
                  | SOME m => m
              fun foldthis ((n,th,cl), m) = add_to_submap m ((thy,n), (th,cl))
              val submap' = List.foldl foldthis submap blist
              val ordermap' =
                  add_to_ordermap
                    ordermap thy
                    (map (fn (n,th,cl) => ((thy,n), (th, cl))) blist)
          in
            Map.insert(db, thykey, (submap', ordermap'))
          end
      fun bind_with_classfn thy cl thlist db =
          (* used to update a database with all of the current segment's
             theorems.  The latter are a moving target, so needs to be done
             multiple times.  Note that the result of this operation is
             not stored back into the reference cell, so there aren't
             multiple copies of the current segment in what DB stores.

             An alternative approach would be to augment the Theory module
             with a "theorem registration scheme", so that later modules
             could be informed whenever a new theorem was added to the current
             segment.  A function to clear things out would also need to
             be registered with after_new_theory so that theorems could be
             dropped if a segment was restarted. *)
          let val thykey = toLower thy
              val (submap, ordermap) =
                  case Map.peek(db, thykey) of
                    NONE => (empty_sdata_map, empty_sdata_map)
                  | SOME m => m
              fun foldthis ((n, th), m) = add_to_submap m ((thy,n),(th, cl))
              val submap' = List.foldl foldthis submap thlist
              val ordermap' =
                  add_to_ordermap
                    ordermap thy
                    (map (fn (n, th) => ((thy,n), (th, cl))) thlist)
          in
            Map.insert(db, thykey, (submap', ordermap'))
          end
in
fun bindl thy blist = DBref := functional_bindl (lemmas()) thy blist

(*---------------------------------------------------------------------------
    To the database representing all ancestor theories, add the
    entries in the current theory segment.
 ---------------------------------------------------------------------------*)

fun CT() =
  let val thyname = Theory.current_theory()
  in
    (bind_with_classfn thyname Def (rev (Theory.current_definitions ())) o
     bind_with_classfn thyname Axm (rev (Theory.current_axioms ())) o
     bind_with_classfn thyname Thm (rev (Theory.current_theorems ())))
    (lemmas())
  end
end (* local *)


(*---------------------------------------------------------------------------
     Misc. support
 ---------------------------------------------------------------------------*)

val occurs = String.isSubstring

fun norm_thyname "-" = current_theory()
  | norm_thyname s = s;


(*---------------------------------------------------------------------------
     thy  : All entries in a specified theory
     find : Look up something by name fragment
 ---------------------------------------------------------------------------*)

fun thy s =
    case Map.peek(CT(), toLower (norm_thyname s)) of
      NONE => []
    | SOME (m, om) => let
      in
        case Map.peek (om, norm_thyname s) of
          NONE => []
        | SOME x => x
      end

fun find s =
    let val s = toLower s
        fun subfold (k, v, acc) = if occurs s k then v @ acc else acc
        fun fold (thy, (m, _), acc) = Map.foldr subfold acc m
    in
      Map.foldr fold [] (CT())
    end


(*---------------------------------------------------------------------------
      Look up something by matching. Parameterized by the matcher.
 ---------------------------------------------------------------------------*)

fun matchp P thylist =
    let fun data_P (_, (th, _)) = P th
        fun subfold (k, v, acc) = List.filter data_P v @ acc
    in
      case thylist of
        [] => let fun fold (k, (m, _), acc) = Map.foldr subfold acc m
              in
                Map.foldr fold [] (CT())
              end
      | _ => let val db = CT()
                 fun fold (thyn, acc) =
                     case Map.peek(db, toLower (norm_thyname thyn)) of
                       NONE => acc
                     | SOME (m, _) => Map.foldr subfold acc m
             in
               List.foldr fold [] thylist
             end
    end


fun matcher f thyl pat =
  matchp (fn th => can (find_term (can (f pat))) (concl th)) thyl;

val match = matcher (ho_match_term [] empty_tmset);
val apropos = match [];


fun listDB () =
    let fun subfold (k,v,acc) = v @ acc
        fun fold (_, (m, _), acc) = Map.foldr subfold acc m
    in
      Map.foldr fold [] (CT())
    end

(*---------------------------------------------------------------------------
      Some other lookup functions
 ---------------------------------------------------------------------------*)

fun thm_class origf thy name = let
  val db = CT()
  val thy = norm_thyname thy
  val nosuchthm = ("theorem "^thy^"$"^name^" not found")
  val thymap = #1 (Map.find(db, toLower thy))
               handle Map.NotFound => raise ERR origf ("no such theory: "^thy)
  val result = Map.find(thymap, toLower name)
               handle Map.NotFound => raise ERR origf nosuchthm
in
  case filter (equal (norm_thyname thy,name) o fst) result of
    [(_,p)] => p
  | [] => raise ERR origf nosuchthm
  | other => raise ERR origf
                       ("multiple things in theory "^thy^" with name "^name)
end

fun fetch s1 s2 = fst (thm_class "fetch" s1 s2);

fun thm_of ((_,n),(th,_)) = (n,th);
fun is x (_,(_,cl)) = (cl=x)

val thms        = List.map thm_of o thy
val theorems    = List.map thm_of o Lib.filter (is Thm) o thy
val definitions = List.map thm_of o Lib.filter (is Def) o thy
val axioms      = List.map thm_of o Lib.filter (is Axm) o thy

fun theorem s = let
  val (thm,c) = thm_class "theorem" "-" s
in
  if c = Thm then thm
  else raise ERR "theorem" ("No theorem in current theory of name "^s^
                            " (but there is "^indef_class2string c^")")
end

fun definition s = let
  val (thm,c) = thm_class "definition" "-" s
in
  if c = Def then thm
  else raise ERR "theorem" ("No definition in current theory of name "^s^
                            " (but there is "^indef_class2string c^")")
end

fun axiom s = let
  val (thm,c) = thm_class "axiom" "-" s
in
  if c = Axm then thm
  else raise ERR "axiom" ("No axiom in current theory of name "^s^
                          " (but there is "^indef_class2string c^")")
end
(*---------------------------------------------------------------------------
     Support for print_theory
 ---------------------------------------------------------------------------*)

fun dest_theory s =
 let val thyname = if s = "-" then Theory.current_theory () else s
 in
   Hol_pp.THEORY (thyname,
    {types = rev (Theory.types thyname),
     consts = rev (map dest_const (Theory.constants thyname)),
     parents = Theory.parents thyname,
     axioms = axioms thyname,
     definitions = definitions thyname,
     theorems = theorems thyname})
 end
 handle e => raise ERR "dest_theory" (Lib.quote s^" is not a known theory");

fun outstreamConsumer ostrm =
    {consumer = fn s => TextIO.output(ostrm,s),
     flush = fn () => (TextIO.output(ostrm,"\n"); TextIO.flushOut ostrm),
     linewidth = !Globals.linewidth};

fun print_theory_to_outstream thy ostrm =
 PP.with_pp (outstreamConsumer ostrm)
            (C Hol_pp.pp_theory (dest_theory thy));

fun print_theory thy = print_theory_to_outstream thy TextIO.stdOut;

fun print_theory_to_file thy file =
  let open TextIO
      val ostrm = openOut file
  in print_theory_to_outstream thy ostrm
   ; closeOut ostrm
  end
  handle e => raise wrap_exn "DB" "print_theory_to_file" e;


(*---------------------------------------------------------------------------
     Print a theory as HTML
 ---------------------------------------------------------------------------*)

fun pp_theory_as_html ppstrm theory_name = let
  open Portable Hol_pp
  val THEORY(_,{parents,types, consts,
                axioms, definitions, theorems}) = dest_theory theory_name
  val {add_string,add_break,begin_block,end_block,
       add_newline,flush_ppstream,...} = with_ppstream ppstrm
  val pp_thm  = pp_thm ppstrm
  val pp_type = pp_type ppstrm
  fun colour thing col =
      String.concat["<font color=\"",col,"\">",thing,"</font>"];
  fun strong s =
      (add_string"<span class=\"strong\">"; add_string s;
       add_string"</span>")
  fun STRONG s =
      (add_string"<span class=\"vstrong\">";
       add_string s;
       add_string"</span>")
  fun title s = add_string(String.concat ["<h1>",s,"</h1>"]);
  fun link (l,s) =
      (add_string("<a href = "^Lib.quote l^">");
       strong s;
       add_string"</a>")
  fun HR() = (add_newline();add_string"<hr>";add_newline());

  fun pblock(ob_pr, obs) =
      ( begin_block CONSISTENT 4;
          STRONG "Parents";
          add_string "&nbsp;&nbsp;&nbsp;&nbsp;";
          add_break (1,0);
          pr_list ob_pr (fn () => add_string"&nbsp;&nbsp;")
                  (fn () => add_break (1,0)) obs;
        end_block();
        add_newline();
        add_newline())

  fun sig_block(ob_pr1, obs1, ob_pr2,obs2) =
      if null types andalso null consts then ()
      else
        ( title "Signature"; add_newline();
          begin_block CONSISTENT 4;
            begin_block CONSISTENT 0;
              add_string "<center>"; add_newline();
              add_string "<table BORDER=4 CELLPADDING=10 CELLSPACING=1>";
              add_newline();
            end_block();
            add_newline();
            if null types then ()
            else
              (begin_block CONSISTENT 0;
                 add_string "<tr>"; add_break (1,0);
                 add_string "<th>"; add_break (1,0);
                 add_string "Type"; add_break (1,0);
                 add_string "<th>"; add_break (1,0);
                 add_string "Arity";
               end_block();
               pr_list (fn x => (add_string"<tr>"; ob_pr1 x))
                       (fn () => ()) add_newline obs1;
               add_newline());
            if null consts then ()
            else
              (begin_block CONSISTENT 0;
                 add_string "<tr>"; add_break (1,0);
                 add_string "<th>"; add_break (1,0);
                 add_string "Constant"; add_break (1,0);
                 add_string "<th>"; add_break (1,0);
                 add_string "Type" ;
               end_block();
               pr_list (fn x => (add_string"<tr>"; ob_pr2 x))
                       (fn () => ()) add_newline obs2;
               add_newline());
          end_block(); add_newline();
          begin_block CONSISTENT 0;
            add_string "</table>"; add_newline();
            add_string "</center>"; add_newline();
          end_block();
          add_newline())

  fun dl_block(header, ob_pr, obs) =
      ( begin_block CONSISTENT 0;
          title header;
          add_newline();
          add_string"<DL>"; add_newline();
          pr_list
            (fn (x,ob) =>
                (begin_block CONSISTENT 0;
                   add_string"<DT>"; strong x; add_newline();
                   add_string"<DD>"; add_newline();
                   ob_pr ob;
                 end_block()))
            (fn () => ()) add_newline obs;
          add_newline();
          add_string"</DL>";
        end_block();
        add_newline();
        add_newline())

  fun pr_thm (heading, ths) =
      dl_block(heading,
               (fn th => (begin_block CONSISTENT 0;
                            add_string"<pre>";
                            add_newline();
                            pp_thm th;
                            add_newline();
                            add_string"</pre>";
                            add_newline();
                          end_block())),    ths)
  fun NL() = add_newline()
in
   begin_block CONSISTENT 0;
     add_string "<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01//EN\">";
     add_newline();

     add_string "<html>"; add_newline();
     add_string("<head><title>Theory: "^theory_name^"</title>");
     add_string("<meta http-equiv=\"content-type\"\
                \ content=\"text/html;charset=UTF-8\">");
     add_newline();
     add_string("<style type=\"text/css\">"); NL();
     add_string "<!--\n\
                \  body {background: #faf0e6; color: #191970; }\n\
                \  span.freevar  { color: blue}\n\
                \  span.boundvar { color: green}\n\
                \  span.typevar  { color: purple}\n\
                \  span.type     { color: teal}\n\
                \  span.strong   { color: black; font-weight: bold}\n\
                \  span.vstrong  { color: black; \n\
                \                  font-weight: bold;\n\
                \                  font-size: larger}\n\
                \  h1 {color: black}\n\
                \  th {color: crimson}\n\
                \-->";
     NL(); add_string "</style>"; NL();
     add_string("</head>");
     add_newline();
     add_string "<body>";
     add_newline();
     title ("Theory \""^theory_name^"\"");
     add_newline() ;

     if null parents then ()
     else pblock ((fn n => link(n^"Theory.html",n)), parents) ;
     sig_block((fn (Name,Arity) =>
                   (begin_block CONSISTENT 0;
                      add_string"<td>"; add_break(1,0); strong Name;
                      add_break(1,0);
                      add_string"<td>"; add_break(1,0);
                      add_string (Lib.int_to_string Arity);
                    end_block())),
               types,
               (fn (Name,Ty) =>
                   (begin_block CONSISTENT 0;
                      add_string"<td>"; add_break(1,0); strong Name;
                      add_break(1,0);
                      add_string"<td>"; add_break(1,0); pp_type Ty;
                    end_block())), consts)
   ; if null axioms then () else pr_thm ("Axioms", axioms)
   ; if null definitions then ()
     else (if null axioms then () else (HR();HR());
           pr_thm ("Definitions", definitions))
   ; if null theorems then ()
     else (if null axioms andalso null definitions then ()
           else (HR();HR());
           pr_thm ("Theorems", theorems));
     add_newline();
     HR();
     add_string "</body>"; add_newline();
     add_string "</html>"; add_newline();
   end_block()
end;

fun print_theory_as_html s path = let
  val name = (case s of "-" => current_theory() | other => s)
  val ostrm = Portable.open_out path
  val oldbackend = !Parse.current_backend
  val _ = Parse.current_backend := PPBackEnd.raw_terminal
          (* would like this to be html_terminal, but it causes
             occasional exceptions *)
  fun finalise() = (Parse.current_backend := oldbackend; TextIO.closeOut ostrm)
in
  PP.with_pp {consumer = (fn s => TextIO.output(ostrm,s)),
              linewidth = 78,
              flush = fn () => TextIO.flushOut ostrm}
             (Lib.C pp_theory_as_html name)
             handle e => (finalise(); raise e);
  finalise()
end;

fun html_theory s = print_theory_as_html s (s^"Theory.html");

(*---------------------------------------------------------------------------
    Refugee from Parse structure
 ---------------------------------------------------------------------------*)

fun export_theory_as_docfiles dirname =
    Parse.export_theorems_as_docfiles dirname
                                      (axioms "-" @ definitions "-" @
                                       theorems "-");





fun data_to_string (((th,name),(thm,cl)):data) =
let
   open PPBackEnd Parse
   val cl_s = if cl = Thm then "THEOREM" else
	   if cl = Axm then "AXIOM" else
	   "DEFINITION";
   val name_style = add_style_to_string [Bold] name

   val s = th^"Theory."^name^" ("^cl_s^")\n";
   val s_style = (th^"Theory.")^name_style^" ("^cl_s^")\n";
   val size = String.size s
   fun line 0 l = l
     | line n l = line (n-1) ("-"^l)
   val s = s_style^(line (size-1) "\n")^thm_to_backend_string thm^"\n";
in
   s
end;


val data_list_to_string = (foldl (fn (d, s) => s^(data_to_string d)^"\n\n") "\n\n\n");

val print_apropos = print o data_list_to_string o apropos;
val print_find = print o data_list_to_string o find;
fun print_match x1 x2 = print (data_list_to_string (match x1 x2));


end
