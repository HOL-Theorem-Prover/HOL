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

fun occurs s1 s2 =
    not(Substring.isEmpty (#2(Substring.position s1 (Substring.all s2))));

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

fun thm_class thy name =
    let val db = CT()
       val thymap = #1 (Map.find(db, toLower (norm_thyname thy)))
                     handle Map.NotFound =>
                            raise ERR "thm_class" "no such theory"
        val result = Map.find(thymap, toLower name)
                     handle Map.NotFound =>
                            raise ERR "thm_class" "not found"
    in
      case filter (equal (norm_thyname thy,name) o fst) result of
        [(_,p)] => p
      | [] => raise ERR "thm_class" "not found"
      | other => raise ERR "thm_class" "multiple things with the same name"
    end

fun fetch s1 s2 = fst (thm_class s1 s2);

fun thm_of ((_,n),(th,_)) = (n,th);
fun is x (_,(_,cl)) = (cl=x)

val thms        = List.map thm_of o thy
val theorems    = List.map thm_of o Lib.filter (is Thm) o thy
val definitions = List.map thm_of o Lib.filter (is Def) o thy
val axioms      = List.map thm_of o Lib.filter (is Axm) o thy

fun theorem s = let
  val (thm,c) = thm_class "-" s
      handle HOL_ERR _ => raise ERR "theorem" "No theorem of that name"
in
  if c = Thm  then thm
  else raise ERR "theorem" "No theorem of that name"
end

fun definition s = let
  val (thm,c) = thm_class "-" s
      handle HOL_ERR _ => raise ERR "definition" "No definition of that name"
in
  if c = Def then thm
  else raise ERR "theorem" "No definition of that name"
end

fun axiom s = let
  val (thm,c) = thm_class "-" s
      handle HOL_ERR _ => raise ERR "axiom" "No axiom of that name"
in
  if c = Axm then thm
  else raise ERR "axiom" "No axiom of that name"
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
      (add_string"<STRONG>"; add_string (colour s "black");
       add_string"</STRONG>")
  fun STRONG s =
      (add_string"<STRONG>";
       add_string
         (String.concat["<font size=+3 color=\"black\">",s,"</font>"]);
       add_string"</STRONG>")
  fun title s = add_string(String.concat
                             ["<H1><font color=\"black\">",s,"</font></H1>"]);
  fun link (l,s) =
      (add_string("<A HREF = "^Lib.quote l^">");
       strong s;
       add_string"</A>")
  fun HR() = (add_newline();add_string"<HR>";add_newline());

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
             add_string (colour"Type" "crimson"); add_break (1,0);
             add_string "<th>"; add_break (1,0);
             add_string (colour"Arity" "crimson");
             end_block();
             pr_list (fn x => (add_string"<tr>"; ob_pr1 x))
                     (fn () => ()) add_newline obs1;
             add_newline())
        ; if null consts then ()
          else
            (begin_block CONSISTENT 0;
             add_string "<tr>"; add_break (1,0);
             add_string "<th>"; add_break (1,0);
             add_string (colour"Constant" "crimson"); add_break (1,0);
             add_string "<th>"; add_break (1,0);
             add_string (colour"Type" "crimson");
             end_block();
             pr_list (fn x => (add_string"<tr>"; ob_pr2 x))
                     (fn () => ()) add_newline obs2;
             add_newline())
        ; end_block(); add_newline();
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
                          add_string"<PRE>";
                          add_newline();
                          pp_thm th;
                          add_newline();
                          add_string"</PRE>";
                          add_newline();
                          end_block())),    ths)
in
   begin_block CONSISTENT 0;
   add_string "<HTML>"; add_newline();
   add_string("<HEAD><TITLE>Theory: "^theory_name^"</TITLE>");
   add_string("<meta http-equiv=\"content-type\"\
              \ content=\"text/html;charset=UTF-8\">");
   add_newline();
   add_string("</HEAD>");
   add_newline();
   add_string "<BODY bgcolor=linen text=midnightblue>";
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
                  add_string (Lib.int_to_string Arity); end_block())),
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
   add_string "</BODY>"; add_newline();
   add_string "</HTML>"; add_newline();
   end_block()
end;

fun print_theory_as_html s path =
   let val name = (case s of "-" => current_theory() | other => s)
       val ostrm = Portable.open_out path
   in
     PP.with_pp {consumer = Portable.outputc ostrm, linewidth = 78,
                 flush = fn () => Portable.flush_out ostrm}
        (Lib.C pp_theory_as_html name)
     handle e => (Portable.close_out ostrm; raise e);
     Portable.close_out ostrm
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
   val cl_s = if cl = Thm then "THEOREM" else
	   if cl = Axm then "AXIOM" else
	   "DEFINITION";
   val s = th^"Theory."^name^" ("^cl_s^")\n";
   val size = String.size s
   fun line 0 l = l
     | line n l = line (n-1) ("-"^l)
   val s = s^(line (size-1) "\n")

   val s = s^Parse.thm_to_string thm^"\n";
in
   s
end;


val data_list_to_string = (foldl (fn (d, s) => s^(data_to_string d)^"\n\n") "\n\n\n");

val print_apropos = print o data_list_to_string o apropos;
val print_find = print o data_list_to_string o find;
fun print_match x1 x2 = print (data_list_to_string (match x1 x2));

end
