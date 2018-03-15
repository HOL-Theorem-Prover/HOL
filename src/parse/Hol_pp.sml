structure Hol_pp :> Hol_pp =
struct

open HolKernel DB Parse;

(*--------------------------------------------------------------------------*
 * Prettyprint a theory for the user                                        *
 *--------------------------------------------------------------------------*)

val CONSISTENT   = Portable.CONSISTENT
val INCONSISTENT = Portable.INCONSISTENT;

fun pp_theory (THEORY(name, {parents, types, consts,
                             axioms,definitions,theorems})) =
let
  open smpp
  val pp_thm = lift pp_thm
  val pp_type = lift pp_type
  val nl2 = add_newline >> add_newline
  fun vspace l = if null l then nothing else nl2
  fun vblock(header, ob_pr, obs) =
    if null obs then nothing
    else
      block CONSISTENT 4 (
        add_string (header^":") >>
        add_newline >>
        pr_list ob_pr add_newline obs
      )
  fun pr_thm (heading, ths) =
    vblock(heading,
      (fn (s,th) => block CONSISTENT 0 (
                     add_string s >> add_newline >>
                     add_string "  " >>
                     pp_thm th
                   )
      ),
      Listsort.sort (inv_img_cmp #1 String.compare) ths)
  val longest_const_size =
      List.foldl (fn ((s,_),i) => Int.max(size s, i)) 0
                 consts
  val m =
    block CONSISTENT 0 (
      add_string ("Theory: "^name) >> nl2 >>
      vblock ("Parents", add_string, Listsort.sort String.compare parents) >>
      nl2 >>
      vblock ("Type constants",
              (fn (name,arity) =>
                  (add_string name >>
                   add_string (" "^Lib.int_to_string arity))),
              types) >>
      vspace types >>
      vblock ("Term constants",
              (fn (name,htype) =>
                  block CONSISTENT 0 (
                    add_string name >>
                    add_string (
                      CharVector.tabulate(longest_const_size + 3 - size name,
                                          K #" ")) >>
                    pp_type htype
                  )
              ),
              consts) >>
      vspace consts >>

      pr_thm ("Axioms", axioms) >> vspace axioms >>
      pr_thm ("Definitions", definitions) >> vspace definitions >>
      pr_thm ("Theorems", theorems)
    )
in
  Parse.mlower m
end;

(*---------------------------------------------------------------------------
     Support for print_theory
 ---------------------------------------------------------------------------*)

fun print_theory_to_outstream thy ostrm =
  HOLPP.prettyPrint((fn s => TextIO.output(ostrm, s)), 80)
                   (pp_theory (dest_theory thy))

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

(*
fun pp_theory_as_html ppstrm theory_name = let
  open Portable
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
*)
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
   val s = s_style^(line (size-1) "\n")^ppstring pp_thm thm^"\n";
in
   s
end;


val data_list_to_string = (foldl (fn (d, s) => s^(data_to_string d)^"\n\n") "\n\n\n");

val print_apropos = print o data_list_to_string o apropos;
val print_find = print o data_list_to_string o find;
fun print_match x1 x2 = print (data_list_to_string (match x1 x2));

end
