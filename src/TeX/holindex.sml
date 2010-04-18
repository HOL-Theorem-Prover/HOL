structure holindex :> holindex =
struct

open Lib Feedback HolKernel Parse boolLib mungeTools holindexData

(******************************************************************************)
(* Some datastructures to store all the necessary information in              *)
(******************************************************************************)

val default_linewidth_ref = ref 80;


(******************************************************************************)
(* Parse the input file                                                       *)
(******************************************************************************)


(*
   val file = "/home/tt291/Documents/thesis/holmunge/test.hix";
   val ds = new_data_store ();
   val l = Portable.input_line fh;
*)

local
   fun is_not_space c = not (Char.isSpace c)
   fun is_lbrace c = c = #"{"
   fun is_not_rbrace c = not (c = #"}")

   fun space_trim ls =
      Substring.dropr Char.isSpace (Substring.dropl Char.isSpace ls)

   val tokenfun_space = Substring.splitl is_not_space
   fun tokenfun_brace ls = 
       let 
           val (ls1, ls2) = Substring.splitl is_not_rbrace ls;
           val ls1' = Substring.triml 1 ls1
           val ls2' = Substring.triml 1 ls2
       in
           (ls1', ls2')
       end;
   fun tokenfun ls = if is_lbrace (valOf(Substring.first ls)) then 
            tokenfun_brace ls else tokenfun_space ls

   fun parse_substring ls = 
      if Substring.isEmpty ls then [] else
      let
         val (ls1, ls2) = tokenfun ls
         val ls1' = space_trim ls1
         val ls2' = space_trim ls2
      in
         ls1'::(parse_substring ls2')            
      end;

in

fun tokenise_hix_line l =
let
   val sl = Substring.full l;
   val sll = parse_substring sl;
   val ll = List.map Substring.string sll
in
   ll
end;

end;



fun process_hix_line basedir ds l = 
let
   val ll = tokenise_hix_line l;
in
   case ll of
     ["Definition", ty_arg, id_arg, label_arg, content_arg] =>
         update_data_store ds (get_data_store_keys ty_arg id_arg)
         (fn ent => data_entry___update_label (SOME label_arg)
             (data_entry___update_content content_arg ent))
   | ["Print", ty_arg, id_arg, page_arg] =>
         update_data_store ds (get_data_store_keys ty_arg id_arg)
         (data_entry___add_page page_arg)
   | ["Reference", ty_arg, id_arg, page_arg] =>
         update_data_store ds (get_data_store_keys ty_arg id_arg)
         ((data_entry___add_page page_arg) o
          (data_entry___update_in_index true))
   | ["Index", ty_arg, id_arg] =>
         update_data_store ds (get_data_store_keys ty_arg id_arg)
         (data_entry___update_in_index true)
   | ["FormatOptions", ty_arg, id_arg, options_arg] =>
         update_data_store ds (get_data_store_keys ty_arg id_arg)
         (data_entry___update_options options_arg)
   | ["Linewidth", length_arg] =>
         let
            val n_opt = Int.fromString length_arg
            val _ = if isSome n_opt then (default_linewidth_ref := valOf n_opt) else ();
         in
            ds
         end
   | ["UseFile", filename] =>
         (let
            val file = if Path.isAbsolute filename then filename else
               Path.concat (basedir, filename) 
            val entryL = AssembleHolindexParser.parse_hdf_file file;
         in
            foldl (fn (de, ds) => parse_entry___add_to_data_store ds de) ds
            entryL
         end handle Interrupt => raise Interrupt
                  | _ => (print ("Error while parsing '"^filename^"' in '"^basedir^"'\n");ds))
   | _ => ds
end; 


fun cleanup_data_store ds =
let
    fun cleanup_subdata_store sds =
    let
        val sdsL = Redblackmap.listItems sds
        val sdsL' = List.filter (data_entry_is_used o snd) sdsL;
        val sds' = List.foldr (fn ((k,v),ds) => 
            (Redblackmap.insert (ds, k, v))) new_data_substore sdsL'
    in
        sds'
    end;

    val dsL   = Redblackmap.listItems ds
    val dsL'  = List.map (fn (k, sds) => (k, cleanup_subdata_store sds)) dsL
    val dsL'' = List.filter (fn (k, sds) => not (Redblackmap.isEmpty sds)) dsL'
    val ds' = List.foldr (fn ((k,v),ds) => 
            (Redblackmap.insert (ds, k, v))) new_data_store dsL''
in
   ds'
end;

fun parse_hix file =
let
   val ds_ref = ref new_data_store;
   val fh = Portable.open_in file;
   val basedir = Path.dir file;

   val _ = while (not (Portable.end_of_stream fh)) do (
      ds_ref := process_hix_line basedir (!ds_ref) (Portable.input_line fh)
   );

   val _ = Portable.close_in fh
in
   cleanup_data_store (!ds_ref)
end;


fun holmunge_format command options content =
let
   val _ = if (content = "") then Feedback.fail() else ();
   val empty_posn = (0,0);
   val opts = mungeTools.parseOpts empty_posn ("alltt,"^options);
   val replacement_args = 
      {argpos = empty_posn, command=command, commpos = empty_posn,
       options = opts, argument=content};
   val width_opt = mungeTools.optset_width opts;
   val width = if isSome width_opt then valOf width_opt else (!default_linewidth_ref);
   val fs = Portable.pp_to_string width mungeTools.replacement replacement_args
in
   UTF8.translate (fn " " => "\\ "
                    | "\n" => "\\par "
                    | s => s) fs
end;


(*val os = Portable.std_out*)
fun output_holtex_def command definetype os (id,
  ({label    = label, 
    in_index = in_index, 
    options  = options,
    content  = content,
    pages    = pages}:data_entry)) =
let
   val cs = holmunge_format command options content;
   val _ = if (cs = "") then Feedback.fail() else ();
   val _ = Portable.output (os, definetype);
   val _ = Portable.output (os, id);
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, cs);
   val _ = Portable.output (os, "}\n");
in
  ()
end handle Interrupt => raise Interrupt
         | _ => ()



val output_holtex_type_def =
   output_holtex_def mungeTools.Type "\\defineHOLty{"

fun process_type_defs os ds =
let
    val type_entryL = (Redblackmap.listItems (Redblackmap.find (ds, "Type")))
          handle Redblackmap.NotFound => []
    val _ = List.map (output_holtex_type_def os) type_entryL
in
   ()
end;


val output_holtex_term_def =
   output_holtex_def mungeTools.Term "\\defineHOLtm{";

fun process_term_defs os ds =
let
    val term_entryL = (Redblackmap.listItems (Redblackmap.find (ds, "Term")))
          handle Redblackmap.NotFound => []
    val _ = List.map (output_holtex_term_def os) term_entryL
in
   ()
end;


val output_holtex_thm_def =
   output_holtex_def mungeTools.Theorem "\\defineHOLthm{";

fun process_thm_theory_defs os (theory,sds) =
let
    val thm_entryL = Redblackmap.listItems sds;
    fun mapfun (id, ({label    = label, 
                 in_index = in_index, 
                 options  = options,
                 content  = content,
                 pages    = pages}:data_entry)) =
               (theory^"."^id, 
                 {label    = label, 
                  in_index = in_index, 
                  options  = options,
                  content  = theory^"."^id,
                  pages    = pages}:data_entry);
    val thm_entryL' = List.map mapfun thm_entryL;
    val _ = List.map (output_holtex_thm_def os) thm_entryL'
in
   ()
end;

fun process_thm_defs os ds =
let
    val ds = (fst (Redblackmap.remove (ds, "Term"))) handle Redblackmap.NotFound => ds;
    val ds = (fst (Redblackmap.remove (ds, "Type"))) handle Redblackmap.NotFound => ds;

    val theory_entryL = Redblackmap.listItems ds;
    val _ = List.map (process_thm_theory_defs os) theory_entryL
in
   ()
end;

fun output_all_defs os ds =
let
   val _ = process_type_defs os ds;
   val _ = process_term_defs os ds;
   val _ = process_thm_defs os ds;
in
   ()
end;




exception nothing_to_do;

fun process_index_pages pages =
let
   val pL = Redblackset.listItems pages
   val pnL = List.map (fn s => (s, Int.fromString s)) pL
   val intL = List.map (fn p => (p,p)) pnL;

   fun make_intervals [] = []
     | make_intervals [pnp] = [pnp]
     | make_intervals ((pn, (p, NONE))::pnL) =
         (pn, (p, NONE))::(make_intervals pnL)
     | make_intervals (pnp::((p, NONE), pn)::pnL) =
         pnp::((p, NONE),pn)::(make_intervals pnL)
     | make_intervals ((pn1, (p1,SOME n1))::((p2, SOME n2), pn2)::pnL) =
         if (n2 = n1 + 1) then
            make_intervals ((pn1, pn2)::pnL)
         else
            (pn1, (p1,SOME n1))::make_intervals(((p2, SOME n2), pn2)::pnL)

   fun remove_intervals [] = []
     | remove_intervals (((p1:string, NONE:int option),_)::pnL) =
         p1::remove_intervals pnL
     | remove_intervals ((_, (p2, NONE:int option))::pnL) =
         p2::remove_intervals pnL
     | remove_intervals (((p1, SOME n1), (p2, SOME n2))::pnL) =
         if (n1 = n2) then
            p1::remove_intervals pnL
         else (if (n2 > n1 + 1) then
            ((String.concat [p1, "--", p2])::remove_intervals pnL)
         else (p1::p2::remove_intervals pnL))

   val sL = remove_intervals (make_intervals intL)
   val sL' = List.map (fn s => String.concat ["\\hyperpage{", s, "}"]) sL
in
   String.concat (commafy sL')
end;



fun output_holtex_index indextype os (id,
  ({label    = label_opt, 
    in_index = in_index, 
    options  = options,
    content  = content,
    pages    = pages}:data_entry)) =
let
   val label = if isSome label_opt then valOf(label_opt) else "";
   val _ = Portable.output (os, indextype);
   val _ = Portable.output (os, id);
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, label);
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, process_index_pages pages);
   val _ = Portable.output (os, "}\n");
in
  ()
end handle Interrupt => raise Interrupt
         | _ => ()


val output_holtex_type_index =
   output_holtex_index "      \\HOLTypeIndexEntry{";

fun process_type_index os ds =
let
    val type_entryL = (Redblackmap.listItems (Redblackmap.find (ds, "Type")))
          handle Redblackmap.NotFound => []
    val type_entryL' = List.filter (#in_index o snd) type_entryL;
    val _ = if null(type_entryL') then raise nothing_to_do else ();

    val _ = Portable.output(os, "   \\HOLBeginTypeIndex\n");
    val _ = List.map (output_holtex_type_index os) type_entryL'
in
   ()
end handle nothing_to_do => ();

val output_holtex_term_index =
   output_holtex_index "      \\HOLTermIndexEntry{"

fun process_term_index os ds =
let
    val term_entryL = (Redblackmap.listItems (Redblackmap.find (ds, "Term")))
          handle Redblackmap.NotFound => []
    val term_entryL' = List.filter (#in_index o snd) term_entryL;
    val _ = if null(term_entryL') then raise nothing_to_do else ();

    val _ = Portable.output(os, "   \\HOLBeginTermIndex\n");
    val _ = List.map (output_holtex_term_index os) term_entryL'
in
   ()
end handle nothing_to_do => ();


val output_holtex_thm_index =
   output_holtex_index "         \\HOLThmIndexEntry{";

fun process_thm_theory_index os (theory,sds) =
let
    val thm_entryL = Redblackmap.listItems sds;
    val thm_entryL' = List.filter (#in_index o snd) thm_entryL;
    val _ = if null(thm_entryL') then raise nothing_to_do else ();

    val tex_escape = UTF8.translate 
         (fn "_" => "\\_" | s => s)
    fun mapfun (id, ({label    = label, 
                 in_index = in_index, 
                 options  = options,
                 content  = content,
                 pages    = pages}:data_entry)) =
               (theory^"."^id, 
                 {label    = SOME (tex_escape id), 
                  in_index = in_index, 
                  options  = options,
                  content  = theory^"."^id,
                  pages    = pages}:data_entry);

    val thm_entryL'' = List.map mapfun thm_entryL'; 
    val _ = Portable.output(os, "      \\HOLThmIndexTheory{"^(tex_escape theory)^"}\n");
    val _ = List.map (output_holtex_thm_index os) thm_entryL''
in
   ()
end handle nothing_to_do => ();


fun process_thm_index os ds =
let
    val ds = (fst (Redblackmap.remove (ds, "Term"))) handle Redblackmap.NotFound => ds;
    val ds = (fst (Redblackmap.remove (ds, "Type"))) handle Redblackmap.NotFound => ds;

    val theory_entryL = Redblackmap.listItems ds;
    val _ = if null(theory_entryL) then raise nothing_to_do else ();

    val _ = Portable.output(os, "   \\HOLBeginThmIndex\n");
    val _ = List.map (process_thm_theory_index os) theory_entryL
in
   ()
end handle nothing_to_do => ();

fun output_all_index os ds =
let
   val _ = Portable.output (os, "\\defineHOLIndex{\n");
   val _ = process_type_index os ds;
   val _ = Portable.output (os, "\n");
   val _ = process_term_index os ds;
   val _ = Portable.output (os, "\n");
   val _ = process_thm_index os ds;
   val _ = Portable.output (os, "}\n");
in
   ()
end;


fun output_tix os ds =
let
   val _ = output_all_defs os ds;
   val _ = Portable.output (os, "\n\n\n");
   val _ = output_all_index os ds;
in
   ()
end;



(*
   val basename = "/home/tt291/Documents/thesis/holmunge/test";
*)

fun holindex basename =
let
    val ds = parse_hix (basename ^ ".hix")   
    val os = Portable.open_out (basename ^ ".tix")   
    val _ = output_tix os ds;
    val _ = Portable.close_out os;
in
    ()
end;

end
