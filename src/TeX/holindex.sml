structure holindex :> holindex =
struct

open Lib Feedback HolKernel Parse boolLib mungeTools holindexData

(******************************************************************************)
(* Some datastructures to store all the necessary information in              *)
(******************************************************************************)

val default_linewidth_ref = ref 80;
val use_occ_sort_ref = ref false;

(******************************************************************************)
(* Parse the input file                                                       *)
(******************************************************************************)


(*
   val file = "/home/tt291/Documents/thesis/holmunge/test.hix";
   val ds = new_data_store ();
   val l = Portable.input_line fh;
*)

val error_found = ref false;
fun report_error e = (print e;print"\n";error_found := true);
fun report_warning e = (print e;print"\n");

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
         update_data_store (true, report_error)
         ds ty_arg id_arg
         (fn ent => data_entry___update_label (SOME label_arg)
             (data_entry___update_content (SOME content_arg) ent))
   | ["Printed", ty_arg, id_arg, page_arg] =>
         update_data_store (false, report_error) ds ty_arg id_arg
         ((data_entry___add_page page_arg) o
          (data_entry___update_printed true))
   | ["Reference", ty_arg, id_arg, page_arg] =>
         update_data_store (false, report_error) ds ty_arg id_arg
         ((data_entry___add_page page_arg) o
          (data_entry___update_in_index true))
   | ["ForceIndex", ty_arg, id_arg] =>
         update_data_store (false, report_error) ds ty_arg id_arg
         (data_entry___update_in_index true)
   | ["FullIndex", ty_arg, id_arg, f_arg] =>
         update_data_store (false, report_error) ds ty_arg id_arg
         (data_entry___update_full_index (f_arg = "true"))
   | ["FormatOptions", ty_arg, id_arg, options_arg] =>
         update_data_store (false, report_error) ds ty_arg id_arg
         (data_entry___update_options options_arg)
   | ["Comment", ty_arg, id_arg, comment_arg] =>
         update_data_store (false, report_error) ds ty_arg id_arg
         (data_entry___update_comment (SOME comment_arg))
   | ["Overrides", file] =>
         (mungeTools.user_overrides := mungeTools.read_overrides file;
          ds)
   | ["UseOccurenceSort"] =>
         let
            val _ = use_occ_sort_ref := true;
         in
            ds
         end
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
                  | _ => (report_error ("Error while parsing '"^filename^"' in '"^basedir^"'");ds))
   | _ => (report_error ("Error line: "^l); ds)
end;



fun cleanup_data_store (sds_thm, sds_term, sds_type) =
let
    fun cleanup_subdata_store sds =
    let
        val sdsL = Redblackmap.listItems sds
        val sdsL' = List.filter (data_entry_is_used o snd) sdsL;
    in
        sdsL'
    end;
    fun thmmapfun (id, de:data_entry) =
           (id, if (isSome (#content de)) then de else
              data_entry___update_content (SOME id) de)
in
   (List.map thmmapfun (cleanup_subdata_store sds_thm),
    cleanup_subdata_store sds_term,
    cleanup_subdata_store sds_type)
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





(******************************************************************************)
(* Output definitions                                                         *)
(******************************************************************************)
fun destruct_theory_thm s2 =
    let
       val ss2 = (Substring.full s2)
       val (x1,x2) = Substring.splitl (fn c => not (c = #".")) ss2
       val x2' = Substring.triml 1 x2
    in
       (Substring.string x1, Substring.string x2')
    end

fun command2string mungeTools.Term = "Term"
  | command2string mungeTools.Theorem = "Theorem"
  | command2string mungeTools.Type = "Type";

fun holmunge_format command id options content =
let
   val _ = if (isSome content) then () else Feedback.fail();
   val empty_posn = (0,0);
   val opts = mungeTools.parseOpts empty_posn ("alltt,"^options);
   val _ = if command = mungeTools.Theorem then
        let
           val (ty, tm) = destruct_theory_thm (valOf content);
           val _ = DB.fetch ty tm
                   handle HOL_ERR e =>
                       (report_error (#message e);Feedback.fail());
        in
           ()
        end else ();
   val replacement_args =
      {argpos = empty_posn, command=command, commpos = empty_posn,
       options = opts, argument=(valOf content)};
   val width_opt = mungeTools.optset_width opts;
   val width = if isSome width_opt then valOf width_opt else (!default_linewidth_ref);
   val fs = Portable.pp_to_string width mungeTools.replacement replacement_args
   val _ = if fs = "" then (report_error
           ("Error while formating "^(command2string command)^" '"^id^"'!");Feedback.fail()) else ();
in
   UTF8.translate (fn " " => "\\ "
                    | "\n" => "\\par "
                    | s => s) fs
end handle Interrupt => raise Interrupt
         | _ => "";


(*val os = Portable.std_out*)
fun output_holtex_def_internal (definetype,id,cs) os  =
let
   val _ = Portable.output (os, definetype);
   val _ = Portable.output (os, id);
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, cs);
   val _ = Portable.output (os, "}\n");
in
  ()
end handle Interrupt => raise Interrupt
         | _ => ()



fun output_holtex_def command definetype os (id,
  ({options  = options,
    content  = content_opt,
    printed  = printed,
    latex    = latex_opt,
    ...}:data_entry)) =
let
   val cs = if isSome latex_opt then
      (report_error ("Notice: using user defined latex for "^(command2string command)^" '"^id^"'!");valOf latex_opt) else
      holmunge_format command id options content_opt;
   val _ = if (cs = "") then Feedback.fail() else ();
   val _ = if printed then
              output_holtex_def_internal (definetype,id,cs) os
           else ();
in
  (id, cs)
end handle Interrupt => raise Interrupt
         | _ => (id, "")



fun process_type_defs os =
   List.map (output_holtex_def mungeTools.Type "\\defineHOLty{" os)


fun process_term_defs os =
   List.map (output_holtex_def mungeTools.Term "\\defineHOLtm{" os)

fun process_thm_defs os =
   List.map (output_holtex_def mungeTools.Theorem "\\defineHOLthm{" os)

fun output_all_defs os (thmL, termL, typeL) =
let
   val typeDefL = process_type_defs os typeL;
   val termDefL = process_term_defs os termL;
   val thmDefL = process_thm_defs os thmL;

   fun list2map l =
   let
      val emptyMap = Redblackmap.mkDict String.compare;
   in
      List.foldr (fn ((id,d),m) => Redblackmap.insert(m,id,d)) emptyMap l
   end
in
   (list2map thmDefL,list2map termDefL,list2map typeDefL)
end;


(******************************************************************************)
(* Output index                                                               *)
(******************************************************************************)


(* -------------------------------------------------------------------------- *)
(* comparisons for sorting the index                                          *)
(* -------------------------------------------------------------------------- *)

val string_compare = String.collate (fn (c1, c2) =>
    Char.compare (Char.toUpper c1, Char.toUpper c2))

fun entry_list_pos_compare ((id1, de1 as {pos_opt=NONE,...}:data_entry),
                            (id2, de2 as {pos_opt=NONE,...}:data_entry)) =
    string_compare (id1, id2)
  | entry_list_pos_compare ((id1, de1 as {pos_opt=SOME _,...}:data_entry),
                            (id2, de2 as {pos_opt=NONE,...}:data_entry)) =
    LESS
  | entry_list_pos_compare ((id1, de1 as {pos_opt=NONE,...}:data_entry),
                            (id2, de2 as {pos_opt=SOME _,...}:data_entry)) =
    GREATER
  | entry_list_pos_compare ((id1, de1 as {pos_opt=SOME pos1,...}:data_entry),
                            (id2, de2 as {pos_opt=SOME pos2,...}:data_entry)) =

    let
       val r = Int.compare(pos1,pos2)
    in if r = EQUAL then string_compare (id1,id2) else r end;


fun entry_list_label_compare ((id1, de1 as {label=NONE,...}:data_entry),
                              (id2, de2 as {label=NONE,...}:data_entry)) =
    entry_list_pos_compare ((id1,de1),(id2,de2))
  | entry_list_label_compare ((id1, de1 as {label=SOME _,...}:data_entry),
                              (id2, de2 as {label=NONE,...}:data_entry)) =
    GREATER
  | entry_list_label_compare ((id1, de1 as {label=NONE,...}:data_entry),
                              (id2, de2 as {label=SOME _,...}:data_entry)) =
    LESS
  | entry_list_label_compare ((id1, de1 as {label=SOME l1,...}:data_entry),
                              (id2, de2 as {label=SOME l2,...}:data_entry)) =
    let
       val r = string_compare (l1,l2)
    in if r = EQUAL then entry_list_pos_compare ((id1,de1),(id2,de2)) else r end


fun entry_list_thm_compare ((id1, de1 as {content=NONE,...}:data_entry),
                            (id2, de2 as {content=NONE,...}:data_entry)) =
    entry_list_label_compare ((id1,de1),(id2,de2))
  | entry_list_thm_compare ((id1, de1 as {content=SOME _,...}:data_entry),
                              (id2, de2 as {content=NONE,...}:data_entry)) =
    GREATER
  | entry_list_thm_compare ((id1, de1 as {content=NONE,...}:data_entry),
                            (id2, de2 as {content=SOME _,...}:data_entry)) =
    LESS
  | entry_list_thm_compare ((id1, de1 as {content=SOME c1,...}:data_entry),
                            (id2, de2 as {content=SOME c2,...}:data_entry)) =
    let
       val (theory1,thm1) = destruct_theory_thm c1;
       val (theory2,thm2) = destruct_theory_thm c2;
       val r = Lib.list_compare string_compare ([theory1,thm1], [theory2,thm2])
    in if r = EQUAL then entry_list_label_compare ((id1,de1),(id2,de2)) else r end


(* -------------------------------------------------------------------------- *)
(* other auxiliary defs                                                       *)
(* -------------------------------------------------------------------------- *)


exception nothing_to_do;

fun process_index_pages pages =
let
   val pL = Redblackset.listItems pages
   val pnL = List.map (fn s => (s, Int.fromString s)) pL
   fun get_int (_, NONE) = 0
     | get_int (_, (SOME n)) = n
   val pnL' = Listsort.sort (fn (a,b) => Int.compare (get_int a, get_int b)) pnL;
   val intL = List.map (fn p => (p,p)) pnL';

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



fun bool2latex true  = "true"
  | bool2latex false = "false"

fun boolopt2latex (SOME b) def = bool2latex b
  | boolopt2latex NONE     def = def;

fun output_holtex_index d (indextype,flagtype) os (id,
  ({label    = label_opt,
    full_index = full_index,
    pages    = pages,
    comment  = comment_opt, ...}:data_entry)) =
let
   val label = if isSome label_opt then valOf(label_opt) else "";
   val _ = Portable.output (os, indextype);
   val _ = Portable.output (os, id);
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, label);
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, process_index_pages pages);
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, boolopt2latex full_index flagtype);
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, bool2latex (not (Redblackset.isEmpty pages)));
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, if isSome comment_opt then valOf comment_opt else "");
   val _ = Portable.output (os, "}{");
   val _ = Portable.output (os, Redblackmap.find (d,id));
   val _ = Portable.output (os, "}\n");
in
  ()
end handle Interrupt => raise Interrupt
         | _ => ();



fun process_type_index d os typeL =
let
    val type_entryL  = List.filter (#in_index o snd) typeL;
    val _ = if null(type_entryL) then raise nothing_to_do else ();
    val type_entryL' = Listsort.sort entry_list_pos_compare type_entryL;

    val _ = Portable.output(os, "   \\begin{HOLTypeIndex}\n");
    val _ = List.map (output_holtex_index d ("      \\HOLTypeIndexEntry{","holIndexLongTypeFlag") os) type_entryL'
    val _ = Portable.output(os, "   \\end{HOLTypeIndex}\n");
in
   ()
end handle nothing_to_do => ();


fun process_term_index d os termL =
let
    val term_entryL = List.filter (#in_index o snd) termL;
    val _ = if null(term_entryL) then raise nothing_to_do else ();
    val term_entryL' = Listsort.sort entry_list_pos_compare term_entryL;

    val _ = Portable.output(os, "   \\begin{HOLTermIndex}\n");
    val _ = List.map (output_holtex_index d ("      \\HOLTermIndexEntry{","holIndexLongTermFlag") os) term_entryL'
    val _ = Portable.output(os, "   \\end{HOLTermIndex}\n");
in
   ()
end handle nothing_to_do => ();


fun process_thm_index d os thmL =
let
    val thm_entryL = List.filter (#in_index o snd) thmL;
    val _ = if null(thm_entryL) then raise nothing_to_do else ();
    val cmp = if (!use_occ_sort_ref) then entry_list_pos_compare else
         entry_list_thm_compare
    val thm_entryL' = Listsort.sort cmp thm_entryL;

    fun thmmapfun (id, de:data_entry) =
       let
          val label_opt = #label de;
          val add_label = if (isSome label_opt) then
             (" "^(valOf label_opt)) else "";
          val content_opt = (#content de);
          val content = if isSome content_opt then valOf content_opt else id;
          val (thy,thm) = destruct_theory_thm content;
          val thythm = if (!use_occ_sort_ref) then
              (thy^ "Theory."^thm) else thm
          val new_label = SOME ("\\HOLThmName{"^thythm ^ "}"^add_label);
       in
          (id, thy, data_entry___update_label new_label de)
       end;
    val thm_entryL'' = List.map thmmapfun thm_entryL';

    val _ = Portable.output(os, "\\begin{HOLThmIndex}\n");

    fun foldfun ((id, thy, de), old_thy) =
        let
            val _ = if ((!use_occ_sort_ref) orelse (thy = old_thy)) then () else
                (Portable.output(os, "   \\HOLThmIndexTheory{"^thy^"}\n"))
            val _ = output_holtex_index d ("      \\HOLThmIndexEntry{","holIndexLongThmFlag") os (id, de);
        in
            thy
        end;
    val _ = List.foldl foldfun "" thm_entryL'';
    val _ = Portable.output(os, "\\end{HOLThmIndex}\n");

in
   ()
end handle nothing_to_do => ();



fun output_all_index os (thmD,termD,typeD) (thmL, termL, typeL) =
let
   val _ = process_type_index typeD os typeL;
   val _ = process_term_index termD os termL;
   val _ = process_thm_index thmD os thmL;
   val _ = Portable.output (os, " \n");
in
   ()
end;






(******************************************************************************)
(* Put everything together                                                    *)
(******************************************************************************)

(*
   val basename = Globals.HOLDIR ^ "/src/TeX/holindex-demo";
   val file = (basename ^ ".hix")
   val (thmL, termL, typeL) = parse_hix file
*)

fun holindex basename =
let
    val _ = error_found := false;
    val ds = parse_hix (basename ^ ".hix")
    val os = Portable.open_out (basename ^ ".tde")
    val dd = output_all_defs os ds
    val _  = Portable.close_out os;
    val os = Portable.open_out (basename ^ ".tid")
    val _ = output_all_index os dd ds;
    val _  = Portable.close_out os;
    val _ = if (!error_found) then (Process.exit Process.failure) else ()
in
    ()
end;

end
