structure DefnBase :> DefnBase =
struct

open HolKernel

val ERR = mk_HOL_ERR "DefnBase";

(*---------------------------------------------------------------------------
    The type of definitions. This is an attempt to gather all the
    information about a definition in one place.
 ---------------------------------------------------------------------------*)

datatype defn
   = ABBREV  of {eqn:thm, bind:string}
   | PRIMREC of {eqs:thm, ind:thm, bind:string}
   | NONREC  of {eqs:thm, ind:thm, SV:term list, stem:string}
   | STDREC  of {eqs:thm list, ind:thm, R:term,SV:term list,stem:string}
   | MUTREC  of {eqs:thm list, ind:thm, R:term, SV:term list,
                 stem:string,union:defn}
   | NESTREC of {eqs:thm list, ind:thm, R:term, SV:term list,
                 stem:string, aux:defn}
   | TAILREC of {eqs:thm list, ind:thm, R:term, SV:term list, stem:string}

local open Portable
      fun kind (ABBREV _)  = "abbreviation"
        | kind (NONREC  _) = "non-recursive"
        | kind (STDREC  _) = "recursive"
        | kind (PRIMREC _) = "primitive recursion"
        | kind (MUTREC  _) = "mutual recursion"
        | kind (NESTREC _) = "nested recursion"
        | kind (TAILREC _) = "nonterminating tail recursion"
      fun hyps thl = HOLset.listItems
                       (foldl (fn (th,s) => HOLset.union(hypset th, s))
                              empty_tmset thl)
in
fun pp_defn ppstrm =
 let val {add_string,add_break,
          begin_block,end_block,add_newline,...} = with_ppstream ppstrm
     val pp_term = Parse.pp_term ppstrm
     val pp_thm  = Parse.pp_thm ppstrm
     fun pp_rec (eqs,ind,tcs) =
        (begin_block CONSISTENT 0;
         add_string "Equation(s) :";
         add_break(1,0);
         pr_list pp_thm (fn () => ()) add_newline eqs;
         add_newline (); add_newline ();
         add_string "Induction :";
         add_break(1,0);
         pp_thm ind;
         if null tcs then ()
         else (add_newline (); add_newline ();
               add_string "Termination conditions :";
               add_break(1,2);
               begin_block CONSISTENT 0;
                 pr_list (fn (n,tm) =>
                           (begin_block CONSISTENT 3;
                            add_string (Lib.int_to_string n^". ");
                            pp_term tm; end_block()))
                         (fn () => ())
                         add_newline
                      (Lib.enumerate 0 tcs);
               end_block());
         end_block())
   fun pp (ABBREV {eqn, ...}) =
          (begin_block CONSISTENT 0;
           add_string "Equation :";
           add_break(1,0);
           pp_thm eqn;
           end_block())
     | pp (PRIMREC{eqs, ind, bind}) =
          (begin_block CONSISTENT 0;
           add_string "Equation(s) :";
           add_break(1,0);
           pp_thm eqs; end_block())
     | pp (NONREC {eqs, ind, SV, stem}) =
          (begin_block CONSISTENT 0;
           add_string "Equation(s) :";
           add_break(1,0);
           pp_thm eqs;
           add_newline (); add_newline();
           add_string "Case analysis:";
           add_break(1,0); pp_thm ind;
           end_block())
     | pp (STDREC {eqs, ind, R, SV, stem})        = pp_rec(eqs,ind, hyps eqs)
     | pp (NESTREC{eqs, ind, R, SV, aux, stem})   = pp_rec(eqs,ind, hyps eqs)
     | pp (MUTREC {eqs, ind, R, SV, union, stem}) = pp_rec(eqs,ind, hyps eqs)
     | pp (TAILREC{eqs, ind, R, SV, stem})        = pp_rec(eqs,ind, hyps eqs)
 in
   fn d =>
       (begin_block CONSISTENT 0;
        add_string "HOL function definition ";
        add_string (String.concat ["(",kind d,")"]);
        add_newline (); add_newline ();
        pp d;
        end_block())
 end
end;


(*---------------------------------------------------------------------------
    Congruence rules for termination condition extraction. Before
    t.c. extraction is performed, the theorems in "non_datatype_congs"
    are added to the congruence rules arising from datatype definitions,
    which are held in the TypeBase.
 ---------------------------------------------------------------------------*)


local open boolTheory
      val non_datatype_congs =
        ref [LET_CONG, COND_CONG, IMP_CONG, literal_case_CONG]
in
  fun read_congs() = !non_datatype_congs
  fun write_congs L = (non_datatype_congs := L)
end;

fun add_cong thm = write_congs (thm :: read_congs());

fun drop_cong c =
 let open boolSyntax
     val P = same_const c
     val (cong,rst) =
         pluck (fn th => P (fst(strip_comb(lhs(snd
                             (strip_imp(snd(strip_forall(concl th)))))))))
               (read_congs())
     val _ = write_congs rst
 in
   cong
 end
 handle e => raise wrap_exn "DefnBase.drop_cong"
    (case total dest_thy_const c
      of NONE => "expected a constant"
       | SOME{Thy,Name,...} =>
           ("congruence rule for "
            ^Lib.quote(Thy^"$"^Name)
            ^" was not found")) e;

val {export = export_cong,...} =
    ThmSetData.new_exporter "defncong" (K (app add_cong))

end
