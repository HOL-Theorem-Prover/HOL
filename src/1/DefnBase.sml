structure DefnBase :> DefnBase =
struct

open HolKernel boolSyntax Drule

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

fun all_terms d =
  case d of
      ABBREV{eqn,...} => [concl eqn]
    | PRIMREC {eqs,ind,...} => [concl eqs, concl ind]
    | NONREC {eqs,ind,SV,...} => concl eqs::concl ind::SV
    | STDREC {eqs,ind,R,SV,...} => R :: concl ind :: map concl eqs @ SV
    | MUTREC {eqs,ind,R,SV,union,...} =>
        R :: concl ind :: map concl eqs @ SV @ all_terms union
    | NESTREC {eqs,ind,R,SV,aux,...} =>
        R :: concl ind :: map concl eqs @ SV @ all_terms aux
    | TAILREC {eqs,ind,R,SV,...} => R :: concl ind :: map concl eqs @ SV

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
fun pp_defn d =
  let open smpp
      val pp_term = lift Parse.pp_term
      val pp_thm  = lift Parse.pp_thm
      fun pp_rec (eqs,ind,tcs) =
        block CONSISTENT 0 (
          add_string "Equation(s) :" >>
          add_break(1,0) >>
          pr_list pp_thm add_newline eqs >>
          add_newline >> add_newline >>
          add_string "Induction :" >>
          add_break(1,0) >>
          pp_thm ind >>
          (if null tcs then nothing
           else
             (add_newline >> add_newline >>
              add_string "Termination conditions :" >>
              add_break(1,2) >>
              block CONSISTENT 0 (
                 pr_list (fn (n,tm) =>
                             block CONSISTENT 3 (
                               add_string (Lib.int_to_string n^". ") >>
                               pp_term tm
                             )
                         )
                         add_newline
                         (Lib.enumerate 0 tcs)
               ))
          )
        )
   fun pp (ABBREV {eqn, ...}) =
          block CONSISTENT 0 (
            add_string "Equation :" >>
            add_break(1,0) >>
            pp_thm eqn
          )
     | pp (PRIMREC{eqs, ind, bind}) =
          block CONSISTENT 0 (
            add_string "Equation(s) :" >>
            add_break(1,0) >>
            pp_thm eqs
          )
     | pp (NONREC {eqs, ind, SV, stem}) =
          block CONSISTENT 0 (
             add_string "Equation(s) :" >>
             add_break(1,0) >>
             pp_thm eqs >>
             add_newline >> add_newline >>
             add_string "Case analysis:" >>
             add_break(1,0) >> pp_thm ind
          )
     | pp (STDREC {eqs, ind, R, SV, stem})        = pp_rec(eqs,ind, hyps eqs)
     | pp (NESTREC{eqs, ind, R, SV, aux, stem})   = pp_rec(eqs,ind, hyps eqs)
     | pp (MUTREC {eqs, ind, R, SV, union, stem}) = pp_rec(eqs,ind, hyps eqs)
     | pp (TAILREC{eqs, ind, R, SV, stem})        = pp_rec(eqs,ind, hyps eqs)
   val m =
     block CONSISTENT 0 (
       add_string "HOL function definition " >>
       add_string (String.concat ["(",kind d,")"]) >>
       add_newline >> add_newline >>
       pp d
     )
  in
    Parse.mlower m
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
    ThmSetData.new_exporter {
      settype = "defncong",
      efns = {
        add = fn {thy,named_thms} => app (add_cong o #2) named_thms,
        remove = fn _ => ()
      }
    }

(* ----------------------------------------------------------------------
    storage of definitions
   ---------------------------------------------------------------------- *)

type defnstore = (string * KernelSig.kernelname, thm) Binarymap.dict
type indnstore = (KernelSig.kernelname, thm * term list) Binarymap.dict

val the_defnstore : defnstore ref =
    ref (Binarymap.mkDict(pair_compare(String.compare, KernelSig.name_compare)))
val the_indnstore : indnstore ref =
    ref (Binarymap.mkDict KernelSig.name_compare)

fun list_insert m k v =
    case Binarymap.peek(m,k) of
        NONE => Binarymap.insert(m,k,[v])
      | SOME vs => Binarymap.insert(m,k,v::vs)

fun to_kid {Thy,Name,Ty} = {Thy = Thy, Name = Name}

fun register_defn tag thm =
    let
      val ths = thm |> CONJUNCTS
      val cs =
          map
            (fn th =>
                (th |> concl |> strip_forall |> #2 |> lhs |> strip_comb |> #1
                    |> dest_thy_const |> to_kid,
                 th))
            ths handle HOL_ERR _ => raise mk_HOL_ERR "DefnBase" "register_defn"
                                          "Malformed definition"
      val m = List.foldr (fn ((t,th),A) => list_insert A t th)
                         (Binarymap.mkDict KernelSig.name_compare)
                         cs
    in
      the_defnstore :=
      Binarymap.foldl (fn (k,cs,A) => Binarymap.insert(A,(tag,k),LIST_CONJ cs))
                      (!the_defnstore)
                      m
    end

fun lookup_defn c tag =
    let
      val {Name,Thy,...} =
          dest_thy_const c
          handle HOL_ERR _ => raise mk_HOL_ERR "DefnBase"
                                    "lookup_defn" "Not a constant"
    in
      Binarymap.peek (!the_defnstore, (tag, {Name = Name, Thy = Thy}))
    end

fun isprefix l1 l2 =
    case (l1,l2) of
        ([] , _) => true
      | (h1::t1, []) => false
      | (h1::t1, h2::t2) => h1 = h2 andalso isprefix t1 t2

fun register_indn (ind, cs) =
    let
      val _ = not (null cs) orelse
              raise mk_HOL_ERR "DefnBase" "register_indn"
                    "Must have non-empty list of constants"
      val (Ps, body) = ind |> concl |> strip_forall
      fun check (P, c) =
          let
            val (Pdoms, _) = strip_fun (type_of P)
            val (cdoms, _) = strip_fun (type_of c)
          in
            isprefix Pdoms cdoms orelse
            raise mk_HOL_ERR "DefnBase" "register_indn"
                    ("Induction variable type of ivar "^ #1 (dest_var P) ^
                     " doesn't match that of constant " ^ #1 (dest_const c))
          end
      val _ = ListPair.all check (Ps, cs)
    in
      the_indnstore :=
      List.foldl (fn (c, A) =>
                     Binarymap.insert(A, c |> dest_thy_const |> to_kid,
                                      (ind,cs)))
                 (!the_indnstore)
                 cs
    end

fun lookup_indn c =
    let
      val {Name,Thy,...} =
          dest_thy_const c
          handle HOL_ERR _ => raise mk_HOL_ERR "DefnBase"
                                    "lookup_indn" "Not a constant"
    in
      Binarymap.peek (!the_indnstore, {Name = Name, Thy = Thy})
    end

end
