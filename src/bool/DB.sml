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
type keydata = (string * string) * data


(*---------------------------------------------------------------------------
   Map keys to canonical case
 ---------------------------------------------------------------------------*)

fun toLower s =
 let open Char CharVector in tabulate(size s, fn i => toLower(sub(s,i))) end

(*---------------------------------------------------------------------------
     Persistence: bindl is used to populate the database when a theory
     is loaded.
 ---------------------------------------------------------------------------*)

local val DBref = ref [] : keydata list ref
      fun lemmas() = !DBref
      fun add ((p as (s1,s2)),x) = cons ((toLower s1, toLower s2),(p,x))
      fun addb thy (name,th,cl) = add ((thy,name),(th,cl))
      fun classify thy cl (s,th) = ((thy,s),(th,cl))
in
fun bindl thy blist = DBref := Lib.rev_itlist (addb thy) blist (lemmas())

(*---------------------------------------------------------------------------
    To the database representing all ancestor theories, add the
    entries in the current theory segment.
 ---------------------------------------------------------------------------*)

fun CT() =
  let val thyname = Theory.current_theory()
  in
    itlist (add o classify thyname Def) (Theory.current_definitions ())
     (itlist (add o classify thyname Axm) (Theory.current_axioms ())
      (itlist (add o classify thyname Thm) (Theory.current_theorems ())
              (lemmas())))
  end
end;


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
   map snd (filter (equal(toLower(norm_thyname s)) o fst o fst) (CT()));

fun find s = map snd (filter (occurs(toLower s) o snd o fst) (CT()));


(*---------------------------------------------------------------------------
      Look up something by matching. Parameterized by the matcher.
 ---------------------------------------------------------------------------*)

fun matchp P thylist =
 let val matchfn =
       case List.map norm_thyname thylist
        of []   => (fn (_,(th,_)) => P th)
         | strl => (fn ((s,_),(th,_)) => Lib.mem s strl andalso P th)
 in
   map snd (filter (matchfn o snd) (CT()))
 end


fun matcher f thyl pat =
  matchp (fn th => can (find_term (can (f pat))) (concl th)) thyl;

val match = matcher (ho_match_term [] empty_tmset);
val apropos = match [];


fun listDB () = map snd (CT());

(*---------------------------------------------------------------------------
      Some other lookup functions
 ---------------------------------------------------------------------------*)

fun thm_class thy name =
  case filter (equal (norm_thyname thy,name) o fst o snd) (CT())
   of [(_,p)] => snd p
    | [] => raise ERR "thm_class" "not found"
    | other => raise ERR "thm_class" "multiple things with the same name";


fun fetch s1 s2 = fst (thm_class s1 s2);

fun thm_of ((_,n),(th,_)) = (n,th);
fun is x (_,(_,cl)) = (cl=x)

val thms        = rev o List.map thm_of o thy
val theorems    = rev o List.map thm_of o Lib.filter (is Thm) o thy
val definitions = rev o List.map thm_of o Lib.filter (is Def) o thy
val axioms      = rev o List.map thm_of o Lib.filter (is Axm) o thy

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
    Refugee from Parse structure
 ---------------------------------------------------------------------------*)

fun export_theory_as_docfiles dirname =
    Parse.export_theorems_as_docfiles dirname (theorems "-");

end
