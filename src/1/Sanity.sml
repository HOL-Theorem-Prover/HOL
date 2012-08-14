(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(*   Sanity checks for theorems stored in DB. This is intended to check for  *)
(*   simple errors like types in quantified variable names etc.              *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

structure Sanity :> Sanity =
struct

open HolKernel DB Abbrev Parse boolSyntax;
type theory = Hol_pp.theory;


fun report_sanity_problem___plain thy thm_name warning =
  HOL_WARNING ("Sanity Check "^thy^"Theory") thm_name
     warning;

val report_last_thm = ref "";
fun report_sanity_problem___verbose thy thm_name warning =
  let
     open PPBackEnd
     val thm_s = thy^"Theory."^thm_name;
     val _ = if not (thm_s = (!report_last_thm)) then
        let
          val _ = report_last_thm := thm_s;
          val _ = print "\n\n";
          val _ = print_with_style [Bold] thm_s;
          val _ = print "\n";
          val size = UTF8.size thm_s
          fun line 0 l = l
            | line n l = line (n-1) ("-"^l);
          val _ = print (line size "\n");
        in
          ()
        end else ()

   val _ = print "  - ";
   val _ = print warning;
   val _ = print "\n";
  in
     ()
  end;

fun init_report_sanity_problem () =
   (report_last_thm := "");

val report_verbose = ref true;
val _ = Feedback.register_btrace ("Sanity Check Verbose", report_verbose);


fun report_sanity_problem thy thm_name warning =
  (if (!report_verbose) then
      report_sanity_problem___verbose thy thm_name warning
   else
      report_sanity_problem___plain thy thm_name warning);


fun map_fail c f [] = c
  | map_fail c f (x::xs) =
    let
       val c' = (f x) handle Interrupt => raise Interrupt
                           | _ => true;
    in
       map_fail (c orelse c') f xs
    end


(******************************************************************************)
(* Check for assumptions                                                      *)
(******************************************************************************)

fun check_assumptions ((thy, name), (thm, cl)) =
let
  val hL = hyp thm
in
  if null hL then false else
  (report_sanity_problem thy name "Theorem has assumptions";true)
end;


(******************************************************************************)
(* Check for tags                                                             *)
(******************************************************************************)

val accepted_axioms = ref ([]:string list);
val accepted_oracles = ref (["DISK_THM"]:string list);

fun check_tags ((thy, name), (thm, cl)) =
let
  val (oL, aL) = Tag.dest_tag (tag thm);
  val oL' = filter (fn s => not(
      (mem s (!accepted_oracles)))) oL
  val aL' = filter (fn s => not(
      (mem s (!accepted_axioms)))) aL
  val orac_s = if (null oL') then "" else
       ("Oracles used: "^(concat (commafy oL')));
  val axiom_s = if (null aL') then "" else
       ("Axioms used: "^(concat (commafy aL')));
  val s = if (null oL') then axiom_s else
          if (null aL') then orac_s else
          (orac_s ^ "; "^axiom_s)
in
  if (null oL' andalso null aL') then false else
  ((report_sanity_problem thy name s);true)
end;


(******************************************************************************)
(* Check for theorem name clashes                                             *)
(******************************************************************************)

val check_thm_name_flag = ref true;
val _ = Feedback.register_btrace ("Sanity Check Thm-Name Clash", check_thm_name_flag);

fun check_thm_name ((thy, name), (thm, cl)) =
if (!check_thm_name_flag) then
let
  val dL = DB.listDB ();
  val dL' = filter (fn ((thy',name'), _) =>
      ((name = name') andalso (not (thy = thy')))) dL
  val dL'' = map (fn ((s,_), _) => "'"^s^"'") dL';
in
  if (null dL') then false else
  (report_sanity_problem thy name ("Name-clash with theorems in theories "^
     (concat (commafy dL''))); true)
end else false;


(******************************************************************************)
(* Check for problematic variable names                                       *)
(******************************************************************************)

fun check_var_names___no_ident ((thy, name), (thm, cl)) =
let
  val vL = all_varsl ((concl thm)::hyp thm)
  val vL' = filter (fn v => not (Lexis.ok_identifier (fst (dest_var v)))) vL
  val vnL = map  (fn v => ("'"^(fst (dest_var v))^"'")) vL'
in
  if (null vnL) then false else
  ((report_sanity_problem thy name ("Dodgy variables names: "^
     (concat (commafy vnL))));true)
end;


val check_var_names___const_flag = ref true;
val _ = Feedback.register_btrace ("Sanity Check Var-Const Clash", check_var_names___const_flag);

fun check_var_names___const ((thy, name), (thm, cl)) =
if (!check_var_names___const_flag) then
let
  val vL = all_varsl ((concl thm)::hyp thm)
  val vL' = filter (fn v => Parse.is_constname (fst (dest_var v))) vL
  val vnL = map  (fn v => ("'"^(fst (dest_var v))^"'")) vL'
in
  if (null vnL) then false else
  ((report_sanity_problem thy name ("Variables names clash with constants: "^
     (concat (commafy vnL))));true)
end else false;



(******************************************************************************)
(* Check for free top-level variables                                         *)
(******************************************************************************)

val check_free_vars_ref = ref 1;
val _ = Feedback.register_trace ("Sanity Check Free Vars", check_free_vars_ref, 1);

fun varlist_to_string vL =
  concat (commafy (map (fn v => "'"^(ppstring pp_term v)^"'") vL))

fun check_free_vars ((thy, name), (thm, cl)) =
let
   val do_check = if (!check_free_vars_ref = 0) then true
                  else (if (!check_free_vars_ref = 1) then
                     exists is_forall (strip_conj (concl thm)) else false)
in
if (do_check) then
let
  val fv = free_vars (concl thm)
in
  if null fv then false else
  (report_sanity_problem thy name ("Free top_level vars " ^
    (varlist_to_string fv) ^ "!");true)
end else false end

(******************************************************************************)
(* Check for redundant quantors                                               *)
(******************************************************************************)

fun is_quant t =
  is_forall t orelse
  is_exists t orelse
  is_exists1 t

fun check_redundant_quantors ((thy, name), (thm, cl)) =
let
   val tL = find_terms is_quant (concl thm);
   fun check_term t =
      let
        val (v, b) = dest_abs (rand t)
      in
        if (free_in v b) then false else
          (report_sanity_problem thy name ("Redundant quantor: '" ^
          (ppstring pp_term v) ^ "'!");true)
      end;
in
   (map_fail false check_term tL)
end;



(******************************************************************************)
(* A list of all checks                                                       *)
(******************************************************************************)

val sanity_checks = [
   check_tags,
   check_assumptions,
   check_thm_name,
   check_var_names___no_ident,
   check_var_names___const,
   check_free_vars,
   check_redundant_quantors]:(DB.data -> bool) list

fun sanity_check_data (data:DB.data) =
   (map_fail false (fn ff => ff data) sanity_checks)

fun sanity_check_theory thy =
  (init_report_sanity_problem ();(map_fail false sanity_check_data (DB.thy thy)))

fun sanity_check () = sanity_check_theory "-";

fun sanity_check_all () =
  (init_report_sanity_problem ();
   (map_fail false sanity_check_data (DB.listDB ())))

fun sanity_check_named_thm (name, thm) =
   sanity_check_data ((Theory.current_theory(), name), (thm, DB.Thm))

fun sanity_check_thm thm = sanity_check_named_thm ("-", thm);

(******************************************************************************)
(* Apply the checks when saving theorems                                      *)
(******************************************************************************)

val strict_sanity = ref true;
val _ = Feedback.register_btrace ("Sanity Check Strict", strict_sanity);

exception sanity_exn;
fun sanity_check_exn_thm (name, thm) =
   if (not (sanity_check_named_thm (name, thm)) orelse not (!strict_sanity)) then
      thm
   else
      (print "\n\n";raise sanity_exn);

fun sanity_prove (t, tac) = sanity_check_exn_thm ("-", Tactical.prove (t, tac));
fun save_thm (name, thm) = Theory.save_thm (name, sanity_check_exn_thm (name, thm));
fun store_thm (name, t, tac) =
   sanity_check_exn_thm (name, Tactical.store_thm (name, t, tac));

end
