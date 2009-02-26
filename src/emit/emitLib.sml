structure emitLib :> emitLib =
struct
 open HolKernel boolLib EmitML
 open num_emitTheory list_emitTheory set_emitTheory option_emitTheory
      sum_emitTheory
 
(* ------------------------------------------------------------------------- *)
(* pp_datatype_theorem : ppstream -> thm -> unit                             *)
(*   Pretty-printer for datatype theorems                                    *)
(* ------------------------------------------------------------------------- *)

fun pp_datatype_theorem ostrm thm =
let val S = PP.add_string ostrm
    val BR = PP.add_break ostrm
    val BB = PP.begin_block ostrm
    fun NL() = PP.add_newline ostrm
    fun EB() = PP.end_block ostrm
    val PT = pp_term ostrm
    val TP = type_pp.pp_type (Parse.type_grammar()) ostrm

    val type_trace = current_trace "types"
    val _ = set_trace "types" 0

    fun strip_type t =
      if is_vartype t then
       [t]
      else
        case dest_type t of
          ("fun", [a, b]) => a :: strip_type b

        | _ => [t]

    fun pp_clause t =
        let val l = strip_type (type_of t)
            val ll = length l
        in
          (PT t;
             if ll < 2 then
               ()
             else
               (S " of ";
                BB PP.CONSISTENT 0;
                  app (fn x => (TP x; S " =>"; BR(1,0))) (List.take(l, ll - 2));
                  TP (List.nth(l, ll - 2));
                EB()))
        end
    fun enumerated_type n =
          let val l = butlast (strip_type (type_of n))
              val typ = fst (dest_var n)
          in
            all (fn x => fst (dest_type x) = typ) l
          end
    fun pp_constructor_spec (n, l) =
          (PT n;
           BB (if enumerated_type n then PP.INCONSISTENT else PP.CONSISTENT) 1;
             S " = ";
             app (fn x => (pp_clause x; BR(1,0); S "| "))
               (List.take(l, length l - 1));
             pp_clause (last l);
           EB())
    fun pp_record_spec l =
        let val ll = tl l
            fun pp_record x = (PT x; S " : "; TP (type_of x))
        in
          (PT (hd l); S " = ";
           BB PP.CONSISTENT 1;
             S "<|"; BR(1,1);
             app (fn x => (pp_record x; S ";"; BR(1,1)))
               (List.take(ll, length ll - 1));
             pp_record (last ll); BR(1,0);
             S "|>";
           EB())
        end
    fun pp_binding (n, l) =
          if fst (dest_var n) = "record" then
            pp_record_spec l
          else
            pp_constructor_spec (n, l)
    fun pp_datatype l =
          (BB PP.CONSISTENT 0;
             app (fn x => (pp_binding x; S " ;"; NL(); NL()))
               (List.take(l, length l - 1));
             pp_binding (last l);
           EB())

    val t = map strip_comb (strip_conj (snd (dest_comb (concl thm))))
in
  pp_datatype t; PP.flush_ppstream ostrm; set_trace "types" type_trace
end;

val datatype_thm_to_string =
  PP.pp_to_string (!Globals.linewidth) pp_datatype_theorem;

end
