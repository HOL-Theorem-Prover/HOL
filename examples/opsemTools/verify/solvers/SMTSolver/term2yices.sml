(* ==================================================== *)
(* To translate a HOL term in the input syntax of Yices *)
(* ==================================================== *)


(* TODO: add a unary minus operator to parse expressions
         such as ~(exp)
 For the moment, only negative LITERALS are possible

Examples:
  x > -1 is correctly parsed
  -x > 1 raise an exception because ~x is not parsed 
*)


open HolKernel Parse boolLib
     bossLib  intLib  stringLib;

open intSyntax   (* various functions on ints (e.g. is_plus) *)
     pairSyntax;  (* various functions on pairs (e.g. strip_pair)    *)



(* ============================================= *)
(* To print a term built during symbolic execution
   in a .ys file that follows the of yices
*)
(* ============================================= *)

(* ============================================= *)
(* inputs:
   - the name of the program, 
   - a term (logical expression)
   output: a .ys file that follows the syntax of yices
*)
(* ============================================= *)



(* ============================================= *)
(* functions for parsing Boolean and integer terms *)
(* ----------------------------------------------- *)

(* ad hoc function to temporary handle Num in terms 
   built from \forall JML 
   TODO: handle domains of numeral values*)
fun is_num t = 
   if is_comb t
   then
     let val (opr,v) = dest_comb t
     in
       opr = ``Num``
     end
   else false;


(* functions to identify the types of terms *)
(* ---------------------------------------- *)

(* functions for parsing exponential *)
fun is_exponential tm =
 is_comb tm 
  andalso is_comb(rator tm) 
  andalso is_const(rator(rator tm)) 
  andalso (fst(dest_const(rator(rator tm))) = "int_exp");

fun dest_exponential tm = 
 if is_exponential tm
  then (rand(rator tm), rand tm)
  else raise ERR "dest_exponential" "not an integer exponential";


fun is_comparator(t) = 
    is_less(t) orelse is_leq(t) orelse is_great(t)
    orelse is_geq(t) orelse is_eq(t);

fun is_bool_term(t) =
    is_neg(t) orelse is_conj(t) orelse is_disj(t)
    orelse is_imp_only(t) orelse is_var(t) orelse 
    is_comparator(t);

fun is_int_term(t) =
    is_plus(t) orelse is_minus(t) orelse is_mult(t)
    orelse is_div(t) orelse is_exponential(t) 
    orelse is_var(t) orelse is_int_literal(t) orelse 
    is_num(t) orelse  numSyntax.is_numeral t; (* added for \forall in JML *)

(* function to indent printing *)
fun  indent 0  =  ""
| indent n =  "  " ^ indent (n-1);



(* function for parsing a variable *)
(* ------------------------------- *)
fun get_var(tm) =
     fst(dest_var tm) ;


(* function for parsing an integer expression *)
fun parse_int(tm,i) =
  if is_num(tm)
  then let val (opr,v) = dest_comb(tm)
    in 
     parse_int(v,i) 
    end            
  else
    if is_var(tm) 
    then " " ^ get_var(tm)  
    else 
      if is_int_literal(tm) orelse numSyntax.is_numeral(tm)
       then 
         let val l =  term_to_string(tm);
           in
             if is_negated(tm)
             then  " (-" ^ substring(l,1,size(l)-1) ^ ")"
             else  " " ^ l 
         end
   else
      if is_plus(tm)
      then
        let val c1 = parse_int(fst(dest_plus tm),i+1); 
          val c2 = parse_int(snd(dest_plus tm),i+1); 
          in
             "(+ " ^ c1 ^  c2 ^ ")"
          end
      else 
        if is_minus(tm)
        then
          let val c1 = parse_int(fst(dest_minus tm),i+1); 
            val c2 = parse_int(snd(dest_minus tm),i+1); 
            in
              "(- " ^  c1 ^  c2 ^ ")"
            end
        else 
          if is_mult(tm)
          then
            let val c1 = parse_int(fst(dest_mult tm),i+1); 
               val c2 = parse_int(snd(dest_mult tm),i+1); 
               in
                  "(* " ^  c1 ^  c2 ^  ")"
               end
          else 
            if is_div(tm)
            then
              let val c1 = parse_int(fst(dest_div tm),i+1); 
                val c2 = parse_int(snd(dest_div tm),i+1); 
                in
                   "(/ " ^  c1 ^  c2  ^ ")"
                end
            else (* exponential *)
              (* n**2 is translated as n*n *)
              if snd(dest_exponential tm)=``2``
              then 
                let val c =  parse_int(fst(dest_exponential tm),i+1);
                   in
                     "(* " ^  c ^  c ^  ")"
                   end
              else "";


(* function for parsing comparators *)
fun parse_comparator(tm,i) =
        if is_less(tm)
        then
            let val c1 = parse_int(fst(dest_less tm),i+1); 
              val c2 = parse_int(snd(dest_less tm),i+1); 
            in
                "(< " ^ c1 ^ c2 ^  ")"
            end
        else
            if is_leq(tm)
            then
                let val c1 = parse_int(fst(dest_leq tm),i+1); 
                  val c2 = parse_int(snd(dest_leq tm),i+1); 
                in
                     "(<= " ^ c1  ^ c2  ^ ")"
                end
            else
                if is_eq(tm)
                then 
                    let val c1 = parse_int(fst(dest_eq tm),i+1); 
                      val c2 = parse_int(snd(dest_eq tm),i+1); 
                    in
                        "(= "  ^ c1 ^ c2 ^  ")"
                    end
                    else
                    if is_great(tm)
                    then
                        let val c1 = parse_int(fst(dest_great tm),i+1); 
                          val c2 = parse_int(snd(dest_great tm),i+1); 
                        in
                           "(> "  ^  c1 ^  c2 ^ ")"
                        end
                    else (* greater or equal *)
                             let val c1 = parse_int(fst(dest_geq tm),i+1); 
                               val c2 = parse_int(snd(dest_geq tm),i+1); 
                             in
                                "(>= "   ^  c1 ^  c2 ^  ")"
                             end;



(* function for parsing a Boolean term (without quantifiers) *)
(* the boolean variable b is associated with constraint b==1 *)
fun parse_bool(tm,i) =
 if is_const tm
 then 
  if tm = ``T``
  then " true "
  else " false "
 else
  if is_var(tm) 
       then let val v = get_var(tm)
              in
                "(= " ^ v  ^ "1)"
              end
    else 
        if is_comparator(tm)
        then parse_comparator(tm,i+1)
        else
            if is_neg(tm)
            then 
                let val c1 = parse_bool(dest_neg tm,i+1); 
                in 
                  "(not "   ^ c1  ^")" 
                end
            else 
                (* binary operators *)
    if is_disj(tm)
    then
        let val c1 = parse_bool(fst(dest_disj tm),i+1); 
          val c2 = parse_bool(snd(dest_disj tm),i+1); 
        in
            "(or " ^  c1 ^  c2  ^ ")\n"
        end
    else 
        if is_imp_only(tm)
        then
             let val c1 = parse_bool(fst(dest_imp_only tm),i+1); 
              val c2 = parse_bool(snd(dest_imp_only tm),i+1); 
            in
                "(=>" ^  c1 ^  c2  ^ ")\n"
            end
                (* conjunction *)
        else 
          if (fst(dest_conj tm)=``T``)
          then parse_bool(snd(dest_conj tm),i+1)
          else
            let val c1 = parse_bool(fst(dest_conj tm),i+1); 
              val c2 = parse_bool(snd(dest_conj tm),i+1); 
            in
                 "(and " ^  c1 ^  c2  ^ ")\n"
            end;


(* to print the variables *)
(* ---------------------- *)

fun var_list tm =
  let val l = all_vars tm 
    val ll = 
       map (fn v => "(define " ^ term_to_string(v) ^"::int)\n")
       l
  in
    (concat ll) ^ "\n\n"
  end;



(* to add check command *)
(* -------------------- *)
fun check_term() = 
   "\n(check)";


(* to print the term  *)
(* terms can be empty *)
(* ------------------ *)

fun get_term(t) = 
     "(assert \n" ^ parse_bool(t,1) ^ "\n)\n";



(* ------------------------------------------ *)
(* main function to print a term as xml tree          *)
(* ------------------------------------------ *)
fun print_opsemTerm(out,name,tm) =
   (out(var_list(tm));
    out(get_term(tm));
    out(check_term())
   )
   handle HOL_ERR s =>
      print("Error in term2yices " ^ term_to_string(tm) ^"\n");

