(* Call an external solver as an oracle *)

open HolKernel Parse boolLib term2xml execSymb;

fun extSolv name tm =
 let val (vars,bdy) = strip_exists tm
 in
 (print("Calling extSolv \"" ^ name ^ "\" on:\n");
  print_term bdy; print "\n";
  printXML_to_file(name,bdy);
  execPath name;
  let val (sol,time) = 
       getSolutions(ilogPath ^ "results/" ^ name ^ ".res");
      val th =
       if null sol
        then EQF_INTRO(mk_oracle_thm name ([], mk_neg tm))
        else EQT_INTRO(mk_oracle_thm name ([],tm))
  in
   if (null sol)
   then  
     (print "======================\n";
      print (term_to_string bdy ^ "\n");
      print "has no solutions:\n";
      print_thm th;
      print "\n======================\n";
      th
     )
   else 
     (print "======================\n";
      print(term_to_string tm ^ "\n");
      print("has " ^ Int.toString(length sol) ^ " solution" ^ 
            (if length sol > 1 then "s\n" else "\n"));
      print_thm th;
      print "\n======================\n";
      REFL tm
     )
  end)
 end;
