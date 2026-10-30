fun identity_require message condition =
  if condition then () else raise Fail message;
fun identity_split name =
  case String.fields (fn c => c = #"$") name of
    [thy,nm] => (thy,nm)
  | _ => raise Fail ("unqualified identity: " ^ name);
fun identity_constant name =
  let val (thy,nm) = identity_split name
  in Term.prim_mk_const {Thy=thy,Name=nm} end;
fun identity_const_exists name =
  let val (thy,nm) = identity_split name
  in List.exists (fn tm => #Thy (Term.dest_thy_const tm) = thy)
       (Term.decls nm)
  end;
val identity_cases = ["identity_restore", "identity_collision",
  "identity_closure", "identity_reexport", "identity_reexport_child",
  "identity_trace_loader"];
fun identity_check lookup merged =
  let
    fun theorem thy name = case lookup thy name of
        SOME th => th
      | NONE => raise Fail ("missing export " ^ thy ^ "$" ^ name)
    fun exact thy name tm =
      let val th = theorem thy name
      in identity_require ("wrong sequent for " ^ thy ^ "$" ^ name)
           (null (Thm.hyp th) andalso
            Term.aconv (Thm.concl th) (Thm.concl (Thm.REFL tm)));
         print ("IDENTITY_EXACT " ^ thy ^ "$" ^ name ^ "\n")
      end
    fun inventory thy =
      let val ins = TextIO.openIn (thy ^ ".expected")
          val lines = String.tokens (fn c => c = #"\n") (TextIO.inputAll ins)
          val () = TextIO.closeIn ins
          fun one line =
            case String.tokens (fn c => c = #" ") line of
              ["final_const",name] => exact thy "RESULT"
                (identity_constant name)
            | ["decl_const",name] => identity_require line
                (merged orelse identity_const_exists name)
            | ["private_const",name] => identity_require line
                (identity_const_exists name)
            | ["public_const",name] => identity_require line
                (identity_const_exists name)
            | _ => raise Fail ("unknown identity expectation: " ^ line)
      in List.app one lines end
    val () = List.app inventory identity_cases
  in print "IDENTITY_EXACT_SEQUENTS_AND_INVENTORY_PASS\n" end;
