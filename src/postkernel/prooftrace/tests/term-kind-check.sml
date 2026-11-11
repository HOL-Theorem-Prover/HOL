(* Run with the minimal HOL heap after replaying the separate or merged
   term-kind export, then call term_kind_check with its theorem database. *)
fun term_kind_check db = let
  val b = Type.bool
  val f = Term.mk_var("f",Type.--> (b,b))
  val x = Term.mk_var("x",b)
  val nested = Term.mk_abs(f,Term.mk_abs(f,x))
  val truth = Term.mk_thy_const {Thy="bool",Name="T",Ty=b}
  val closed = Term.mk_abs(f,truth)
  fun check (name,tm) = let
    val ty = Term.type_of tm
    val eq = Term.mk_thy_const
      {Thy="min",Name="=",Ty=Type.--> (ty,Type.--> (ty,b))}
    val expected = Term.mk_comb(Term.mk_comb(eq,tm),tm)
  in case PFTReplay.lookup db ("pft_term_kinds$" ^ name) of
       SOME th =>
         if null (Thm.hyp th) andalso Term.aconv (Thm.concl th) expected then
           print ("TERM_KIND_HOL_EXACT " ^ name ^ "\n")
         else raise Fail ("term-kind sequent mismatch: " ^ name)
     | NONE => raise Fail ("missing term-kind export: " ^ name)
  end
  val () = List.app check [("RENAME",nested),("SPEC",closed)]
  val _ = Term.mk_thy_const {Thy="pft_term_kinds",Name="unused",Ty=b}
in print "TERM_KIND_HOL_ALL_EXACT_PASS\n" end;
