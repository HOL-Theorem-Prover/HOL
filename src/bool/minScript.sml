(* ===================================================================== *)
(* FILE          : mk_min.sml                                            *)
(* DESCRIPTION   : The Mother of All Theories.                           *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : September 11, 1991                                    *)
(*                 June 18, 1998                                         *)
(* ===================================================================== *)


structure minScript =
struct

open Theory Parse;

val _ = new_theory "min";

val _ = new_type{Name="bool", Arity=0};
val _ = new_type{Name="ind",  Arity=0};

val _ = new_infix_type{Name="fun",  Arity=2, ParseName = SOME "->",
                       Assoc = HOLgrammars.RIGHT, Prec = 50};

val _ = new_constant{Name = "=",   Ty=Type `: 'a -> 'a -> bool`};
val _ = new_constant{Name = "==>", Ty = Type`:bool -> bool -> bool`};
(* using the standard rules for infixes for ==> and = seems to result in bad
   pretty-printing of goals.  I think the following customised printing
   spec works better.  The crucial difference is that the blocking style
   is CONSISTENT rather than INCONSISTENT. *)
val _ = add_rule {term_name = "==>",
                  block_style = (AroundSamePrec, (PP.CONSISTENT, 0)),
                  fixity = Infix(RIGHT, 200),
                  pp_elements = [HardSpace 1, TOK "==>", BreakSpace(1,0)],
                  paren_style = OnlyIfNecessary};
val _ = add_rule {term_name = "=",
                  block_style = (AroundSamePrec, (PP.CONSISTENT, 0)),
                  fixity = Infix(NONASSOC, 100),
                  pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,0)],
                  paren_style = OnlyIfNecessary};

val _ = new_binder{Name ="@",   Ty=Type `: ('a -> bool) -> 'a`};

val _ = adjoin_to_theory
   {sig_ps = NONE,
    struct_ps = SOME(fn ppstrm =>
     (PP.begin_block ppstrm PP.CONSISTENT 2;
      PP.add_string ppstrm "val _ = ";
      PP.add_break ppstrm (1,0);
      PP.begin_block ppstrm PP.CONSISTENT 0;
      PP.add_string ppstrm "let open Type Term infixr -->";
      PP.add_break ppstrm(1,0);
      PP.add_string ppstrm "    val alpha = mk_vartype\"'a\"";
      PP.add_break ppstrm(1,0);
      PP.add_string ppstrm "    val eek = mk_const{Name = \"=\", Ty = alpha --> alpha --> Type.bool}";
      PP.add_break ppstrm(1,0);
      PP.add_string ppstrm "in Term.minTheory_init eek";
      PP.add_break ppstrm(1,0);
      PP.add_string ppstrm "end";
      PP.end_block ppstrm;
      PP.end_block ppstrm))};

val _ = export_theory();

end;
