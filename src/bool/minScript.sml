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

open Parse Theory;

val _ = new_theory "min";

val _ = new_type{Name="bool", Arity=0};
val _ = new_type{Name="ind",  Arity=0};
val _ = new_type{Name="fun",  Arity=2};

val _ = new_infix{Name = "=",   Ty=Type `: 'a -> 'a -> bool`,     Prec=100};
val _ = new_infix{Name = "==>", Ty=Type `: bool -> bool -> bool`, Prec=200};
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
