structure Portable_PrettyPrint =
    struct
	fun install_pp path s = Fail "install_pp can't be used."

	type ppstream = ppstream
	    
	open PP
	    
	fun with_ppstream ppstrm = 
	    {add_string     = add_string ppstrm, 
	     add_break      = add_break ppstrm, 
	     begin_block    = begin_block ppstrm, 
	     end_block      = fn () => end_block ppstrm, 
	     add_newline    = fn () => add_newline ppstrm, 
	     clear_ppstream = fn () => clear_ppstream ppstrm, 
	     flush_ppstream = fn () => flush_ppstream ppstrm}

	fun defaultConsumer () =
	    {consumer  = fn s => TextIO.output(TextIO.stdOut, s),
	     linewidth = 72, (* heuristic taken from help *)
	     flush     = fn () => TextIO.flushOut TextIO.stdOut}
	    
	fun pp_to_string linewidth ppfn ob = 
	    let val l = ref ([]:string list)
		fun attach s = l := (s::(!l))
	    in with_pp {consumer = attach, 
			linewidth=linewidth, flush = fn()=>()}
                (fn ppstrm =>  ppfn ppstrm ob);
		String.concat(List.rev(!l))
	    end

	val mk_consumer = fn x => x


(* Support for minimizing the number of brackets *)
datatype gravity = TOP | APPL | INFIX of int | WEAK | BOTTOM;

fun gravity_geq TOP _ = true
  | gravity_geq _ TOP = false
  | gravity_geq APPL _ = true
  | gravity_geq _ APPL = false
  | gravity_geq (INFIX n) (INFIX m) = (n >= m)
  | gravity_geq (INFIX _) _ = true
  | gravity_geq _ (INFIX _) = false
  | gravity_geq WEAK _ = true
  | gravity_geq _ WEAK = false
  | gravity_geq _ BOTTOM = true

fun add_lparen ppstrm grav1 grav2 =
   if (gravity_geq grav1 grav2)
   then add_string ppstrm "("
   else ();

fun add_rparen ppstrm grav1 grav2 =
   if (gravity_geq grav1 grav2)
   then add_string ppstrm ")"
   else ()


(*---------------------------------------------------------------------------
 * Print a list of items.
 *
 *     pfun = print_function
 *     dfun = delim_function
 *     bfun = break_function
 *---------------------------------------------------------------------------*)
fun pr_list_to_ppstream ppstrm pfun dfun bfun =
 let fun pr [] = ()
       | pr [i] = pfun ppstrm i
       | pr (i::rst) = ( pfun ppstrm i; dfun ppstrm ; bfun ppstrm ; pr rst )
 in 
    pr 
 end;


(*---------------------------------------------------------------------------
 * Simple and heavily used.
 * pfun = item printing function
 * dfun = delimiter printing function
 * bfun = break printer function
 *---------------------------------------------------------------------------*)
fun pr_list pfun dfun bfun =
   let fun pr [] = ()
         | pr [i] = pfun i
         | pr (i::rst) = ( pfun i; dfun() ; bfun() ; pr rst )
   in
      pr 
   end;

end;
