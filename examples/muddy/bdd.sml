(* Copyright (C) 1997-2001 by Ken Friis Larsen and Jakob Lichtenberg. *)
structure bdd :> bdd =
struct

    prim_type bdd;
    type varSet = bdd;
    type assignment = bdd;
    prim_type pairSet;
    type composeSet = pairSet (* not the entire truth *)

    type varnum = int

    datatype bddop =
	And | Xor | Or | Nand | Nor | Imp | Biimp | Diff | Lessth | Invimp


    open MuddyCore

    val constants_ : unit -> int * int * int * int
                           * int * int * int * int
	                   * int * int
	                   * int * int * int * int * int * int * int * int
	           = app1 (symb "mlbdd_constants")

    val (bddop_and, bddop_xor, bddop_or, bddop_nand,
	 bddop_nor, bddop_imp, bddop_biimp, bddop_diff,
	 bddop_less, bddop_invimp,
	 FIXED, FREE, WIN2, WIN2ITE, SIFT, SIFTITE, RANDOM, REORDER_NONE)
	= constants_ ()

    val opr2i =
	fn And    => bddop_and
	 | Xor    => bddop_xor
	 | Or     => bddop_or
	 | Nand   => bddop_nand
	 | Nor    => bddop_nor
	 | Imp    => bddop_imp
	 | Biimp  => bddop_biimp
	 | Diff   => bddop_diff
	 | Lessth => bddop_less
	 | Invimp => bddop_invimp

    val apply_ : bdd -> bdd -> int -> bdd = app3 (symb "mlbdd_bdd_apply")
    val exist_  : bdd -> varSet -> bdd    = app2 (symb "mlbdd_bdd_exist")
    val forall_ : bdd -> varSet -> bdd    = app2 (symb "mlbdd_bdd_forall")
    val appall_ : bdd -> bdd -> int -> varSet -> bdd
	                                  = app4 (symb "mlbdd_bdd_appall")
    val appex_ : bdd -> bdd -> int -> varSet -> bdd
	                                  = app4 (symb "mlbdd_bdd_appex")

    val mkset_ : varnum vector -> varSet  = app1 (symb "mlbdd_makeset")


    val stats_ : unit -> int * int * int * int * int * int * int * int
	                                  = app1 (symb "mlbdd_bdd_stats")


    val makepairset_ : varnum vector -> varnum vector -> pairSet
	                                  = app2 (symb "mlbdd_makepairset")

    val makebddpairset_ : varnum vector -> bdd vector -> pairSet
	                                  = app2 (symb "mlbdd_makebddpairset")


    val setVarnum : int -> unit = app1 (symb "mlbdd_bdd_setvarnum")
    val getVarnum : unit -> int = app1 (symb "mlbdd_getvarnum")

    val root : bdd -> int = app1 (symb "mlbdd_root")
    val hash = root

    val init : int -> int -> unit         = app2 (symb "mlbdd_bdd_init")
    val done : unit -> unit               = app1 (symb "mlbdd_bdd_done")
    val isRunning : unit -> bool          = app1 (symb "mlbdd_bdd_isrunning")

    val ithvar : varnum -> bdd  = app1 (symb "mlbdd_bdd_ithvar")
    val nithvar : varnum -> bdd = app1 (symb "mlbdd_bdd_nithvar")

    val fromBool : bool -> bdd = app1 (symb "mlbdd_fromBool")
    val toBool : bdd -> bool   = app1 (symb "mlbdd_toBool")

    val var  : bdd -> varnum = app1 (symb "mlbdd_bdd_var")
    val low  : bdd -> bdd    = app1 (symb "mlbdd_bdd_low")
    val high : bdd -> bdd    = app1 (symb "mlbdd_bdd_high")

    val TRUE = fromBool true
    val FALSE = fromBool false

    val equal : bdd -> bdd -> bool = app2 (symb "mlbdd_equal")

    local fun C f x y = f y x in
    val simplify : bdd -> bdd -> bdd = C (app2 (symb "mlbdd_bdd_simplify")) end

    val printdot : bdd -> unit             = app1 (symb "mlbdd_bdd_printdot")
    val fnprintdot : string -> bdd -> unit = app2 (symb "mlbdd_bdd_fnprintdot")

    val printset : bdd -> unit             = app1 (symb "mlbdd_bdd_printset")
    val fnprintset : string -> bdd -> unit = app2 (symb "mlbdd_bdd_fnprintset")

    val bddSave : string -> bdd -> unit    = app2 (symb "mlbdd_bdd_fnsave")
    val bddLoad : string -> bdd            = app1 (symb "mlbdd_bdd_fnload")


    val satcount : bdd -> real = app1 (symb "mlbdd_bdd_satcount")

    val nodecount : bdd -> int = app1 (symb "mlbdd_bdd_nodecount")

    fun stats unit =
	let val (p,nn,mn,fnum,minn,vn,cs,gn) = stats_ unit
	in
	    {produced     = p,
	     nodenum      = nn,
	     maxnodenum   = mn,
	     freenodes    = fnum,
	     minfreenodes = minn,
	     varnum       = vn,
	     cachesize    = cs,
	     gbcnum       = gn}
	end

    fun makeset_ vector = if Vector.length vector = 0 then (*Obj.magic*) FALSE
			  else mkset_ vector

    fun nodup _ nil                   = nil
      | nodup pre (h :: tail) = if pre = h then nodup pre tail
					else h :: nodup h tail
    fun makeset varlist =
	let val positive = List.filter (fn i => i >= 0) varlist
	    val sorted = Listsort.sort Int.compare positive
	    val nodup  = case sorted of
		             nil => nil
			   | h :: tail => h :: nodup h tail
	in
	    makeset_ (Vector.fromList(nodup))
	end

    val scanset : varSet -> varnum vector = app1 (symb "mlbdd_bdd_scanset")

    val support : bdd -> varSet = app1 (symb "mlbdd_bdd_support")

    val fromSet = fn x => x
    val toSet_  = fn x => x

    fun apply r1 r2 opr         = apply_ r1 r2 (opr2i opr)
    fun exist vs r              = exist_ r vs
    fun forall vs r             = forall_ r vs
    fun appall r1 r2 opr varset = appall_ r1 r2 (opr2i opr) varset
    fun appex r1 r2 opr varset  = appex_ r1 r2 (opr2i opr) varset


    val NOT : bdd -> bdd  = app1 (symb "mlbdd_bdd_not")
    val ITE : bdd -> bdd -> bdd -> bdd = app3(symb "mlbdd_bdd_ite")

    fun AND (r1, r2)    = apply_ r1 r2 bddop_and
    fun XOR (r1, r2)    = apply_ r1 r2 bddop_xor
    fun OR (r1, r2)     = apply_ r1 r2 bddop_or
    fun NAND (r1, r2)   = apply_ r1 r2 bddop_nand
    fun NOR (r1, r2)    = apply_ r1 r2 bddop_nor
    fun IMP (r1, r2)    = apply_ r1 r2 bddop_imp
    fun BIIMP (r1, r2)  = apply_ r1 r2 bddop_biimp
    fun DIFF (r1, r2)   = apply_ r1 r2 bddop_diff
    fun LESSTH (r1, r2) = apply_ r1 r2 bddop_less
    fun INVIMP (r1, r2) = apply_ r1 r2 bddop_invimp

    val replace : bdd -> pairSet -> bdd = app2 (symb "mlbdd_bdd_replace")

    fun makepairSet pl =
        let val (old,new) = ListPair.unzip pl
        in makepairset_ (vector old) (vector new) end

    val compose_ : bdd -> bdd -> varnum -> bdd
	= app3 (symb "mlbdd_bdd_compose")

    fun compose (v,r2) r1 = compose_ r1 r2 v

    val veccompose : pairSet -> bdd -> bdd = app2 (symb "mlbdd_bdd_veccompose")

    fun composeSet pl =
        let val (old, new) = ListPair.unzip pl
        in  makebddpairset_ (vector old) (vector new) end


    fun assign((v,b), res) = apply res (if b then ithvar v else nithvar v) And
    val assignment = List.foldl assign TRUE
    val fromAssignment = fn x => x
    val toAssignment_ = fn x => x

    fun isBool bdd = (toBool bdd; true) handle Domain => false

    fun getAssignment bdd =
        let fun loop bdd acc =
                if isBool bdd then acc
                else let val var = var bdd
                         val low = low bdd
			 val high = high bdd
                     in  if equal low FALSE then loop high ((var,true) :: acc)
                         else loop low ((var,false) :: acc)
                     end
        in  loop bdd [] end

    val restrict : bdd -> bdd -> bdd = app2 (symb "mlbdd_bdd_restrict")

    val satone_ : bdd -> assignment = app1 (symb "mlbdd_bdd_satone")
    fun satone r = if equal r FALSE then raise Domain
                   else satone_ r

    val fullsatone_ : bdd -> assignment = app1 (symb "mlbdd_bdd_fullsatone")
    fun fullsatone r = if equal r FALSE then raise Domain
                   else fullsatone_ r

    type nodetable = int * (varnum * int * int) Vector.vector


    (* Three helper functions, used to normalize rootno *)
    fun table size = (size, ref 0, Array.array(size,[]))
    fun mem i []           = NONE
      | mem i ((k,d) :: t) = if i = k then SOME d
			     else mem i t
    fun add (size,next,tab) r =
	let val code = r mod size
	    val slot = Array.sub(tab,code)
	in
	    case mem r slot of
		NONE => let val n = !next
			in  next := n + 1;
			    Array.update(tab, code, (r,n) :: slot);
			    n
			end
	      | SOME n => n
	end

    fun nodetable r =
	let val nc = nodecount r + 2
	    val rootno = add (table nc) o root
	    val tab = Array.array(nc,NONE)
	    fun peek i = Array.sub(tab, i)
	    fun update i d = Array.update(tab,i,SOME d)

	    fun node r =
		let val root = rootno r
		in
		    case peek root of
			NONE   => let val low = low r
				      val high = high r
				  in  update root (var r,
						   rootno low,
						   rootno high);
				      node low;
				      node high
				  end
		      | SOME _ => ()
		end
	in
	    update (rootno TRUE) (0,0,0);
	    update (rootno FALSE) (0,0,0);
	    node r;
	    (rootno r,
	     Vector.tabulate(nc, fn i => valOf(Array.sub(tab,i))))
	end

    (* BuDDy tuning stuff *)
    val setMaxincrease : int -> int = app1 (symb "mlbdd_bdd_setmaxincrease")
    val setCacheratio  : int -> int = app1 (symb "mlbdd_bdd_setcacheratio")

    val setprintgc : bool -> string -> string -> unit =
	app3 (symb "mlbdd_setprintgc")

    fun verbosegc NONE           = setprintgc false "" ""
      | verbosegc (SOME(s1, s2)) = setprintgc true s1 s2


    (* Variable reordering stuff *)
    type fixed = int
    val addvarblock  : varnum -> varnum -> fixed -> unit
        = app3 (symb "mlbdd_bdd_intaddvarblock")
    val clrvarblocks  : unit -> unit = app1 (symb "mlbdd_bdd_clrvarblocks")


    type method = int
    val reorder     : method -> unit = app1 (symb "mlbdd_bdd_reorder")
    val autoReorder : method -> method = app1 (symb "mlbdd_bdd_autoreorder")
    val autoReorderTimes : method -> int -> method = app2 (symb "mlbdd_bdd_autoreorder_times")

    val getMethod : unit -> method = app1 (symb "mlbdd_bdd_getreorder_method")
    val getTimes  : unit -> int    = app1 (symb "mlbdd_bdd_getreorder_times")

    val disableReorder : unit -> unit = app1 (symb "mlbdd_bdd_disable_reorder")
    val enableReorder  : unit -> unit = app1 (symb "mlbdd_bdd_enable_reorder")

    type level = int
    val varToLevel : varnum -> level = app1 (symb "mlbdd_bdd_var2level")
    val varAtLevel : level -> varnum = app1 (symb "mlbdd_bdd_level2var")

end
