structure Robdd :> Robdd =
struct
	
    prim_type robdd;
    type varSet = robdd; (* just to help people *)
    type restriction = robdd;	
    prim_type pairSet;
    
    type varnum = int
    
    datatype bddop =
	And | Xor | Or | Nand | Nor | Imp | Biimp | Diff | Lessth | Invimp 
	
    local
	open Dynlib
	val hdl  = dlopen {lib = Globals.HOLDIR^"/sigobj/mlrobdd.so", 
			   flag = RTLD_LAZY, global = false}
	val symb = Dynlib.dlsym hdl
	    
	    
	val constants_ : unit -> int * int * int * int 
	                       * int * int * int * int 
	                       * int * int             
	    = app1 (symb "mlrobdd_constants") 

	val (bddop_and, bddop_xor, bddop_or, bddop_nand, 
	     bddop_nor, bddop_imp, bddop_biimp, bddop_diff, 
	     bddop_less, bddop_invimp)
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

	val apply_ : robdd -> robdd -> int -> robdd 
	                                  = app3 (symb "mlrobdd_bdd_apply")
	val exist_  : robdd -> varSet -> robdd 
                                          = app2 (symb "mlrobdd_bdd_exist")
	val forall_ : robdd -> varSet -> robdd 
                                          = app2 (symb "mlrobdd_bdd_forall")
	val appall_ : robdd -> robdd -> int -> varSet -> robdd
	                                  = app4 (symb "mlrobdd_bdd_appall")
	val appex_ : robdd -> robdd -> int -> varSet -> robdd
	                                  = app4 (symb "mlrobdd_bdd_appex")

	val mkset_ : int vector -> varSet = app1 (symb "mlrobdd_makeset")


	val stats_ : unit -> int * int * int * int * int * int * int * int 
	    = app1 (symb "mlrobdd_bdd_stats")


	val makepairset_ : int vector -> int vector -> pairSet
	    = app2 (symb "mlrobdd_makepairset")

	val varnum     = ref 0
	val realvarnum = ref 0
	val setvarnum_ : int -> unit = app1 (symb "mlrobdd_setvarnum")


	val root : robdd -> int = app1 (symb "mlrobdd_root")
	 
    in

    val init : int -> int -> unit         = app2 (symb "mlrobdd_bdd_init")
    val done : unit -> unit               = app1 (symb "mlrobdd_bdd_done")
    val isRunning : unit -> bool          = app1 (symb "mlrobdd_bdd_isrunning")
    fun setvarnum n = (varnum := n;
		       if n > !realvarnum then 
			   (realvarnum := n; setvarnum_ n)
		       else ())
    fun getvarnum () = !varnum

    
    val ithvar : int -> robdd             = app1 (symb "mlrobdd_bdd_ithvar")
    val nithvar : int -> robdd            = app1 (symb "mlrobdd_bdd_nithvar")
    val fromBool : bool -> robdd          = app1 (symb "mlrobdd_fromBool")
    val toBool : robdd -> bool            = app1 (symb "mlrobdd_toBool")

    val var  : robdd -> varnum            = app1 (symb "mlrobdd_bdd_var")
    val low  : robdd -> robdd             = app1 (symb "mlrobdd_bdd_low")
    val high : robdd -> robdd             = app1 (symb "mlrobdd_bdd_high")

    val TRUE = fromBool true
    val FALSE = fromBool false

    val equal : robdd -> robdd -> bool    = app2 (symb "mlrobdd_equal")



    val simplify : robdd -> robdd -> robdd 
	= app2 (symb "mlrobdd_bdd_simplify")

    val printdot : robdd -> unit          = app1 (symb "mlrobdd_bdd_printdot")
    val fnprintdot : string -> robdd -> unit 
	= app2 (symb "mlrobdd_bdd_fnprintdot")

    val printset : robdd -> unit          = app1 (symb "mlrobdd_bdd_printset")
    val fnprintset : string -> robdd -> unit 
	= app2 (symb "mlrobdd_bdd_fnprintset")


    val satcount : robdd -> real = app1 (symb "mlrobdd_bdd_satcount")

    val satone : robdd -> varSet = app1 (symb "mlrobdd_bdd_satone")

    val nodecount : robdd -> int = app1 (symb "mlrobdd_bdd_nodecount")
	
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

    fun makeset_ vector = if Vector.length vector = 0 then Obj.magic FALSE
			  else mkset_ vector

    fun nodup _ nil                   = nil
      | nodup pre ((h : int) :: tail) = if pre = h then nodup pre tail
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

    val scanset  : varSet -> int vector = app1 (symb "mlrobdd_scanset")

    val fromSet = fn x => x
    val toSet_  = fn x => x

    fun apply r1 r2 opr         = apply_ r1 r2 (opr2i opr)
    fun exist vs r              = exist_ r vs
    fun forall vs r             = forall_ r vs
    fun appall r1 r2 opr varset = appall_ r1 r2 (opr2i opr) varset
    fun appex r1 r2 opr varset  = appex_ r1 r2 (opr2i opr) varset


    val NOT : robdd -> robdd  = app1 (symb "mlrobdd_bdd_not")

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

    val replace : robdd -> pairSet -> robdd = app2 (symb "mlrobdd_bdd_replace")

    fun makepairSet (pl : (varnum * varnum) list) = 
        makepairset_ (Vector.fromList(map #1 pl)) (Vector.fromList(map #2 pl))

    val compose : robdd -> robdd -> varnum -> robdd 
	= app3 (symb "mlrobdd_bdd_compose")



    val restrict : robdd -> robdd -> robdd = app2 (symb "mlrobdd_bdd_restrict")
    
    fun mkRestr((v,b), res) = 
	apply res (if b then ithvar v else nithvar v) And 	
    val makeRestriction = foldl mkRestr TRUE


	
(*    type elem = var * low * high *)
    type nodetable = int * (int * int * int) Vector.vector


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
    end
end
