(* Copyright (C) 1997-2001 by Ken Friis Larsen and Jakob Lichtenberg. *)
structure fdd :> fdd =
struct
	
    open MuddyCore
	
    open bdd
	
    type precision = int
    type domain = int
    type fddvar = int
	
    local 
	val extDomain_ : int vector -> fddvar = app1 (symb "mlfdd_extdomain") 
	    
	fun mkList(start, stop) = 
	    if start > stop then []
	    else start::mkList(start+1, stop)
    in
	fun extDomain l = 
	    let val i = extDomain_ (Vector.fromList(l))
	    in mkList(i,i-1+List.length l) end
    end

    val clearAll: unit -> unit = app1 (symb "mlfdd_clearall") 
    val domainNum: unit -> int = app1 (symb "mlfdd_domainnum") 
    val domainSize: fddvar -> int = app1 (symb "mlfdd_domainsize") 
    val varNum: fddvar -> int = app1 (symb "mlfdd_varnum") 
	
    local 
	fun vectorToList v = Vector.foldl op:: nil v
    in
	val vars: fddvar -> bdd.varnum list = 
	    vectorToList o app1 (symb "mlfdd_vars") 
    end

    val ithSet: fddvar -> varSet = app1 (symb "mlfdd_ithset")
    val domain: fddvar -> bdd  = app1 (symb "mlfdd_domain")
	
    val makeSet: fddvar list -> bdd.varSet =
	(app1 (symb "mlfdd_makeset")) o Vector.fromList
	
    local
	val setPairs_: int vector -> int vector -> bdd.pairSet =
	    app2 (symb "mlfdd_setpairs")
    in
	fun setPairs l = 
	    let val (l1,l2) = ListPair.unzip l
	    in setPairs_ (Vector.fromList l1) (Vector.fromList l2) end
    end
end
