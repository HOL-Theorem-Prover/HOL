(*****************************************************************************)
(* Ken Larsen's BDDOracle package opened up and modified                     *)
(* to support BDDs listed in a table of the form:                            *)
(*                                                                           *)
(*    [...,(<CONST>(<varstruct>), <robdd>),...]                              *)
(*                                                                           *)
(* The original package uses the type:                                       *)
(*                                                                           *)
(*     type mapping = (string, Robdd.varnum) Binarymap.dict                  *)
(*                                                                           *)
(* this is renamed to:                                                       *)
(*                                                                           *)
(*     type var_map = (string, Robdd.varnum) Binarymap.dict                  *)
(*                                                                           *)
(* BuDDy package: http://britta.it.dtu.dk/~jl/buddy                          *)
(*                                                                           *)
(*****************************************************************************)

structure robddLib :> robddLib = 
struct

(* hand loading for interactive system
  app load ["Binarymap", "Robdd", "Net", "Polyhash", "Psyntax", "unwindLib"];

*)

open HolKernel Net Conv Psyntax;

type robdd = Robdd.robdd;
type 'a net = 'a Net.net;

infix ## |-> THENC;

exception Error;
fun error () = raise Error;

fun ERR msg func = 
    raise Exception.HOL_ERR{origin_structure = "robddLib",
                            origin_function  = func,
                            message          = msg};

val tag = Tag.read "BDD";

val EX_OR_CONV     = Conv.EXISTS_OR_CONV;  
val term_to_string = Parse.term_to_string;


fun TERNOP_CONV cnv = 
 RAND_CONV cnv 
  THENC RATOR_CONV (RAND_CONV cnv THENC RATOR_CONV(RAND_CONV cnv));

val T = mk_const("T", Type.bool)
and F = mk_const("F", Type.bool);

fun mk_conj1(t1,t2) =
 if t1 = T 
  then t2
  else 
  if t2 = T 
   then t1
   else 
   if t1 = F orelse t2 = F then F else mk_conj(t1,t2);

fun mk_disj1(t1,t2) =
 if t1 = F 
  then t2
  else 
  if t2 = F 
   then t1
   else 
   if t1 = T orelse t2 = T then T else mk_disj(t1,t2);


(* Should var_map be a hash table? *)

type var_map = (string, int) Binarymap.dict;
type table   = int * var_map;

(*****************************************************************************)
(* Create an empty (string,int)dict                                          *)
(*****************************************************************************)

val empty_var_map = 
 Binarymap.mkDict String.compare : (string, int) Binarymap.dict;

val empty_table = (0,empty_var_map) : table;

fun insert (c,table) name = (c+1, Binarymap.insert(table,name,c));

(* timing 
use "reftime.ml";
val insert_time = ref 0.0;
val insert_fn = insert;
fun insert (c,table) = reftime insert_time (insert_fn (c,table));
*)

fun peek (_,table) name = Binarymap.peek(table,name);

fun size tab = Binarymap.numItems tab;

fun peek_map table name = Binarymap.peek(table,name);

(*****************************************************************************)
(* Convert a string to a BDD node number using var_map                       *)
(*****************************************************************************)

fun var_to_int (var_map:var_map) s   = Binarymap.find(var_map,s);

(* timing 
val var_to_int_time = ref 0.0;
val var_to_int_fn = var_to_int;
val var_to_int = reftime var_to_int_time var_to_int_fn;
*)

(*****************************************************************************)
(* Create a dictionary from a list by repeated insertion                     *)
(*****************************************************************************)

fun list_to_var_map l =
 let fun list_to_var_map_aux n []     = empty_var_map
      |  list_to_var_map_aux n (x::l) =
          Binarymap.insert(list_to_var_map_aux(n+1)l,x,n)
 in
  list_to_var_map_aux 0 l
 end;

val var_map_to_pairs = Binarymap.listItems;


(*****************************************************************************)
(* The BDDs associated with terms are stored in a bdd_map:                   *)
(*                                                                           *)
(*    type bdd_map =                                                         *)
(*     (Term.term, Robdd.robdd)Polyhash.hash_table * (Term.term)Net.net      *)
(*                                                                           *)
(* To compute the BDD of ``<constant> <args>``                               *)
(*                                                                           *)
(*   1. check to see if ``<constant> <args>`` already has                    *)
(*      a previously computed BDD (use hash table) and return it             *)
(*      if it does;                                                          *)
(*                                                                           *)
(*   2. if ``<constant> <args>`` doesn't have a precomputed BDD,             *)
(*      then find the least general term with a BDD that can be              *)
(*      instantiated to ``<constant> <args>`` (e.g. the LHS of the           *)
(*      definition of ``<constant>``) and create a new BDD from              *)
(*      the corresponding BDD (use net)                                      *)
(*                                                                           *)
(* The terms of the form ``<constant> <args>`` are called the                *)
(* descriptors of the corresponding BDDs in the hash table.                  *)
(*****************************************************************************)

type bdd_map = 
 (Term.term, Robdd.robdd)Polyhash.hash_table * (Term.term)Net.net;

val PolyTableSizeHint = ref 1000;

val current_bdd_map:bdd_map = 
 (Polyhash.mkPolyTable
  (!PolyTableSizeHint, 
    Exception.HOL_ERR
      {origin_structure = "BDDOracle",
       origin_function  = "Polyhash.find",
       message          = "Hash table lookup failure"}),
  Net.empty_net);

        
fun lookup_var var_map name =
 case peek_map var_map name of
  SOME i => Robdd.ithvar i
 | NONE   => ERR ("The variable "^name^" is not in the mapping") "lookup_var";

(*****************************************************************************)
(* Check that a term substitution [(new1,old1),...,(newn,oldn)]              *)
(* is 1-1, i.e. new1,...,newn are distinct                                   *)
(* and that all the variables are boolean,                                   *)
(* return a list of [(oldname1,newname1),...,(oldnamen,newnamen)]            *)
(*****************************************************************************)

fun check_var tm =
 is_var tm orelse 
 ERR ("``"^term_to_string tm^"`` is not a variable") "check_var";

fun match_to_pairs []             = []
 |  match_to_pairs ((new,old)::l) =
     if not(exists (fn (new',_) => new=new') l) 
         andalso (type_of new = bool) andalso check_var new
         andalso (type_of old = bool) andalso check_var old
      then (fst(dest_var old),fst(dest_var new))::match_to_pairs l
      else ERR "BDD replacement or matching problem" "match_to_pairs";

(*****************************************************************************)
(*    subst_bdd tab [(oldname1,newname1),...,(oldnamen,newnamen)] bdd        *)
(*                                                                           *)
(* gives result of substituting newnamei for oldnamei (1<=i<=n) in bdd       *)
(*****************************************************************************)

fun subst_bdd var_map old_new_list bdd =
 let val v2i = var_to_int var_map
 in
  Robdd.replace bdd (Robdd.makepairSet(List.map (v2i ## v2i) old_new_list))
 end;

(*****************************************************************************)
(* Scan a list of keys in normal order to find the first                     *)
(* one with an entry in a hashtable. Return key-data pair.                   *)
(*****************************************************************************)

fun find_data msg htbl []      = ERR msg "find_data"
 |  find_data msg htbl (k::kl) = (case Polyhash.peek htbl k of
                                     SOME data => (k,data)
                                   | NONE      => find_data msg htbl kl);

(*****************************************************************************)
(* Looks up a term in a net. Returns NONE if no match in net found.          *)
(* If a match is found then a renaming of the corresponding BDD in the       *)
(* hash table is attempted.                                                  *)
(*****************************************************************************)

fun NetPeek var_map (htbl,net) tm =
 let val netl = Net.lookup tm net
 in
  if null netl
   then NONE
   else
   let val (descr,bdd) =
        find_data 
         "Unhashed application"
         htbl 
         (rev netl)
   in
    SOME
     (subst_bdd var_map (match_to_pairs(fst(Psyntax.match_term descr tm))) bdd)
   end
 end;

(*****************************************************************************)
(* Timings:                                                                  *)
(*                                                                           *)
(* Old version:                                                              *)
(* time term_to_bdd (rhs(concl nextstate_rel_eqn));                          *)
(* runtime: 0.030s,    gctime: 0.000s,     systime: 0.000s.                  *)
(* > val it = <robdd> : Robdd.robdd                                          *)
(*                                                                           *)
(* New version:                                                              *)
(* time term_to_bdd (rhs(concl nextstate_rel_eqn));                          *)
(* runtime: 0.350s,    gctime: 0.000s,     systime: 0.000s.                  *)
(* > val it = <robdd> : Robdd.robdd                                          *)
(*****************************************************************************)

fun fromTerm_aux var_map (htbl,net) tm =
 case Polyhash.peek htbl tm of
    SOME bdd => bdd
  | NONE
    =>
    case NetPeek var_map (htbl,net) tm of
       SOME bdd => bdd
     | NONE
       =>
       if Term.is_var tm then 
           let val {Name,Ty} = Term.dest_var tm
           in  
               if Ty = Type.bool then lookup_var var_map Name
               else ERR ("Variable "^Name^" is not of type bool") "fromTerm"
           end 
       else
        let val (comb,args) = Dsyntax.strip_comb tm
            val {Name, Ty}  = Term.dest_const comb
        in
        case Name of
         "/\\"  => binExp var_map (htbl,net) Robdd.And args
       | "\\/"  => binExp var_map (htbl,net) Robdd.Or args
       | "==>"  => binExp var_map (htbl,net) Robdd.Imp args
       | "="    => let val [arg1,arg2] = args
                   in
                    if Term.is_var arg1 andalso Term.is_var arg2
                    then binExp var_map (htbl,net) Robdd.Biimp args
                    else (ListPair.foldl (fn(x1,x2,bdd) => 
                            Robdd.AND
                              (binExp var_map (htbl,net) Robdd.Biimp [x1,x2],
                               bdd))
                         Robdd.TRUE
                         (strip_pair arg1,strip_pair arg2)
                           handle Interrupt => raise Interrupt
                                |  _ => ERR "Can't make BDD of equation"
                                            "fromTerm")
                   end
       | "~"    => Robdd.NOT(fromTerm_aux var_map (htbl,net) (List.hd args))
       | "T"    => Robdd.TRUE
       | "F"    => Robdd.FALSE
       | "!"    => quantExp var_map (htbl,net) Dsyntax.strip_forall 
                            Robdd.forall tm
       | "?"    => quantExp var_map (htbl,net) Dsyntax.strip_exists 
                          Robdd.exist tm
       | "COND" => condExp var_map (htbl,net) args
       | _      => ERR ("Can't make BDD from "^Name) "fromTerm_aux"   
  end
   
and binExp var_map bdd_map opr [t1,t2] = 
    let val e1 = fromTerm_aux var_map bdd_map t1
        val e2 = fromTerm_aux var_map bdd_map t2
    in  Robdd.apply e1 e2 opr
    end
  | binExp _ _ _ _ = error() (* impossible *)
    
and quantExp var_map bdd_map strip quant t =
    let val (vars,body) = strip t
        fun find v = 
            case peek_map var_map (#Name(Term.dest_var v)) of
                SOME i => i
              | NONE   => ERR ("The variable "^
                                   (#Name(Term.dest_var v))^
                                   " is not in the mapping")
                                  "quantExp"
        val varset = Robdd.makeset (List.map find vars)
        val ebody = fromTerm_aux var_map bdd_map body
    in  
     quant varset ebody
    end

and condExp var_map bdd_map [x,y,z] = 
    let val x' = fromTerm_aux var_map bdd_map x
        val y' = fromTerm_aux var_map bdd_map y
        val z' = fromTerm_aux var_map bdd_map z
    in
        Robdd.OR(Robdd.AND(x',y'),Robdd.AND(Robdd.NOT x',z'))
    end
  | condExp _ _ _ = error();

fun fromTerm var_map bdd_map tm =
    let  
        val _ = if not (Robdd.isRunning()) then Robdd.init 10000 1000
                else ()
        val _ = if Robdd.getvarnum() < size var_map then 
                    Robdd.setvarnum(size var_map)
                else ()
    in 
       fromTerm_aux var_map bdd_map tm 
    end;


(*****************************************************************************)
(* BDD_CONV bdd_map tm --> |- tm = tm'                                       *)
(*                                                                           *)
(* where tm' is suitable for representing as a BDD using term_to_bdd.        *)
(*                                                                           *)
(* The bdd_map parameter is the part of the BDD state, needed to             *)
(* determine which terms are descriptors in the BDD hash table, and so       *)
(* need processing as illustrated below.                                     *)
(*                                                                           *)
(* Robdd.replace can only replace distinct variables with distinct           *)
(* variables.  Thus, for example, if:                                        *)
(*                                                                           *)
(*    |- Foo (u, v, w, x, y, z) = (u \/ v) /\ w /\ (~x = ~y) /\ ~z           *)
(*                                                                           *)
(* then the BDD of ``Foo(a,b,p,q,p,(x/\y))`` is computed by                  *)
(* first transforming it (using BDD_CONV) to:                                *)
(*                                                                           *)
(*   ?p' z.                                                                  *)
(*    (p' = p)       /\             (* Note: "p"    is repeated         *)   *)
(*    (z = (x /\ y)) /\             (* Note: "x/\y" is not a variable   *)   *)
(*    Foo (a, b, p, q, new1, new2)                                           *)
(*                                                                           *)
(* and then computing the BDD of this.                                       *)
(*****************************************************************************)


(*****************************************************************************)
(* bdd_match_split partitions the result of matching a term and a descriptor *)
(*                                                                           *)
(*    [(e1,v1),...,(en,vn)]                                                  *)
(*                                                                           *)
(* into a substitution                                                       *)
(*                                                                           *)
(*    [(v1',v1),...,(vn',vn)]                                                *)
(*                                                                           *)
(* and a list of the form for ?-quantification                               *)
(*                                                                           *)
(*    [(new1,ei1),...,(newm,eim)]                                            *)
(*                                                                           *)
(* where newi is a variant of the corresponding vi not clashing              *)
(* with any variable occurring in e1,...,en                                  *)
(*                                                                           *)
(* Accumulator acc holds those variables that cannot be substituted in.      *)
(* Initially it is the list of variables in the descriptor of the BDD,       *)
(* but during the execution of bdd_match_split all variables being           *)
(* substituted in are added.                                                 *)
(* qlist are the bindings to be handled by ?-quantification,                 *)
(* rlist are the bindings to be handled by Robdd.replace.                    *)
(*****************************************************************************)

fun bdd_match_split []         acc = ([],[])
 |  bdd_match_split ((e,v)::l) acc = 
     if not(is_var e) orelse mem e acc                         (* ?-quant    *)
      then let val (qlist,rlist) = bdd_match_split l acc
           in
            ((e,v)::qlist, rlist)
           end
      else let val (qlist,rlist) = bdd_match_split l (e::acc)  (* subst      *)
           in
            (qlist, (e,v)::rlist)
           end;

fun BDD_CONV (htbl,net) tm =
 case Polyhash.peek htbl tm of
    SOME _ => ALL_CONV tm
  | NONE
    =>
    case NetPrePeek (htbl,net) tm of
       SOME th => th
     | NONE
       =>
       if Term.is_var tm then ALL_CONV tm
       else
           let val (comb,args) = Dsyntax.strip_comb tm
               val {Name, Ty}  = Term.dest_const comb
           in
            case Name of
                "/\\"  => BINOP_CONV (BDD_CONV (htbl,net)) tm
              | "\\/"  => BINOP_CONV (BDD_CONV (htbl,net)) tm
              | "==>"  => BINOP_CONV (BDD_CONV (htbl,net)) tm
              | "="    => BINOP_CONV (BDD_CONV (htbl,net)) tm
              | "~"    => RAND_CONV  (BDD_CONV (htbl,net)) tm
              | "T"    => ALL_CONV tm
              | "F"    => ALL_CONV tm
              | "!"    => QUANT_CONV (BDD_CONV (htbl,net)) tm
              | "?"    => QUANT_CONV (BDD_CONV (htbl,net)) tm
              | "COND" => TERNOP_CONV(BDD_CONV (htbl,net)) tm
              | _      => ALL_CONV tm
           end


(*****************************************************************************)
(* Looks up a term in a net. Returns NONE if no match in net found.          *)
(* If a match is found then BDD_MATCH_CONV is applied                        *)
(*****************************************************************************)

and NetPrePeek (htbl,net) tm =
 let val netl = Net.lookup tm net
 in
  if null netl
   then NONE
   else
   let val (descr,bdd) =
        find_data 
         "Unhashed application"
         htbl 
         (rev netl)
   in
    SOME (BDD_MATCH_CONV (htbl,net) descr tm)
   end
 end

and BDD_MATCH_CONV bdd_map descr tm =
 let val (mlist,tysubst) = Psyntax.match_term descr tm
     val _ = if not(tysubst = []) then ERR "Bad match" "bdd_match" else ()
     val vars  = U(map (all_vars o fst) mlist)
     val (qlist,rlist)  = bdd_match_split mlist (free_vars descr)
     val (qvars,rlist',qconj)  = 
          foldr (fn ((e,v),(vl,sl,tm)) => 
                    let val v' = variant vars v
                    in
                     (v'::vl,
                      (if v=v' then sl else (v', v)::sl),
                      mk_conj1(mk_eq(v',e),tm))
                     end)
                ([],[],T)
                qlist
 in
  if null qvars
   then ALL_CONV tm
   else
   let val qtm = list_mk_exists(qvars, 
                    mk_conj1(qconj, subst (rlist@rlist') descr))
       val th1 = SYM(unwindLib.EXPAND_AUTO_CONV [] qtm)
       val th2 = unwindLib.DEPTH_EXISTS_CONV 
                  (RATOR_CONV(RAND_CONV(BDD_CONV bdd_map))) 
                  qtm
       val th3 = TRANS th1 th2
   in
    if tm = lhs(concl th3) then th3 else ERR "unwind error" "bdd_match"
   end
 end;


(*****************************************************************************)
(* Transform a term to one that can be represented as a BDD                  *)
(*****************************************************************************)

fun BDD_TR bdd_map tm = rhs(concl(BDD_CONV bdd_map tm));

(*****************************************************************************)
(* Adds a variable to a table if it isn't already there                      *)
(* (identity function if it is)                                              *)
(*****************************************************************************)

fun add_var_to_table(name, tab:table) : table =
 case peek tab name of
     SOME _ => tab
   | NONE   => insert tab name;

fun add_vars_to_table (tab:table) varlist =
 List.foldr add_var_to_table tab (List.map (fst o dest_var) varlist);

(*****************************************************************************)
(* Add a list of variable names to a table                                   *)
(*                                                                           *)
(* add_names_to_table tab ["v1",...,"vn"] -- adds vi,...,vn to tab           *)
(*                                                                           *)
(*****************************************************************************)

val add_names_to_table = foldl add_var_to_table;


(*****************************************************************************)
(* A bdd_state holds a map from variables to BDD node numbers                *)
(* (table = int*var_map) and a map from descriptors to BDDs (bdd_map)        *)
(*****************************************************************************)

(*****************************************************************************)
(* The BDD state is held in global variable bdd_state,                       *)
(* which is a reference to a pair: the first component being the table       *)
(* and the second being the bdd_map                                          *)
(*****************************************************************************)

val bdd_state = ref(empty_table,current_bdd_map);

(*****************************************************************************)
(* Reset BDD state to have an empty BDD hash table and variable table        *)
(* with a given variable ordering                                            *)
(*****************************************************************************)

fun reset_state var_order =
 let val (_,(htbl,net)) = !bdd_state
 in
  (map (fn(tm,_) => Polyhash.remove htbl tm) (Polyhash.listItems htbl);
   bdd_state := (add_names_to_table empty_table var_order,
                 (htbl,Net.empty_net)))
 end;

(*****************************************************************************)
(* Show var_map and bdd_map                                                  *)
(*****************************************************************************)

fun show_var_map() = var_map_to_pairs(snd(fst(!bdd_state)));

fun show_bdd_map() = Polyhash.listItems(fst(snd(!bdd_state)));

(*****************************************************************************)
(* Get variable order in current state                                       *)
(*****************************************************************************)

fun get_var_order() = map fst (sort (fn(_,m)=>fn(_,n)=>m<n) (show_var_map()));

(*****************************************************************************)
(* Convert a term to a BDD in current BDD state, adding any new variables    *)
(* to the state's var_map, if necessary.                                     *)
(*****************************************************************************)

fun term_to_bdd tm =
 let val (tab,bdd_map) = !bdd_state
     val (c',var_map') = add_vars_to_table tab (all_vars tm)
     val _             = bdd_state := ((c', var_map'), bdd_map)
 in
  fromTerm var_map' bdd_map tm
   handle Interrupt => raise Interrupt
             |    _ => let val tm' = BDD_TR bdd_map tm
                           val (c'',var_map'') = add_vars_to_table 
                                                     (c', var_map') 
                                                     (all_vars tm')
                       in
                        bdd_state := ((c'', var_map''), snd(!bdd_state));
                        fromTerm var_map'' bdd_map tm'
                       end
 end;

(*****************************************************************************)
(* Add a variable to the BDD state, returning the node number. If the        *)
(* variable already exists, then BDD state is unchanged and the variable's   *)
(* existing number is returned                                               *)
(*****************************************************************************)

fun add_var s = Robdd.var(term_to_bdd(mk_var(s,bool)));

(*****************************************************************************)
(* Add a definition of a constant to a net of BDDs (bdd_map),                *)
(* if necessary first extending the variable table                           *)
(*                                                                           *)
(* First add variables in defn to tab, then compute BDD of RHS of defn,      *)
(* and add (descriptor,bdd) to bdd_map.                                      *)
(*                                                                           *)
(*****************************************************************************)

fun add_definition defn (tab,bdd_map) 
    : ((Term.term * Robdd.robdd) * (table * bdd_map)) =
 let val defn_tm       = concl defn
     val (_,eqn)       = strip_forall defn_tm
     val (tm_descr,tm) = dest_eq eqn
     val (c',var_map') = add_vars_to_table tab (all_vars tm)
     val _             = bdd_state := ((c', var_map'), bdd_map)
     val tm_bdd        = fromTerm var_map' bdd_map tm
                           handle Interrupt => raise Interrupt
                           | _ => 
                             let val tm' = BDD_TR bdd_map tm
                                 val (c'',var_map'') = add_vars_to_table 
                                                         (c', var_map')
                                                         (all_vars tm')
                             in
                               bdd_state := ((c'',var_map''),snd(!bdd_state));
                               fromTerm var_map'' bdd_map tm'
                             end
     val (htbl,net)    = bdd_map
     val bdd_map'      = ((Polyhash.insert htbl (tm_descr,tm_bdd);htbl),
                          Net.enter(tm_descr,tm_descr)net)
 in
  ((tm_descr,tm_bdd),((c',var_map'), bdd_map'))
 end;

(*****************************************************************************)
(* Add a definition to BDD state                                             *)
(*****************************************************************************)

fun add_defn th =
 let val ((tm,bdd),bdd_state') = add_definition th (!bdd_state)
 in
  bdd_state := bdd_state'; (tm,bdd)
 end;

(*****************************************************************************)
(* Test whether is BDD is a tautology                                        *)
(*****************************************************************************)

fun is_taut bdd =
 (Robdd.toBool bdd = true)
 handle Domain => false 
      | Error  => false;

(*****************************************************************************)
(* Versions of Ken Larsen's oracle functions that                            *)
(* use the BDD state                                                         *)
(*****************************************************************************)

(* Old code
fun bddCheck tm =
 let val (tab,bdd_map) = !bdd_state
     val (_,var_map')  = add_vars_to_table tab (all_vars tm)
 in 
  (SOME(Robdd.toBool (fromTerm var_map' bdd_map tm)))
   handle Domain => NONE 
        | Error  => NONE
 end;
*)

fun bddCheck tm =
 SOME(Robdd.toBool(term_to_bdd tm))
  handle Domain => NONE 
       | Error  => NONE;

(*****************************************************************************)
(* Test whether a term corresponds to a true BDD -- true or false returned   *)
(*****************************************************************************)

fun isT tm =
 case bddCheck tm of
    SOME true => true
  | _         => false;


fun mk_bdd_thm tm = 
 Thm.mk_oracle_thm 
  tag 
  ([], (if valOf (bddCheck tm) 
         then tm
         else Dsyntax.mk_neg tm)
  handle Interrupt => raise Interrupt
               | _ => ERR "Could not reduce term" "mk_bdd_thm");

fun BDD_TAC (asl:Term.term list,tm) =
 case bddCheck tm of
    SOME true => ([], fn [] => mk_bdd_thm tm)
  | _         => ERR "bddCkeck failed" "BDD_TAC"

(*****************************************************************************)
(* Finds an assignment that makes a term F                                   *)
(*****************************************************************************)

(* Old version
fun findAssignment(var_map, r) = 
 let val pairs  = var_map_to_pairs var_map
     infix 9 sub 
     val op sub = Vector.sub
     val (root,nt) = Robdd.nodetable r
     fun var i  = #1(nt sub i)
     fun low i  = #2(nt sub i) 
     fun high i = #3(nt sub i)
     fun name i =
      (case assoc2 (var i) pairs of
          SOME(str,_) => mk_var(str,Type.bool)
        | NONE        => ERR ("Node "^(int_to_string i)^" has no name") 
                                 "findAssign")
     fun findAssignment_aux r acc = 
          if r < 2 then acc
                   else if low r = 0 
                         then findAssignment_aux (high r) (name r :: acc)
                         else findAssignment_aux (low r) (mk_neg(name r) :: acc)
 in
  list_mk_conj(findAssignment_aux root [])
 end;
*)

(* This version (from Ken Larsen) is faster
fun findAssignment(var_map, bdd) = 
 let val pairs  = var_map_to_pairs var_map
     fun name i =
      (case assoc2 i pairs of
          SOME(str,_) => mk_var(str,Type.bool)
        | NONE        => ERR ("Node "^(int_to_string i)^" has no name") 
                                 "findAssign")
     fun findAssignment_aux bdd acc = 
          if (Robdd.equal bdd Robdd.TRUE) orelse (Robdd.equal bdd Robdd.FALSE)
           then acc
           else if Robdd.equal (Robdd.low bdd) Robdd.TRUE
                 then findAssignment_aux 
                       (Robdd.high bdd) 
                       (name(Robdd.var bdd) :: acc)
                 else findAssignment_aux 
                       (Robdd.low bdd) 
                       (mk_neg(name(Robdd.var bdd)) :: acc)
 in
  list_mk_conj(findAssignment_aux bdd [])
 end;
*)

fun findAssignment_aux bdd = 
 let fun aux_fun bdd acc = 
          if (Robdd.equal bdd Robdd.TRUE) orelse (Robdd.equal bdd Robdd.FALSE)
           then acc
           else if Robdd.equal (Robdd.low bdd) Robdd.TRUE
                 then aux_fun 
                       (Robdd.high bdd) 
                       (Robdd.ithvar(Robdd.var bdd) :: acc)
                 else aux_fun 
                       (Robdd.low bdd) 
                       (Robdd.nithvar(Robdd.var bdd) :: acc)
 in
  aux_fun bdd []
 end;

fun bdd_to_literal var_map bdd =
 let val i = Robdd.var bdd
     val v =
      (case assoc2 i (var_map_to_pairs var_map) of
          SOME(str,_) => mk_var(str,Type.bool)
        | NONE        => ERR ("Node "^(int_to_string i)^" has no name") 
                                 "findAssign")
 in
  if Robdd.equal (Robdd.high bdd) Robdd.TRUE andalso
     Robdd.equal (Robdd.low bdd)  Robdd.FALSE
   then v
   else
   if Robdd.equal (Robdd.high bdd) Robdd.FALSE andalso
      Robdd.equal (Robdd.low bdd)  Robdd.TRUE
    then mk_neg v
    else ERR "Non literal" "bdd_to_literal"
 end;

fun findAssignment(var_map, bdd) = 
 list_mk_conj(map (bdd_to_literal var_map) (findAssignment_aux bdd));


(*****************************************************************************)
(* Find an assignment that makes a term F in current BDD state               *)
(* (previously called findAss)                                               *)
(*****************************************************************************)

fun find_refutation tm = 
 let val bdd             = term_to_bdd tm     (* sequencing important here! *)
     val ((_,var_map),_) = !bdd_state
 in
  findAssignment(var_map,bdd)
 end;


(*****************************************************************************)
(* Find a BDD (representing a conjunction of literals) that satisfies        *)
(* a given satisfiable BDD                                                   *)
(*****************************************************************************)

(* Reverse order; doesn't find same mode for arbiter example

fun find_bdd_model bdd = 
 if Robdd.equal bdd Robdd.TRUE
  then SOME Robdd.TRUE
  else
   if Robdd.equal bdd Robdd.FALSE
    then NONE
    else
     case find_bdd_model (Robdd.high bdd) of
        SOME bdd' => SOME(Robdd.AND(Robdd.ithvar(Robdd.var bdd),bdd'))
      | NONE      => case find_bdd_model (Robdd.low bdd) of
                        SOME bdd' => SOME(Robdd.AND(Robdd.nithvar(Robdd.var bdd),bdd'))
                      | NONE      => NONE;
*)

fun find_bdd_model_aux bdd acc = 
 if Robdd.equal bdd Robdd.TRUE
  then SOME acc
  else
   if Robdd.equal bdd Robdd.FALSE
    then NONE
    else
     case find_bdd_model_aux (Robdd.low bdd) acc of
        SOME bddl => SOME(Robdd.nithvar(Robdd.var bdd)::bddl)
      | NONE      => case find_bdd_model_aux (Robdd.high bdd) acc of
                        SOME bddl => SOME(Robdd.ithvar(Robdd.var bdd)::bddl)
                      | NONE      => NONE;

fun  find_bdd_model bdd =  
 case find_bdd_model_aux bdd [] of
    SOME bddl => SOME(foldr Robdd.AND Robdd.TRUE bddl)
  | NONE      => NONE;

fun find_model tm = 
 let val bdd             = term_to_bdd tm     (* sequencing important here! *)
     val ((_,var_map),_) = !bdd_state
 in
  case find_bdd_model_aux bdd [] of
     SOME []   => T
   | SOME bddl => list_mk_conj(map (bdd_to_literal var_map) bddl)
   | NONE      => ERR "Can't find model" "find_model"
 end;

(*****************************************************************************)
(* Find a BDD (conjunction of literals) that refutes a non-tautology         *)
(*****************************************************************************)

fun find_bdd_refutation bdd = 
 if Robdd.equal bdd Robdd.TRUE
  then NONE
  else
   if Robdd.equal bdd Robdd.FALSE
    then SOME Robdd.TRUE
    else
     if Robdd.equal (Robdd.high bdd) Robdd.FALSE
      then SOME(Robdd.ithvar(Robdd.var bdd))
      else
       if Robdd.equal (Robdd.low bdd) Robdd.FALSE
        then SOME(Robdd.nithvar(Robdd.var bdd))
        else
         case find_bdd_refutation (Robdd.high bdd) of
            SOME bdd' => SOME(Robdd.AND(Robdd.ithvar(Robdd.var bdd),bdd'))
          | NONE      => case find_bdd_refutation (Robdd.low bdd) of
                            SOME bdd' => SOME
                                          (Robdd.AND
                                            (Robdd.nithvar(Robdd.var bdd),
                                           bdd'))
                          | NONE      => NONE;


(*****************************************************************************)
(* Get the name of a BDD node using the current BDD state                    *)
(*****************************************************************************)

fun get_node_name n =
 (case assoc2 n (var_map_to_pairs(snd(fst(!bdd_state)))) of
     SOME(str,_) => str
   | NONE        => ERR ("Node "^(int_to_string n)^" has no name") 
                            "get_node_name");

(*****************************************************************************)
(* Convert a BDD to a conditional term using the current BDD state           *)
(*****************************************************************************)

(* Old version
fun bdd_to_cond bdd = 
 let infix 9 sub 
     val op sub = Vector.sub
     val (root,nt) = Robdd.nodetable bdd
     fun var i  = Psyntax.mk_var(get_node_name(#1(nt sub i)),Type.bool)
     fun low i  = #2(nt sub i) 
     fun high i = #3(nt sub i)
     fun bdd_to_cond_aux node = 
           if node=0 then T
      else if node=1 then F 
                     else Psyntax.mk_cond
                           (var node, 
                            bdd_to_cond_aux(high node), 
                            bdd_to_cond_aux(low node))
 in
  bdd_to_cond_aux root
 end;
*)

fun bdd_to_cond bdd =
 if (Robdd.equal bdd Robdd.TRUE)
  then T
  else
   if (Robdd.equal bdd Robdd.FALSE)
    then F
    else Psyntax.mk_cond(mk_var(get_node_name(Robdd.var bdd),bool),
                         bdd_to_cond(Robdd.high bdd),
                         bdd_to_cond(Robdd.low bdd));

(*****************************************************************************)
(* Count number of nodes in a BDD                                            *)
(*****************************************************************************)

fun NodeCount bdd = 
 if (Robdd.equal bdd Robdd.TRUE) orelse (Robdd.equal bdd Robdd.FALSE)
  then 1
  else NodeCount(Robdd.high bdd) + NodeCount(Robdd.low bdd);


(*****************************************************************************)
(*****************************************************************************)
(* Various functions for printing BDDs into dot files and                    *)
(* postscript files.                                                         *)
(*****************************************************************************)
(*****************************************************************************)


(*****************************************************************************)
(* Create a dictionary for the variables of a term:                          *)
(*                                                                           *)
(*    term_to_var_map ["x0",...,"xm"] t                                      *)
(*                                                                           *)
(* creates a dictionary based on the order ["x0",...,"xm",...,"xn"],         *)
(* where the variables after "xm" are the variables in t (in the             *)
(* reverse order to that found by all_vars, i.e. occurrence order)           *)
(*****************************************************************************)

fun term_to_var_map l tm = (* No longer used *)
 list_to_var_map(l@rev(subtract(List.map(fst o dest_var)(all_vars tm))l));
     
(*****************************************************************************)
(* Create a sed script for editing a dot file so that BBD nodes              *)
(* are labelled with variable names rather than numbers                      *)
(*****************************************************************************)

fun var_map_to_sed_script file var_map_pairs =
 let val out = BasicIO.open_out file
 in
 (List.map 
  (fn (s,n) => 
    BasicIO.output
     (out,
      "s/\\\""^(makestring n)^"\\/"^(makestring n)^"\\\"/\\\""^s^"\\\"/g\n"
     ))
  var_map_pairs;
 BasicIO.close_out out)
 end;

(*****************************************************************************)
(* Print a BDD to <file>.dot and convert it to <file>.ps; return the bdd     *)
(*****************************************************************************)

fun showBDD file label bdd = 
 let val glab  = ("label=\""^label^"\"");
     val gsize = "size=\"7.5,8\""
 in
   Robdd.fnprintdot (file^".dot") bdd;
   Process.system
     ("dot -G"^glab^" -G"^gsize^" -Tps "^file^".dot -o "^file^".ps");
   bdd
 end;


(*****************************************************************************)
(* Convert a term to a BDD                                                   *)
(* using a supplied label and variable dictionary;                           *)
(* print the result into <file>.dot;                                         *)
(* make a sed script to replace node numbers with variable names;            *)
(* execute the sed script to create edited_<file>.dot;                       *)
(* run:                                                                      *)
(*  dot -Glabel="label" -Gsize="7.5,10" -Tps edited_<file>.dot -o <file>.ps  *)
(* return the bdd and the variable name-to-number mapping                    *)
(*****************************************************************************)

fun showBDDofTerm file label var_map bdd_map tm = 
 let val bdd   = fromTerm var_map bdd_map tm;
     val pairs = var_map_to_pairs var_map;
     val glab  = ("label=\""^label^"\"");
     val gsize = "size=\"7.5,8\""
     open Process
 in
   Robdd.fnprintdot (file^".dot") bdd;
   var_map_to_sed_script(file^"_sed_edits")pairs;
   system("sed -f "^file^"_sed_edits "^file^".dot > edited_"^file^".dot");
   system("dot -G"^glab^" -G"^gsize^" -Tps edited_"^file^".dot -o "^file^".ps");
   (bdd,pairs)
 end;


(*****************************************************************************)
(* Print a BDD state ((c,var_map),bdd_map) into a directory dir.             *)
(*                                                                           *)
(* Each entry in bdd_map is printed as separate files in dir with names      *)
(* derived from the head constant of the descriptor.                         *)
(*                                                                           *)
(* A file ghostview.script is written to dir for starting ghostview          *)
(* on all the .ps files generated.                                           *)
(*                                                                           *)
(*****************************************************************************)

fun print_bdd_state dir ((_:int,var_map),bdd_map) =
 let val (htbl,_)   = bdd_map
     val htbl_list  = Polyhash.listItems htbl
     val _          = Process.system ("mkdir "^dir)
     val out        = BasicIO.open_out (dir^"/ghostview.script")
 in
  List.map
   (fn (descr,bdd) => 
      let val name  = fst(Psyntax.dest_const(fst(Dsyntax.strip_comb descr)))
          val file  = dir^"/"^name
          val label = term_to_string descr
          val pairs = var_map_to_pairs var_map;
          val glab  = ("label=\""^label^"\"");
          val gsize = "size=\"7.5,8\""
      in
       Robdd.fnprintdot (file^".dot") bdd;
       var_map_to_sed_script(file^".sed_edits")pairs;
       Process.system
        ("sed -f "^file^".sed_edits "^file^".dot > "^file^".edited.dot");
       Process.system
        ("dot -G"^glab^" -G"^gsize^" -Tps "^file^".edited.dot -o "^file^".ps");
       BasicIO.output(out, "ghostview "^name^".ps&\n")
      end)
   htbl_list;
  BasicIO.close_out out;
  Process.system("chmod a+x "^dir^"/ghostview.script");
  htbl_list
 end;

(*****************************************************************************)
(* Default directory for BDD dot files etc                                   *)
(*****************************************************************************)

val default_dot_dir = ref "scratch_dot";

(*****************************************************************************)
(* Print BDD state into default directory for BDD dot files                  *)
(*****************************************************************************)

fun print_state() = 
 print_bdd_state (!default_dot_dir) (!bdd_state);

(*****************************************************************************)
(* Use "scratchBDD" as the default filename                                  *)
(*****************************************************************************)

fun showTerm tm = 
 let val (tab,bdd_map) = !bdd_state
     val (_,var_map')  = add_vars_to_table tab (all_vars tm)
 in
  showBDDofTerm "scratchBDD" (term_to_string tm) var_map' bdd_map tm
 end;


end;

