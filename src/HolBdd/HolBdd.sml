
(*****************************************************************************)
(* HolBdd.sml                                                                *)
(* ----------                                                                *)
(*                                                                           *)
(* Ken Larsen's BDDOracle package opened up, renamed  and modified           *)
(* to support BDDs listed in a table of the form:                            *)
(*                                                                           *)
(*    [...,(<term>, <bdd>),...]                                              *)
(*                                                                           *)
(* The original package uses the type:                                       *)
(*                                                                           *)
(*     type mapping = (string, bdd.varnum) Binarymap.dict                    *)
(*                                                                           *)
(* this is renamed to:                                                       *)
(*                                                                           *)
(*     type var_map = (string, bdd.varnum) Binarymap.dict                    *)
(*                                                                           *)
(* ML interface to BuDDy package (MuDDy): http://www.itu.dk/research/muddy/  *)
(*                                                                           *)
(*****************************************************************************)

(*
structure HolBdd :> HolBdd = struct
*)

(*
map load ["bdd",
          "Binarymap",
          "Net",
          "Polyhash",
          "Psyntax",
          "Rsyntax",
          "pairLib",
          "unwindLib"];
*)

local

open Globals HolKernel Parse boolLib bdd;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

in

open bdd;

(* See pp_flags *)

(* stack_infixes has gone away, and been replaced by something more
   general  (it's possible that something similar might be reinstated
   eventually, but this was certainly not doing what it used to anyway).  

val _ = stack_infixes := false; 
val _ = infix_at_front := true;
*)

(* val term_to_string = Parse.term_to_string; *)

open Psyntax;

(*---------------------------------------------------------------------------*
 * General purpose conversionals. [from Konrad Slind]                        *
 *---------------------------------------------------------------------------*)

local open Rsyntax
in

fun FORK_CONV (conv1,conv2) tm =
    let val {Rator,Rand=r} = dest_comb tm
        val {Rator,Rand=l} = dest_comb Rator
    in
     MK_COMB(AP_TERM Rator (conv1 l), conv2 r)
    end;

fun BINOP_CONV conv tm = FORK_CONV (conv,conv) tm;
fun QUANT_CONV conv    = RAND_CONV(ABS_CONV conv);
fun BINDER_CONV conv   = ABS_CONV conv ORELSEC QUANT_CONV conv;

end;

local val alpha = mk_vartype "'a"
      val spotBeta = FORK_CONV (QUANT_CONV (BINOP_CONV BETA_CONV),
                                BINOP_CONV (QUANT_CONV BETA_CONV))
      open boolTheory
      val thm0 = SPEC_ALL EXISTS_OR_THM
in
fun EX_OR_CONV tm = 
  let open Rsyntax
      val {Bvar,Body} = dest_exists tm
      val ty = type_of Bvar --> Type.bool
      val P = mk_var{Name="P", Ty=ty}
      val Q = mk_var{Name="Q", Ty=ty}
      val {disj1,disj2} = dest_disj Body
      val lamP = mk_abs{Bvar=Bvar, Body=disj1}
      val lamQ = mk_abs{Bvar=Bvar, Body=disj2}
      val thm = CONV_RULE (RAND_CONV (BINOP_CONV (GEN_ALPHA_CONV Bvar)))
                          (INST_TYPE [alpha |-> type_of Bvar] thm0)
  in 
    CONV_RULE spotBeta (INST [P |-> lamP, Q |-> lamQ] thm)
  end
end;

fun TERNOP_CONV cnv = 
 RAND_CONV cnv THENC RATOR_CONV(RAND_CONV cnv THENC RATOR_CONV(RAND_CONV cnv));

val T = ``T``
and F = ``F``;

fun mk_conj1(t1,t2) =
 if t1 = T 
  then t2
  else 
  if t2 = T 
   then t1
   else 
   if t1 = F orelse t2 = F then F else Psyntax.mk_conj(t1,t2);

fun mk_disj1(t1,t2) =
 if t1 = F 
  then t2
  else 
  if t2 = F 
   then t1
   else 
   if t1 = T orelse t2 = T then T else Psyntax.mk_disj(t1,t2);

exception Error;

fun error () = raise Error;

fun hol_err msg func = 
 (print "HolBdd: hol_err \""; print msg; 
  print "\" \""; print func; print "\"\n";
  raise mk_HOL_ERR "HolBdd" func msg);

val HolBddTag = Tag.read "BuDDy";

(* Should var_map be a hash table? *)

type var_map = (string, int) Binarymap.dict;

(*****************************************************************************)
(* Create an empty (string,int)dict                                          *)
(*****************************************************************************)

val empty_var_map = 
 Binarymap.mkDict String.compare : (string, int) Binarymap.dict;

type table = int * var_map;

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
(*     (Term.term, bdd.bdd)Polyhash.hash_table * (Term.term)Net.net          *)
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
 (Term.term, bdd.bdd)Polyhash.hash_table * (Term.term)Net.net;

val PolyTableSizeHint = ref 1000;

val current_bdd_map:bdd_map = 
 (Polyhash.mkPolyTable
  (!PolyTableSizeHint,
    mk_HOL_ERR "BDDOracle" "Polyhash.find" "Hash table lookup failure"),
  Net.empty);
        
fun lookup_var var_map name =
 case peek_map var_map name of
    SOME i => bdd.ithvar i
  | NONE   => hol_err ("The variable "^name^" is not in the mapping") "var";

(*****************************************************************************)
(* Check that a term substitution [(new1,old1),...,(newn,oldn)]              *)
(* is 1-1, i.e. new1,...,newn are distinct                                   *)
(* and that all the variables are boolean,                                   *)
(* return a list of [(oldname1,newname1),...,(oldnamen,newnamen)]            *)
(*****************************************************************************)

exception match_to_pairs_Failure;

fun match_to_pairs []             = []
 |  match_to_pairs ({redex=old,residue=new}::l) =
     if not(exists (fn {residue=new',...} => new=new') l) 
         andalso (type_of new = bool) 
         andalso is_var new
         andalso (type_of old = bool) 
         andalso is_var old
      then (fst(dest_var old),fst(dest_var new))::match_to_pairs l
      else raise match_to_pairs_Failure;

(*****************************************************************************)
(*    subst_bdd tab [(oldname1,newname1),...,(oldnamen,newnamen)] bdd        *)
(*                                                                           *)
(* gives result of substituting newnamei for oldnamei (1<=i<=n) in bdd       *)
(*****************************************************************************)

fun subst_bdd var_map old_new_list bdd =
 let val v2i = var_to_int var_map
 in
  bdd.replace bdd (bdd.makepairSet(List.map (v2i ## v2i) old_new_list))
 end;

(*****************************************************************************)
(* Scan a list of keys in normal order to find the first                     *)
(* one with an entry in a hashtable. Return key-data pair.                   *)
(*****************************************************************************)

fun find_data msg htbl []      = hol_err msg "find_data"
 |  find_data msg htbl (k::kl) = (case Polyhash.peek htbl k of
                                     SOME data => (k,data)
                                   | NONE      => find_data msg htbl kl);

(*****************************************************************************)
(* Looks up a term in a net. Returns NONE if no match in net found.          *)
(* If a match is found then a renaming of the corresponding BDD in the       *)
(* hash table is attempted.                                                  *)
(*****************************************************************************)

fun NetPeek var_map (htbl,net) tm =
 let val netl = Net.match tm net
 in
  if null netl
   then NONE
   else
   let val (descr,bdd) =
        find_data 
         "Unhashed application"
         htbl 
         netl (*       (rev netl)    *)
   in
    SOME
     (subst_bdd var_map (match_to_pairs(fst(match_term descr tm))) bdd)
   end
 end;

(*****************************************************************************)
(* Predicate to test whether a term is a suitable body for bdd.appex or      *)
(* bdd.appall.  Currently just tests for t1 /\ t2 or t1 \/ t2                *)
(* or t1 ==> t2.                                                             *)
(*****************************************************************************)

fun appQuantTest tm =
 is_conj tm orelse is_disj tm orelse is_imp tm;

(*****************************************************************************)
(* Flatten a varstruct term into a list of variables.                        *)
(*****************************************************************************)

fun flatten_pair t =
if is_var t 
 then [t] 
 else foldr (fn(t,l) => (flatten_pair t) @ l) [] (pairSyntax.strip_pair t);


(*****************************************************************************)
(* ?v1...vn. t                     --> ([v1,...,vn],t)                       *)
(* ?(v1,...,vn). t                 --> ([v1,...,vn],t)                       *)
(* ?(v1,...,(u1,...,um),...,vn). t --> ([v1,...,u1,...,um,...,vn],t)         *)
(*****************************************************************************)

fun gen_strip_exists t =
 let val (vs,bdy) =  pairSyntax.strip_pexists t
 in
  (foldr (fn (p,l) => flatten_pair p @ l) [] vs, bdy)
 end

(*****************************************************************************)
(* !v1...vn. t                     --> ([v1,...,vn],t)                       *)
(* !(v1,...,vn). t                 --> ([v1,...,vn],t)                       *)
(* !(v1,...,(u1,...,um),...,vn). t --> ([v1,...,u1,...,um,...,vn],t)         *)
(*****************************************************************************)

fun gen_strip_forall t =
 let val (vs,bdy) =  pairSyntax.strip_pforall t
 in
  (foldr (fn (p,l) => flatten_pair p @ l) [] vs, bdy)
 end

(*****************************************************************************)
(* Timings:                                                                  *)
(*                                                                           *)
(* Old version:                                                              *)
(* time termToBdd (rhs(concl nextstate_rel_eqn));                            *)
(* runtime: 0.030s,    gctime: 0.000s,     systime: 0.000s.                  *)
(* > val it = <bdd> : bdd.bdd                                                *)
(*                                                                           *)
(* New version:                                                              *)
(* time termToBdd (rhs(concl nextstate_rel_eqn));                            *)
(* runtime: 0.350s,    gctime: 0.000s,     systime: 0.000s.                  *)
(* > val it = <bdd> : bdd.bdd                                                *)
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
           let val (Name,Ty) = Term.dest_var tm
           in  
               if Ty = Type.bool then lookup_var var_map Name
               else hol_err ("Variable "^Name^" is not of type bool") "fromTerm"
           end 
       else
           let val (comb,args) = strip_comb tm
           in
            if Term.is_abs comb then combExp var_map (htbl,net) comb args else 
            case fst(Psyntax.dest_const comb) of
                "/\\"  => binExp var_map (htbl,net) bdd.And args
              | "\\/"  => binExp var_map (htbl,net) bdd.Or args
              | "==>"  => binExp var_map (htbl,net) bdd.Imp args
              | "="    => (case args of
                            [arg1,arg2]
                            =>
                             if Term.is_var arg1 andalso Term.is_var arg2
                              then binExp var_map (htbl,net) bdd.Biimp args
                              else 
                               (ListPair.foldl
                                 (fn(x1,x2,bdd)=> 
                                   bdd.AND
                                    (binExp var_map (htbl,net) bdd.Biimp [x1,x2],
                                     bdd))
                                 bdd.TRUE
                                 (pairSyntax.strip_pair arg1,pairSyntax.strip_pair arg2)
                                 handle Interrupt 
                                         => raise Interrupt
                                   |    match_to_pairs_Failure
                                         => raise match_to_pairs_Failure
                                   |  _  => (print "Can't make BDD of: ";
                                             print_term tm;
                                             print "\n";
                                             hol_err 
                                             "Can't make BDD of equation"
                                             "fromTerm"))
                        | _ => error())
              | "~"    => bdd.NOT(fromTerm_aux var_map (htbl,net) (List.hd args))
              | "T"    => bdd.TRUE
              | "F"    => bdd.FALSE
              | "!"    => quantExp var_map (htbl,net) gen_strip_forall 
                                   bdd.forall bdd.appall tm
              | "?"    => quantExp var_map (htbl,net) gen_strip_exists 
                                   bdd.exist bdd.appex   tm
              | "COND" => condExp var_map (htbl,net) args
              | _      => (print "Can't make BDD of: ";
                           print_term tm;
                           print "\n";
                           hol_err ("Can't make BDD from "^(fst(Psyntax.dest_const comb))) 
                                   "fromTerm_aux")
           end

(* check v in bdy, if so get BDD of bdy (will guarantee v in var_map)
   then (using new map) get number of v, compute BDD of arg,
   do call compose (BDD bdy) (BDD arg) (numb of v), if v not in bdy
   then return BDD bdy
*)
and combExp var_map bdd_map comb args =  
    let val (v,bdy) = Psyntax.dest_abs comb
        val [arg]   = args
    in
     if free_in v bdy
      then compose 
           (valOf(Binarymap.peek(var_map, fst(Psyntax.dest_var v))),
            (fromTerm_aux var_map bdd_map arg))
            (fromTerm_aux var_map bdd_map bdy)
      else fromTerm_aux var_map bdd_map bdy
    end
  | combExp _ _ _ _ = error()

and binExp var_map bdd_map opr [t1,t2] = 
    let val e1 = fromTerm_aux var_map bdd_map t1
        val e2 = fromTerm_aux var_map bdd_map t2
    in  bdd.apply e1 e2 opr
    end
  | binExp _ _ _ _ = error() (* impossible *)
    
and quantExp var_map bdd_map strip quant appquant t =
    let val (vars,body) = strip t
        fun find v = 
            case peek_map var_map (fst(Term.dest_var v)) of
                SOME i => i
              | NONE   => hol_err ("The variable "^
                                   (fst(Term.dest_var v))^
                                   " is not in the mapping")
                                  "quantExp"
        val varset = bdd.makeset (List.map find vars)
        val tmfn   = fromTerm_aux var_map bdd_map
    in  
     if is_conj body
      then 
       let val (tm1,tm2) = dest_conj body 
       in appquant (tmfn tm1) (tmfn tm2) And varset end
     else if is_disj body
      then 
       let val (tm1,tm2) = dest_disj body 
       in appquant (tmfn tm1) (tmfn tm2) Or varset end
     else if is_imp body
      then 
       let val (tm1,tm2) = dest_imp body 
       in appquant (tmfn tm1) (tmfn tm2) Imp varset end
     else if is_eq body andalso (Term.type_of(Term.rand body) = Type.bool)
      then 
       let val (tm1,tm2) = dest_eq body 
       in appquant (tmfn tm1) (tmfn tm2) Biimp varset end
     else quant varset (tmfn body)
    end

and condExp var_map bdd_map [x,y,z] = 
    let val x' = fromTerm_aux var_map bdd_map x
        val y' = fromTerm_aux var_map bdd_map y
        val z' = fromTerm_aux var_map bdd_map z
    in
        bdd.OR(bdd.AND(x',y'),bdd.AND(bdd.NOT x',z'))
    end
  | condExp _ _ _ = error();

fun fromTerm var_map bdd_map tm =
    let val _ = if bdd.getVarnum() < size var_map 
                 then bdd.setVarnum(size var_map)
                 else ()
    in 
       fromTerm_aux var_map bdd_map tm 
    end;

(*****************************************************************************)
(* Conversion from terms to BDDs that doesn't attempt any lookup             *)
(* in the BDD table                                                          *)
(*****************************************************************************)

fun pureFromTerm_aux var_map tm =
 if Term.is_var tm then 
     let val (Name,Ty) = dest_var tm
     in  
         if Ty = Type.bool then lookup_var var_map Name
         else hol_err ("Variable "^Name^" is not of type bool") "pureFromTerm"
     end 
 else
     let val (comb,args) = strip_comb tm
         val (Name, Ty)  = dest_const comb
     in
      case Name of
          "/\\"  => pureBinExp var_map bdd.And args
        | "\\/"  => pureBinExp var_map bdd.Or args
        | "==>"  => pureBinExp var_map bdd.Imp args
        | "="    => (case args of
                      [arg1,arg2]
                      =>
                       if Term.is_var arg1 andalso Term.is_var arg2
                        then pureBinExp var_map bdd.Biimp args
                        else 
                         (ListPair.foldl
                           (fn(x1,x2,bdd)=> 
                             bdd.AND
                              (pureBinExp var_map bdd.Biimp [x1,x2],
                               bdd))
                           bdd.TRUE
                           (pairSyntax.strip_pair arg1,pairSyntax.strip_pair arg2)
                           handle Interrupt => raise Interrupt
                                       |  _ => hol_err 
                                                "Can't make BDD of equation"
                                                "pureFromTerm")
                  | _ => error())
        | "~"    => bdd.NOT(pureFromTerm_aux var_map (List.hd args))
        | "T"    => bdd.TRUE
        | "F"    => bdd.FALSE
        | "!"    => pureQuantExp var_map gen_strip_forall bdd.forall tm
        | "?"    => pureQuantExp var_map gen_strip_exists bdd.exist tm
        | "COND" => pureCondExp var_map args
        | _      => (print "Can't make BDD of: ";
                     print_term tm;
                     print "\n";
                     hol_err ("Can't make BDD from "^Name) "pureFromTerm_aux")
     end
   
and pureBinExp var_map opr [t1,t2] = 
    let val e1 = pureFromTerm_aux var_map t1
        val e2 = pureFromTerm_aux var_map t2
    in  bdd.apply e1 e2 opr
    end
  | pureBinExp _ _ _ = error() (* impossible *)
    
and pureQuantExp var_map strip quant t =
    let val (vars,body) = strip t
        fun find v = 
            case peek_map var_map (fst(Term.dest_var v)) of
                SOME i => i
              | NONE   => hol_err ("The variable "^
                                   (fst(Term.dest_var v))^
                                   " is not in the mapping")
                                  "pureQuantExp"
        val varset = bdd.makeset (List.map find vars)
        val ebody = pureFromTerm_aux var_map body
    in  
     quant varset ebody
    end

and pureCondExp var_map [x,y,z] = 
    let val x' = pureFromTerm_aux var_map x
        val y' = pureFromTerm_aux var_map y
        val z' = pureFromTerm_aux var_map z
    in
        bdd.OR(bdd.AND(x',y'),bdd.AND(bdd.NOT x',z'))
    end
  | pureCondExp _ _ = error();

fun pureFromTerm var_map tm =
    let val _ = if bdd.getVarnum() < size var_map 
                 then bdd.setVarnum(size var_map)
                 else ()
    in 
       pureFromTerm_aux var_map tm 
    end;


(*****************************************************************************)
(* BDD_CONV bdd_map tm --> |- tm = tm'                                       *)
(*                                                                           *)
(* where tm' is suitable for representing as a BDD using termToBdd.          *)
(*                                                                           *)
(* The bdd_map parameter is the part of the BDD state, needed to             *)
(* determine which terms are descriptors in the BDD hash table, and so       *)
(* need processing as illustrated below.                                     *)
(*                                                                           *)
(* bdd.replace can only replace distinct variables with distinct             *)
(* variables.  Thus, for example, if:                                        *)
(*                                                                           *)
(*    |- Foo (u, v, w, x, y, z) = (u \/ v) /\ w /\ (~x = ~y) /\ ~z           *)
(*                                                                           *)
(* then the BDD of ``Foo(a,b,p,q,p,(x/\y))`` is computed by                  *)
(* first transforming it (using BDD_CONV) to:                                *)
(*                                                                           *)
(*                                                                           *)
(* ?y' z.                     (* Note: y' and z are new             *)       *)
(*  ((y' = p)      /\         (* Note: ``p`` is repeated            *)       *)
(*   (z = x /\ y)) /\         (* Note: ``x /\ y`` is not a variable *)       *)
(*   Foo (a, b, p, q, y', z)                                                 *)
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
(* rlist are the bindings to be handled by bdd.replace.                      *)
(*****************************************************************************)

fun bdd_match_split []         acc = ([],[])
 |  bdd_match_split ((b as {redex=v,residue=e})::l) acc = 
     if not(is_var e) orelse mem e acc                         (* ?-quant    *)
      then let val (qlist,rlist) = bdd_match_split l acc
           in (b::qlist, rlist)
           end
      else let val (qlist,rlist) = bdd_match_split l (e::acc)  (* subst      *)
           in (qlist, b::rlist)
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
           let val (comb,args) = strip_comb tm
               val (Name, Ty)  = dest_const comb
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
 let val netl = Net.match tm net
 in
  if null netl
   then NONE
   else
   let val (descr,bdd) =
        find_data 
         "Unhashed application"
         htbl 
         netl
(*       (rev netl)    *)
   in
    SOME (BDD_MATCH_CONV (htbl,net) descr tm)
   end
 end

and BDD_MATCH_CONV bdd_map descr tm =
 let val (mlist,tysubst) = match_term descr tm
     val _ = if null tysubst then () else hol_err "Bad match" "bdd_match"
     val vars  = U(List.map (all_vars o #residue) mlist)
     val (qlist,rlist)  = bdd_match_split mlist (free_vars descr)
     val (qvars,rlist',qconj)  = 
          foldr (fn ({redex=v,residue=e},(vl,sl,tm)) => 
                    let val v' = variant vars v
                    in
                     (v'::vl,
                        (if v=v' then sl else {redex=v,residue=v'}::sl),
                      mk_conj1(mk_eq(v',e),tm))
                     end)
                ([],[],T)
                qlist
 in
  if null qvars
   then ALL_CONV tm
   else
   let val qtm = 
        list_mk_exists(qvars ,mk_conj1(qconj, subst (rlist@rlist') descr))
       val th1 = SYM(unwindLib.EXPAND_AUTO_CONV [] qtm)
       val th2 = unwindLib.DEPTH_EXISTS_CONV 
                  (RATOR_CONV(RAND_CONV(BDD_CONV bdd_map))) 
                  qtm
       val th3 = TRANS th1 th2
   in
    if tm = lhs(concl th3) then th3 else hol_err "unwind error" "bdd_match"
   end
 end;


(*****************************************************************************)
(* Transform a term to one that can be represented as a BDD                  *)
(*****************************************************************************)

val BDD_CONV_flag = ref false;

fun BDD_TR bdd_map tm = 
 let val th = BDD_CONV bdd_map tm;
     val tm = rhs(concl th)
 in
  if !BDD_CONV_flag 
   then (print "BDD_CONV ";print_thm th; print "\n"; tm) 
   else tm
 end;

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

(* Old version for labels with n/n
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
*)

fun var_map_to_sed_script file var_map_pairs =
 let val out = BasicIO.open_out file
 in
 (List.map 
  (fn (s,n) => 
    BasicIO.output
     (out,
      "s/\\\""^(makestring n)^"\\\"/\\\""^s^"\\\"/g\n"
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
 (bdd.fnprintdot (file^".dot") bdd;
  Process.system("dot -G"^glab^" -G"^gsize^" -Tps "^file^".dot -o "^file^".ps");
  bdd)
 end;


(*****************************************************************************)
(* Convert a term to a BDD                                                   *)
(* using a supplied label and variable dictionary;                           *)
(* print the result into <file>.dot;                                         *)
(* make a sed script to replace node numbers with variable names;            *)
(* execute the sed script to create edited_<file>.dot;                       *)
(* run:                                                                      *)
(*  dot -Glabel="label" -Gsize="7.5,10" -Tps edited_<file>.dot -o <file>.ps  *)
(* delete dot, sed edits and and edited dot files                            *)
(* return the bdd and the variable name-to-number mapping                    *)
(*****************************************************************************)

fun showBDDofTerm file label var_map bdd_map tm = 
 let val bdd   = fromTerm var_map bdd_map tm;
     val pairs = var_map_to_pairs var_map;
     val glab  = ("label=\""^label^"\"");
     val gsize = "size=\"7.5,8\""
 in
 (bdd.fnprintdot (file^".dot") bdd;
  var_map_to_sed_script(file^"_sed_edits")pairs;
  Process.system("sed -f "^file^"_sed_edits "^file^".dot > edited_"^file^".dot");
  Process.system("dot -G"^glab^" -G"^gsize^" -Tps edited_"^file^".dot -o "^file^".ps");
  Process.system("rm "^file^".dot");
  Process.system("rm "^file^"_sed_edits");
  Process.system("rm edited_"^file^".dot");
  (bdd,pairs))
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
      let val name  = fst(Psyntax.dest_const(fst(strip_comb descr)))
          val file  = dir^"/"^name
          val label = Parse.term_to_string descr
          val pairs = var_map_to_pairs var_map;
          val glab  = ("label=\""^label^"\"");
          val gsize = "size=\"7.5,8\""
      in
       bdd.fnprintdot (file^".dot") bdd;
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
(* Get the BuDDy variable number corresponding to a HOL variable             *)
(*****************************************************************************)

fun varToBddVar (var_map:(string, int) Binarymap.dict) v = 
 case Binarymap.peek(var_map, fst(Term.dest_var v)) of
     SOME i => i
   | NONE   => hol_err ("The variable "^
                        (fst(Term.dest_var v))^
                        " is not in the mapping")
                       "varToBddVar";

(*****************************************************************************)
(* Show var_map and bdd_map                                                  *)
(*****************************************************************************)

fun showVarMap() = var_map_to_pairs(snd(fst(!bdd_state)));

fun showBddMap() = Polyhash.listItems(fst(snd(!bdd_state)));

(*****************************************************************************)
(* Get variable order in current state                                       *)
(*****************************************************************************)

fun showVarOrd() = map fst (sort (fn(_,m)=>fn(_,n)=>m<n) (showVarMap()));

(*****************************************************************************)
(* Set BDD state to have an empty BDD hash table and variable table          *)
(* with a given variable ordering                                            *)
(*****************************************************************************)

fun initHolBdd var_order =
 let val (_,(htbl,net)) = !bdd_state
 in
  (map (fn(tm,_) => Polyhash.remove htbl tm) (Polyhash.listItems htbl);
   bdd_state := (add_names_to_table empty_table var_order,(htbl,Net.empty));
   let val var_count = length(showVarMap())
   in 
    if getVarnum() < var_count then setVarnum var_count else () 
   end)
 end;

(*****************************************************************************)
(* Delete a BDD from the BDD hash table                                      *)
(*****************************************************************************)

val deleteBdd = Polyhash.remove(fst(snd(!bdd_state)));

(*****************************************************************************)
(* Flag (default true) to determine whether to delete BDDs                   *)
(*****************************************************************************)

val deleteBdd_flag = ref false;

(*****************************************************************************)
(* Convert a term to a BDD in current BDD state, adding any new variables    *)
(* to the state's var_map, if necessary.                                     *)
(*****************************************************************************)

exception termToBddError;

fun termToBdd tm =
 (let val (tab,bdd_map) = !bdd_state
      val (c',var_map') = add_vars_to_table tab (all_vars tm)
      val _             = bdd_state := ((c', var_map'), bdd_map)
  in
   fromTerm var_map' bdd_map tm
    handle Interrupt 
             => raise Interrupt
      |    match_to_pairs_Failure 
             => let val tm' = BDD_TR bdd_map tm
                    val (c'',var_map'') = add_vars_to_table 
                                           (c', var_map')
                                           (all_vars tm')
                in
                 bdd_state := ((c'', var_map''), snd(!bdd_state));
                 fromTerm var_map'' bdd_map tm'
                end
      |    _ => raise termToBddError
  end) handle Interrupt => raise Interrupt
         |    _         => raise termToBddError ;

(*****************************************************************************)
(* Version not using BDD table                                               *)
(*****************************************************************************)

exception pureTermToBddError;

fun pureTermToBdd tm =
 (let val (tab,bdd_map) = !bdd_state
      val (c',var_map') = add_vars_to_table tab (all_vars tm)
      val _             = bdd_state := ((c', var_map'), bdd_map)
  in
   pureFromTerm var_map' tm
  end) handle Interrupt => raise Interrupt
         |    _         => raise termToBddError ;

(*****************************************************************************)
(* Add a variable to the BDD state, returning the node number. If the        *)
(* variable already exists, then BDD state is unchanged and the variable's   *)
(* existing number is returned                                               *)
(*****************************************************************************)

fun add_var s = bdd.var(termToBdd(mk_var(s,bool)));

(*****************************************************************************)
(* Add a definition of a constant to a net of BDDs (bdd_map),                *)
(* if necessary first extending the variable table                           *)
(*                                                                           *)
(* First add variables in defn to tab, then compute BDD of RHS of defn,      *)
(* and add (descriptor,bdd) to bdd_map.                                      *)
(*                                                                           *)
(*****************************************************************************)

fun add_definition defn (tab,bdd_map) 
    : ((Term.term * bdd.bdd) * (table * bdd_map)) =
 let val defn_tm       = concl defn
     val (_,eqn)       = strip_forall defn_tm
     val (tm_descr,tm) = dest_eq eqn
     val (c',var_map') = add_vars_to_table tab (all_vars tm)
     val _             = bdd_state := ((c', var_map'), bdd_map)
     val tm_bdd        = fromTerm var_map' bdd_map tm
                           handle Interrupt => raise Interrupt
                                     |    _ => let val tm' = BDD_TR bdd_map tm
                                                   val (c'',var_map'') =
                                                    add_vars_to_table 
                                                     (c', var_map')
                                                     (all_vars tm')
                                               in
                                                bdd_state := 
                                                 ((c'', var_map''), 
                                                  snd(!bdd_state));
                                                fromTerm var_map'' bdd_map tm'
                                               end
     val (htbl,net)    = bdd_map
     val bdd_map'      = ((Polyhash.insert htbl (tm_descr,tm_bdd);htbl),
                          Net.insert(tm_descr,tm_descr)net)
 in
  ((tm_descr,tm_bdd),((c',var_map'), bdd_map'))
 end;

(*****************************************************************************)
(* Add a definition to BDD state                                             *)
(*****************************************************************************)

fun addEquation th =
 let val ((tm,bdd),bdd_state') = add_definition th (!bdd_state)
 in
  bdd_state := bdd_state'; (tm,bdd)
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
  showBDDofTerm "scratchBDD" "" var_map' bdd_map tm; ()
 end;

fun termToBddDiagram filename lab tm = 
 let val (tab,bdd_map) = !bdd_state
     val (_,var_map')  = add_vars_to_table tab (all_vars tm)
 in
  showBDDofTerm filename lab var_map' bdd_map tm
 end;

(*****************************************************************************)
(* Test whether is BDD is a tautology                                        *)
(*****************************************************************************)

fun is_taut bdd =
 (bdd.toBool bdd = true)
 handle Domain => false 
      | Error  => false;

(*****************************************************************************)
(* Versions of Ken Larsen's oracle functions that                            *)
(* use the BDD state                                                         *)
(*****************************************************************************)

(* Old code
fun tautCheck tm =
 let val (tab,bdd_map) = !bdd_state
     val (_,var_map')  = add_vars_to_table tab (all_vars tm)
 in 
  (SOME(bdd.toBool (fromTerm var_map' bdd_map tm)))
   handle Domain => NONE 
        | Error  => NONE
 end;
*)

fun tautCheck tm = 
 SOME(bdd.toBool(termToBdd tm)) handle Interrupt => raise Interrupt
                                  |    _         => NONE;

fun pureTautCheck tm = 
 SOME(bdd.toBool(pureTermToBdd tm)) handle Interrupt => raise Interrupt
                                      |    _         => NONE;


(*****************************************************************************)
(* Test whether a term corresponds to a true BDD -- true or false returned   *)
(*****************************************************************************)

fun isT tm =
 case tautCheck tm of
    SOME true => true
  | _         => false;

(*****************************************************************************)
(* Test whether a term corresponds to a false BDD -- true or false returned  *)
(*****************************************************************************)

fun isF tm =
 case tautCheck tm of
    SOME false => true
  | _          => false;

(*****************************************************************************)
(* Check Boolean equivalence of two terms                                    *)
(*****************************************************************************)

fun eqCheck(t1,t2) = isT(mk_eq(t1,t2));

fun mk_bdd_thm tm = 
 Thm.mk_oracle_thm 
  HolBddTag 
  ([], (if valOf (tautCheck tm) 
         then tm
         else mk_neg tm)
  handle Interrupt => raise Interrupt
               | _ => hol_err "Could not reduce term"
                              "mk_bdd_thm");

exception bddOracleError;

fun bddOracle tm = 
 Thm.mk_oracle_thm 
  HolBddTag 
  ([], (if valOf(tautCheck tm) 
         then tm
         else raise bddOracleError)
  handle Interrupt => raise Interrupt
               | _ => raise bddOracleError);

(*****************************************************************************)
(* Equivalence prover                                                        *)
(*****************************************************************************)

fun bddEqOracle(t1,t2) = bddOracle(mk_eq(t1,t2));

(*****************************************************************************)
(* BDD tactic                                                                *)
(*****************************************************************************)

fun BDD_TAC (asl:Term.term list,tm) =
 case tautCheck tm of
    SOME true => ([], fn [] => mk_bdd_thm tm | _ => error())
  | _         => hol_err "bddCkeck failed" "BDD_TAC"

(*****************************************************************************)
(* Finds an assignment that makes a term F                                   *)
(*****************************************************************************)

(* Old version
fun findAssignment(var_map, r) = 
 let val pairs  = var_map_to_pairs var_map
     infix 9 sub 
     val op sub = Vector.sub
     val (root,nt) = bdd.nodetable r
     fun var i  = #1(nt sub i)
     fun low i  = #2(nt sub i) 
     fun high i = #3(nt sub i)
     fun name i =
      (case assoc2 (var i) pairs of
          SOME(str,_) => mk_var(str,``:bool``)
        | NONE        => hol_err ("Node "^(int_to_string i)^" has no name") 
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
          SOME(str,_) => mk_var(str,``:bool``)
        | NONE        => hol_err ("Node "^(int_to_string i)^" has no name") 
                                 "findAssign")
     fun findAssignment_aux bdd acc = 
          if (bdd.equal bdd bdd.TRUE) orelse (bdd.equal bdd bdd.FALSE)
           then acc
           else if bdd.equal (bdd.low bdd) bdd.TRUE
                 then findAssignment_aux 
                       (bdd.high bdd) 
                       (name(bdd.var bdd) :: acc)
                 else findAssignment_aux 
                       (bdd.low bdd) 
                       (mk_neg(name(bdd.var bdd)) :: acc)
 in
  list_mk_conj(findAssignment_aux bdd [])
 end;
*)

fun findAssignment_aux bdd = 
 let fun aux_fun bdd acc = 
          if (bdd.equal bdd bdd.TRUE) orelse (bdd.equal bdd bdd.FALSE)
           then acc
           else if bdd.equal (bdd.low bdd) bdd.TRUE
                 then aux_fun 
                       (bdd.high bdd) 
                       (bdd.ithvar(bdd.var bdd) :: acc)
                 else aux_fun 
                       (bdd.low bdd) 
                       (bdd.nithvar(bdd.var bdd) :: acc)
 in
  aux_fun bdd []
 end;

fun bdd_to_literal var_map bdd =
 let val i = bdd.var bdd
     val v =
      (case assoc2 i (var_map_to_pairs var_map) of
          SOME(str,_) => mk_var(str,``:bool``)
        | NONE        => hol_err ("Node "^(int_to_string i)^" has no name") 
                                 "findAssign")
 in
  if bdd.equal (bdd.high bdd) bdd.TRUE andalso
     bdd.equal (bdd.low bdd)  bdd.FALSE
   then v
   else
   if bdd.equal (bdd.high bdd) bdd.FALSE andalso
      bdd.equal (bdd.low bdd)  bdd.TRUE
    then mk_neg v
    else hol_err "Non literal" "bdd_to_literal"
 end;

fun findAssignment(var_map, bdd) = 
 list_mk_conj(map (bdd_to_literal var_map) (findAssignment_aux bdd));


(*****************************************************************************)
(* Find an assignment that makes a term F in current BDD state               *)
(* (previously called findAss)                                               *)
(*****************************************************************************)

fun findRefutation tm = 
 let val bdd             = termToBdd tm     (* sequencing important here! *)
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
 if bdd.equal bdd bdd.TRUE
  then SOME bdd.TRUE
  else
   if bdd.equal bdd bdd.FALSE
    then NONE
    else
     case find_bdd_model (bdd.high bdd) of
        SOME bdd' => SOME(bdd.AND(bdd.ithvar(bdd.var bdd),bdd'))
      | NONE      => case find_bdd_model (bdd.low bdd) of
                        SOME bdd' => SOME(bdd.AND(bdd.nithvar(bdd.var bdd),bdd'))
                      | NONE      => NONE;
*)

fun find_bdd_model_aux bdd acc = 
 if bdd.equal bdd bdd.TRUE
  then SOME acc
  else
   if bdd.equal bdd bdd.FALSE
    then NONE
    else
     case find_bdd_model_aux (bdd.low bdd) acc of
        SOME bddl => SOME(bdd.nithvar(bdd.var bdd)::bddl)
      | NONE      => case find_bdd_model_aux (bdd.high bdd) acc of
                        SOME bddl => SOME(bdd.ithvar(bdd.var bdd)::bddl)
                      | NONE      => NONE;

fun  find_bdd_model bdd =  
 case find_bdd_model_aux bdd [] of
    SOME bddl => SOME(foldr bdd.AND bdd.TRUE bddl)
  | NONE      => NONE;

fun findModel tm = 
 let val bdd             = termToBdd tm     (* sequencing important here! *)
     val ((_,var_map),_) = !bdd_state
 in
  case find_bdd_model_aux bdd [] of
     SOME []   => T
   | SOME bddl => list_mk_conj(map (bdd_to_literal var_map) bddl)
   | NONE      => hol_err "Can't find model" "findModel"
 end;

(*****************************************************************************)
(* Find a BDD (conjunction of literals) that refutes a non-tautology         *)
(*****************************************************************************)

fun find_bdd_refutation bdd = 
 if bdd.equal bdd bdd.TRUE
  then NONE
  else
   if bdd.equal bdd bdd.FALSE
    then SOME bdd.TRUE
    else
     if bdd.equal (bdd.high bdd) bdd.FALSE
      then SOME(bdd.ithvar(bdd.var bdd))
      else
       if bdd.equal (bdd.low bdd) bdd.FALSE
        then SOME(bdd.nithvar(bdd.var bdd))
        else
         case find_bdd_refutation (bdd.high bdd) of
            SOME bdd' => SOME(bdd.AND(bdd.ithvar(bdd.var bdd),bdd'))
          | NONE      => case find_bdd_refutation (bdd.low bdd) of
                            SOME bdd' => SOME
                                          (bdd.AND
                                            (bdd.nithvar(bdd.var bdd),
                                           bdd'))
                          | NONE      => NONE;


(*****************************************************************************)
(* Get the name of a BDD node using the current BDD state                    *)
(*****************************************************************************)

fun get_node_name n =
 (case assoc2 n (var_map_to_pairs(snd(fst(!bdd_state)))) of
     SOME(str,_) => str
   | NONE        => hol_err ("Node "^(int_to_string n)^" has no name") 
                            "get_node_name");

(*****************************************************************************)
(* Convert a BDD to a conditional term using the current BDD state           *)
(*****************************************************************************)

(* Old version
fun bddToTerm bdd = 
 let infix 9 sub 
     val op sub = Vector.sub
     val (root,nt) = bdd.nodetable bdd
     fun var i  = Psyntax.mk_var(get_node_name(#1(nt sub i)),``:bool``)
     fun low i  = #2(nt sub i) 
     fun high i = #3(nt sub i)
     fun bddToTerm_aux node = 
           if node=0 then T
      else if node=1 then F 
                     else Psyntax.mk_cond
                           (var node, 
                            bddToTerm_aux(high node), 
                            bddToTerm_aux(low node))
 in
  bddToTerm_aux root
 end;
*)

fun bddToTerm bdd =
 if (bdd.equal bdd bdd.TRUE)
  then T
  else
   if (bdd.equal bdd bdd.FALSE)
    then F
    else Psyntax.mk_cond(mk_var(get_node_name(bdd.var bdd),bool),
                         bddToTerm(bdd.high bdd),
                         bddToTerm(bdd.low bdd));


(*****************************************************************************)
(* Equivalence BDD representation                                            *)
(*****************************************************************************)

fun bddRepOracle t = bddEqOracle(t, bddToTerm(termToBdd t));

(*****************************************************************************)
(* Count number of nodes in a BDD                                            *)
(*****************************************************************************)

(* Now in Muddy
fun nodecount bdd = Vector.length(snd(nodetable bdd));
*)

(*****************************************************************************)
(* Count number of states (code from Ken Larsen)                             *)
(*****************************************************************************)

fun statecount b = 
 let val sat    = bdd.satcount b
     val total  = Real.fromInt(bdd.getVarnum())
     val sup    = bdd.scanset(bdd.support b)
     val numsup = Real.fromInt(Vector.length sup)
     val free   = total - numsup
 in  if bdd.equal b bdd.TRUE 
      then 0.0
      else sat / Math.pow(2.0, free)
 end;

end


(*
end
*)





