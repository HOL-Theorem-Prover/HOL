(* ========================================================================= *)
(* FILE          : Theory.sml                                                *)
(* DESCRIPTION   : Management of logical theories.                           *)
(*                                                                           *)
(* AUTHOR        : Konrad Slind, University of Calgary                       *)
(*                 (also T.U. Munich and Cambridge)                          *)
(* DATE          : September 11, 1991                                        *)
(* REVISION      : August 7, 1997                                            *)
(*               : March 9, 1998                                             *)
(*               : August 2000                                               *)
(*                                                                           *)
(* ========================================================================= *)

(* ----------------------------------------------------------------------
    Updated November/December 2002 - by Michael Norrish
   ---------------------------------------------------------------------- *)

(*---------------------------------------------------------------------------

     Notes on the design.

  We provide a single current theory segment, which can be thought of as
  a scratchpad for building the segment that eventually gets exported.
  The following are the important components of a segment:

      - the types and terms declared in the current segment (stored in
        the "symbol tables" maintained in modules Term and Type).

      - the unique id for the theory, along with its parents, which
        should be already-loaded theory segments.

      - the theory graph, used to enforce a prohibition on circular
        dependencies among segments.

      - the axioms, definitions, and theorems stored in the segment so far.

  The parents of the segment are held in the theory graph.

  When a segment is exported, we dump everything in it to a text file
  representing an ML structure.

  Elements in the current segment can be deleted or overwritten, which
  makes consistency maintenance an issue.  Before a theory is exported,
  everything that is about to be exported gets checked for up-to-date-ness.

 ---------------------------------------------------------------------------*)


structure Theory :> Theory =
struct

open Feedback Lib Type Term Thm ;

type ppstream = Portable.ppstream
type pp_type  = ppstream -> hol_type -> unit
type pp_thm   = ppstream -> thm -> unit
type num = Arbnum.num

infix ##;

val ERR  = mk_HOL_ERR "Theory";
val WARN = HOL_WARNING "Theory";

type thy_addon = {sig_ps    : (ppstream -> unit) option,
                  struct_ps : (ppstream -> unit) option}


(* This reference is set in course of loading the parsing library *)

val pp_thm = ref (fn _:ppstream => fn _:thm => ())

(*---------------------------------------------------------------------------*
 * Unique identifiers, for securely linking a theory to its parents when     *
 * loading from disk.                                                        *
 *---------------------------------------------------------------------------*)
local
  open Arbnum
in
abstype thyid = UID of {name:string, sec: num, usec : num}
with
  fun thyid_eq x (y:thyid) = (x=y);
  fun new_thyid s =
      let val {sec,usec} = Portable.dest_time (Portable.timestamp())
      in
        UID{name=s, sec = sec, usec = usec}
      end

  fun dest_thyid (UID{name, sec, usec}) = (name,sec,usec)

  val thyid_name = #1 o dest_thyid;

  fun make_thyid(s,i1,i2) = UID{name=s, sec=i1,usec=i2}

  fun thyid_to_string (UID{name,sec,usec}) =
     String.concat["(",Lib.quote name,",",toString sec, ",",
                   toString usec, ")"]

  val min_thyid =
      UID{name="min", sec = fromInt 0, usec = fromInt 0}  (* Ur-theory *)

end;
end (* local *)

fun thyid_assoc x [] = raise ERR "thyid_assoc" "not found"
  | thyid_assoc x ((a,b)::t) = if thyid_eq x a then b else thyid_assoc x t;

fun thyname_assoc x [] = raise ERR "thyname_assoc" "not found"
  | thyname_assoc x ((a,b)::t) = if x = thyid_name a then b
                                 else thyname_assoc x t;


(*---------------------------------------------------------------------------
    The theory graph is quite basic: just a list of pairs (thyid,parents).
    The "min" theory is already installed; it has no parents.
 ---------------------------------------------------------------------------*)

structure Graph = struct type graph = (thyid * thyid list) list
local val theGraph = ref [(min_thyid,[])]
in
   fun add p = theGraph := (p :: !theGraph)
   fun add_parent (n,newp) =
     let fun same (node,_) = thyid_eq node n
         fun addp(node,parents) = (node, op_union thyid_eq [newp] parents)
         fun ins (a::rst) = if same a then addp a::rst else a::ins rst
           | ins [] = raise ERR "Graph.add_parent.ins" "not found"
     in theGraph := ins (!theGraph)
     end
   fun isin n = Lib.can (thyid_assoc n) (!theGraph);
   fun parents_of n = thyid_assoc n (!theGraph);
   fun ancestryl L =
    let fun Anc P Q = rev_itlist
           (fn nde => fn A => if op_mem thyid_eq nde A then A
             else Anc (parents_of nde handle HOL_ERR _ => []) (nde::A)) P Q
    in Anc L []
    end;
   fun fringe () =
     let val all_parents = List.map #2 (!theGraph)
         fun is_parent y = Lib.exists (Lib.op_mem thyid_eq y) all_parents
     in List.filter (not o is_parent) (List.map #1 (!theGraph))
     end;
   fun first P = Lib.first P (!theGraph)
end
end; (* structure Graph *)


(*---------------------------------------------------------------------------*
 * A type for distinguishing the different kinds of theorems that may be     *
 * stored in a theory.                                                       *
 *---------------------------------------------------------------------------*)

datatype thmkind = Thm of thm | Axiom of string Nonce.t * thm | Defn of thm

fun is_axiom (Axiom _) = true  | is_axiom _   = false;
fun is_theorem (Thm _) = true  | is_theorem _ = false;
fun is_defn (Defn _)   = true  | is_defn _    = false;

fun drop_thmkind (Axiom(_,th)) = th
  | drop_thmkind (Thm th)      = th
  | drop_thmkind (Defn th)     = th;

fun drop_pthmkind (s,th) = (s,drop_thmkind th);

fun drop_Axkind (Axiom rth) = rth
  | drop_Axkind    _        = raise ERR "drop_Axkind" "";


(*---------------------------------------------------------------------------*
 * The type of HOL theory segments. Lacks fields for the type and term       *
 * signatures, which are held locally in the Type and Term structures.       *
 * Also lacks a field for the theory graph, which is held in Graph.          *
 *---------------------------------------------------------------------------*)

datatype thydata = Loaded of UniversalType.t
                 | Pending of string list
type ThyDataMap = (string,thydata)Binarymap.dict
                  (* map from string identifying the "type" of the data,
                     e.g., "simp", "mono", "cong", "grammar_update",
                     "LaTeX map", to the data itself. *)
val empty_datamap : ThyDataMap = Binarymap.mkDict String.compare

type segment = {thid    : thyid,                               (* unique id  *)
                facts   : (string * thmkind) list,  (* stored ax,def,and thm *)
                thydata : ThyDataMap,                   (* extra theory data *)
                adjoin  : thy_addon list}              (*  extras for export *)


(*---------------------------------------------------------------------------*
 *                 CREATE THE INITIAL THEORY SEGMENT.                        *
 *                                                                           *
 * The timestamp for a segment is its creation date. "con_wrt_disk" is       *
 * set to false because when a segment is created no corresponding file      *
 * gets created (the file is only created on export).                        *
 *---------------------------------------------------------------------------*)

fun fresh_segment s :segment = {thid=new_thyid s,  facts=[],  adjoin=[],
                               thydata = empty_datamap};


local val CT = ref (fresh_segment "scratch")
in
  fun theCT() = !CT
  fun makeCT seg = CT := seg
end;

val CTname = thyid_name o #thid o theCT;
val current_theory = CTname;


(*---------------------------------------------------------------------------*
 *                  READING FROM THE SEGMENT                                 *
 *---------------------------------------------------------------------------*)

fun thy_types thyname               = Type.thy_types thyname
fun thy_constants thyname           = Term.thy_consts thyname
fun thy_parents thyname             = snd (Graph.first
                                           (equal thyname o thyid_name o fst))
fun thy_axioms (th:segment)         = filter (is_axiom o #2)   (#facts th)
fun thy_theorems (th:segment)       = filter (is_theorem o #2) (#facts th)
fun thy_defns (th:segment)          = filter (is_defn o #2)    (#facts th)
fun thy_addons (th:segment)         = #adjoin th

fun stamp thyname =
  let val (_,sec,usec) = dest_thyid (fst (Graph.first
                          (equal thyname o thyid_name o fst)))
  in
    Portable.mk_time {sec = sec, usec = usec}
  end;

local fun norm_name "-" = CTname()
        | norm_name s = s
      fun grab_item style name alist =
        case Lib.assoc1 name alist
         of SOME (_,th) => th
          | NONE => raise ERR style
                      ("couldn't find "^style^" named "^Lib.quote name)
in
 val types            = thy_types o norm_name
 val constants        = thy_constants o norm_name
 fun get_parents s    = if norm_name s = CTname()
                         then Graph.fringe() else thy_parents s
 val parents          = map thyid_name o get_parents
 val ancestry         = map thyid_name o Graph.ancestryl o get_parents
 fun current_axioms() = map drop_pthmkind (thy_axioms (theCT()))
 fun current_theorems() = map drop_pthmkind (thy_theorems (theCT()))
 fun current_definitions() = map drop_pthmkind (thy_defns (theCT()))
end;


(*---------------------------------------------------------------------------*
 * Is a segment empty?                                                       *
 *---------------------------------------------------------------------------*)

fun empty_segment ({thid,facts, ...}:segment) =
  let val thyname = thyid_name thid
  in null (thy_types thyname) andalso
     null (thy_constants thyname) andalso
     null facts
  end;

(*---------------------------------------------------------------------------*
 *              ADDING TO THE SEGMENT                                        *
 *---------------------------------------------------------------------------*)

fun add_type {name,theory,arity} thy =
    (Type.prim_new_type {Thy = theory, Tyop = name} arity; thy)

fun add_term {name,theory,htype} thy =
    (Term.prim_new_const {Thy = theory, Name = name} htype; thy)

local fun pluck1 x L =
        let fun get [] A = NONE
              | get ((p as (x',_))::rst) A =
                if x=x' then SOME (p,rst@A) else get rst (p::A)
        in get L []
        end
      fun overwrite (p as (s,f)) l =
       case pluck1 s l of
         NONE => p::l
       | SOME ((_,f'),l') => p::l'
in
fun add_fact (th as (s,_)) {thid, facts,adjoin,thydata} =
    {facts= overwrite th facts, thid=thid, adjoin=adjoin,thydata=thydata}
end;

fun new_addon a {thid, facts, adjoin, thydata} =
    {adjoin = a::adjoin, facts=facts, thid=thid, thydata=thydata};

local fun plucky x L =
       let fun get [] A = NONE
             | get ((p as (x',_))::rst) A =
                if x=x' then SOME (rev A, p, rst) else get rst (p::A)
       in get L []
       end
in
fun set_MLbind (s1,s2) (rcd as {thid, facts, adjoin, thydata}) =
    case plucky s1 facts of
      NONE => (WARN "set_MLbind" (Lib.quote s1^" not found in current theory");
               rcd)
    | SOME (X,(_,b),Y) =>
      {facts=X@((s2,b)::Y), adjoin=adjoin,thid=thid, thydata=thydata}
end;

(*---------------------------------------------------------------------------
            Deleting from the segment
 ---------------------------------------------------------------------------*)

fun del_type (name,thyname) thy =
    (Type.prim_delete_type {Thy = thyname, Tyop = name}; thy)

(*---------------------------------------------------------------------------
        Remove a constant from the signature.
 ---------------------------------------------------------------------------*)

fun del_const (name,thyname) thy =
    (Term.prim_delete_const {Thy = thyname, Name = name} ; thy)

fun del_binding name {thid,facts,adjoin,thydata} =
  {facts = filter (fn (s, _) => not(s=name)) facts, thid=thid, adjoin=adjoin,
   thydata = thydata};

(*---------------------------------------------------------------------------
   Clean out the segment. Note: this clears out the segment, and the
   signatures, but does not alter the theory graph. The segment will
   still be there, with its parents.
 ---------------------------------------------------------------------------*)

fun zap_segment s (thy : segment) =
    (Type.del_segment s; Term.del_segment s;
     {adjoin=[], facts=[],thid= #thid thy, thydata = empty_datamap})

(*---------------------------------------------------------------------------
       Wrappers for functions that alter the segment.
 ---------------------------------------------------------------------------*)

local fun inCT f arg = makeCT(f arg (theCT()))
in
  val add_typeCT        = inCT add_type
  val add_termCT        = inCT add_term
  fun add_axiomCT(r,ax) = inCT add_fact (Nonce.dest r, Axiom(r,ax))
  fun add_defnCT(s,def) = inCT add_fact (s,  Defn def)
  fun add_thmCT(s,th)   = inCT add_fact (s,  Thm th)

  fun delete_type n     = inCT del_type  (n,CTname())
  fun delete_const n    = inCT del_const (n,CTname())
  val delete_binding    = inCT del_binding

  fun set_MLname s1 s2  = inCT set_MLbind (s1,s2)
  val adjoin_to_theory  = inCT new_addon
  val zapCT             = inCT zap_segment

end;


(*---------------------------------------------------------------------------*
 *            INSTALLING CONSTANTS IN THE CURRENT SEGMENT                    *
 *---------------------------------------------------------------------------*)

fun new_type (Name,Arity) =
 (if Lexis.allowed_type_constant Name orelse
     not (!Globals.checking_type_names)
  then ()
  else WARN "new_type" (Lib.quote Name^" is not a standard type name")
  ; add_typeCT {name=Name, arity=Arity, theory = CTname()};());

fun new_constant (Name,Ty) =
  (if Lexis.allowed_term_constant Name orelse
      not (!Globals.checking_const_names)
   then ()
   else WARN "new_constant" (Lib.quote Name^" is not a standard constant name")
   ; add_termCT {name=Name, theory=CTname(), htype=Ty}; ())

(*---------------------------------------------------------------------------
     Install constants in the current theory, as part of loading a
     previously built theory from disk.
 ---------------------------------------------------------------------------*)

fun install_type(s,a,thy)   = add_typeCT {name=s, arity=a, theory=thy};
fun install_const(s,ty,thy) = add_termCT {name=s, htype=ty, theory=thy}


(*---------------------------------------------------------------------------
 * Is an object wellformed (current) wrt the symtab, i.e., have none of its
 * constants been re-declared after it was built? A constant is
 * up-to-date if either 1) it was not declared in the current theory (hence
 * it was declared in an ancestor theory and is thus frozen); or 2) it was
 * declared in the current theory and its witness is up-to-date.
 *
 * When a new entry is made in the theory, it is checked to see if it is
 * uptodate (or if its witnesses are). The "overwritten" bit of a segment
 * tells whether any element of the theory has been overwritten. If
 * overwritten is false, then the theory is uptodate. If we want to add
 * something to an uptodate theory, then no processing need be done.
 * Otherwise, we have to examine the item, and recursively any item it
 * depends on, to see if any constant or type constant occurring in it,
 * or any theorem it depends on, is outofdate. If so, then the item
 * will not be added to the theory.
 *
 * To clean up a theory with outofdate elements, use "scrub".
 *
 * To tell if an object is uptodate, we can't just look at it; we have
 * to recursively examine its witness(es). We can't just accept a witness
 * that seems to be uptodate, since its constants may be flagged as uptodate,
 * but some may depend on outofdate witnesses. The solution taken
 * here is to first set all constants in the segment signature to be
 * outofdate. Then a bottom-up pass is made. The "utd" flag in each
 * signature entry is used to cut off repeated recursive traversal, as in
 * dynamic programming. It holds the value "true" when the witness is
 * uptodate.
 *---------------------------------------------------------------------------*)

fun uptodate_thm thm =
    Lib.all uptodate_term (Thm.concl thm::Thm.hyp thm)
    andalso
    uptodate_axioms (Tag.axioms_of (Thm.tag thm))
and uptodate_axioms [] = true
  | uptodate_axioms rlist = let
      val axs = map (drop_Axkind o snd) (thy_axioms(theCT()))
    in
      (* tempting to call uptodate_thm here, but this would put us into a loop
         because axioms have themselves as tags, also unnecessary because
         axioms never have hypotheses (check type of new_axiom) *)
      Lib.all (uptodate_term o Thm.concl o Lib.C Lib.assoc axs) rlist
    end handle HOL_ERR _ => false

fun scrub_ax {thid,facts,adjoin,thydata} =
   let fun check (_, Thm _ ) = true
         | check (_, Defn _) = true
         | check (_, Axiom(_,th)) = uptodate_term (Thm.concl th)
   in
      {thid=thid, adjoin=adjoin, facts=List.filter check facts, thydata=thydata}
   end

fun scrub_thms {thid,facts,adjoin, thydata} =
   let fun check (_, Axiom _) = true
         | check (_, Thm th ) = uptodate_thm th
         | check (_, Defn th) = uptodate_thm th
   in {thid=thid, adjoin=adjoin, facts=List.filter check facts, thydata=thydata}
   end

fun scrub () = makeCT (scrub_thms (scrub_ax (theCT())))

fun scrubCT() = (scrub(); theCT());


(*---------------------------------------------------------------------------*
 *   WRITING AXIOMS, DEFINITIONS, AND THEOREMS INTO THE CURRENT SEGMENT      *
 *---------------------------------------------------------------------------*)

local fun check_name (fname,s) = ()
      fun DATED_ERR f bindname = ERR f (Lib.quote bindname^" is out-of-date!")
      val save_thm_reporting = ref 1
      val _ = Feedback.register_trace ("Theory.save_thm_reporting",
                                       save_thm_reporting, 2)
      val mesg = with_flag(MESG_to_string, Lib.I) HOL_MESG
in
fun save_thm (name,th) =
      (check_name ("save_thm",name)
       ; if uptodate_thm th then add_thmCT(name,th)
         else raise DATED_ERR "save_thm" name
       ; if !save_thm_reporting = 0 then ()
         else if not (!Globals.interactive) orelse !save_thm_reporting > 1
         then
           mesg ("Saved theorem " ^ name ^ "\n")
         else ()
       ; th)

fun new_axiom (name,tm) =
   let val rname = Nonce.mk name
       val axiom = Thm.mk_axiom_thm (rname,tm)
       val  _ = check_name ("new_axiom",name)
   in if uptodate_term tm then add_axiomCT(rname,axiom)
      else raise DATED_ERR "new_axiom" name
      ; axiom
   end

fun store_definition(name, def) =
    let val ()  = check_name ("store_type_definition",name)
    in
      if uptodate_thm def then ()
      else raise DATED_ERR "store_type_definition" name
      ; add_defnCT(name,def)
      ; def
  end


end;

(*---------------------------------------------------------------------------*
 * Adding a new theory into the current theory graph.                        *
 *---------------------------------------------------------------------------*)

fun set_diff a b = filter (fn x => not (Lib.op_mem thyid_eq x b)) a;
fun node_set_eq S1 S2 = null(set_diff S1 S2) andalso null(set_diff S2 S1);

fun link_parents thy plist =
 let val node = make_thyid thy
     val parents = map make_thyid plist
 in
 if Lib.all Graph.isin parents
 then if Graph.isin node
      then if node_set_eq parents (Graph.parents_of node) then ()
           else (HOL_MESG
                  "link_parents: the theory has two unequal sets of parents";
                 raise ERR "link_parents" "")
      else Graph.add (node,parents)
 else let val baddies = Lib.filter (not o Graph.isin) parents
          val names = map thyid_to_string baddies
    in HOL_MESG (String.concat
        ["link_parents: the following parents of ",
         Lib.quote (thyid_name node),
         "\n  should already be in the theory graph (but aren't): ",
         String.concat (commafy names)]);
       raise ERR "link_parents" ""
    end
 end;

fun incorporate_types thy tys =
  let fun itype (s,a) = (install_type(s,a,thy);())
  in List.app itype tys
  end;

fun incorporate_consts thy tyvector consts =
  let fun iconst(s,i) = (install_const(s,Vector.sub(tyvector,i),thy);())
  in List.app iconst consts
  end;

(* ----------------------------------------------------------------------
    Theory data functions

    In addition to the data in the current segment, we want to track the data
    associated with all previous segments.  We do this with another reference
    variable (yuck).
   ---------------------------------------------------------------------- *)

structure LoadableThyData =
struct

  type t = UniversalType.t
  type DataOps = {merge : t * t -> t, read : string -> t option,
                  write : t -> string}
  val allthydata = ref (Binarymap.mkDict String.compare :
                        (string, ThyDataMap) Binarymap.dict)
  val dataops = ref (Binarymap.mkDict String.compare :
                     (string, DataOps) Binarymap.dict)


  fun ThyMap() = let
    val {thydata,thid,...} = theCT()
    val nm = thyid_name thid
  in
    Binarymap.insert(!allthydata, nm, thydata)
  end

  fun segment_data {thy,thydataty} =
      case Binarymap.peek(ThyMap(), thy) of
        NONE => NONE
      | SOME dmap => let
        in
          case Binarymap.peek(dmap, thydataty) of
            NONE => NONE
          | SOME (Loaded value) => SOME value
          | SOME (Pending _) => raise ERR "segment_data"
                                          "Can't interpret pending loads"
        end

  fun write_data_update {thydataty,data} =
      case Binarymap.peek(!dataops, thydataty) of
        NONE => raise ERR "write_data_update"
                          ("No operations defined for "^thydataty)
      | SOME {merge,read,write} => let
          val {thydata,thid,adjoin,facts} = theCT()
          open Binarymap
          fun updatemap inmap = let
            val newdata =
                case peek(inmap, thydataty) of
                  NONE => Loaded data
                | SOME (Loaded t) => Loaded (merge(t, data))
                | SOME (Pending ds) =>
                    raise Fail "write_data_update invariant failure"
          in
            insert(inmap,thydataty,newdata)
          end
        in
          makeCT {thydata = updatemap thydata, thid=thid, adjoin=adjoin,
                  facts=facts}
        end

  fun temp_encoded_update {thy, thydataty, data} = let
    val {thydata, thid, adjoin, facts} = theCT()
    open Binarymap
    fun updatemap inmap = let
      val baddecode = ERR "temp_encoded_update"
                          ("Bad decode for "^thydataty^" ("^data^")")
      val newdata =
        case (peek(inmap, thydataty), peek(!dataops,thydataty)) of
          (NONE, NONE) => Pending [data]
        | (NONE, SOME {read,...}) =>
            Loaded (valOf (read data) handle Option => raise baddecode)
        | (SOME (Loaded t), NONE) =>
             raise Fail "temp_encoded_update invariant failure 1"
        | (SOME (Loaded t), SOME {merge,read,...}) =>
             Loaded (merge(t, valOf (read data)
                              handle Option => raise baddecode))
        | (SOME (Pending ds), NONE) => Pending (data::ds)
        | (SOME (Pending _), SOME _) =>
             raise Fail "temp_encoded_update invariant failure 2"
    in
      insert(inmap, thydataty, newdata)
    end
in
  if thy = thyid_name thid then
    makeCT {thydata = updatemap thydata, thid=thid, facts=facts, adjoin=adjoin}
  else let
      val newsubmap =
          case peek (!allthydata, thy) of
            NONE => updatemap empty_datamap
          | SOME dm => updatemap dm
    in
      allthydata := insert(!allthydata, thy, newsubmap)
    end
end

fun update_pending (m,r) thydataty = let
  open Binarymap
  fun update1 inmap =
      case peek(inmap, thydataty) of
        NONE => inmap
      | SOME (Loaded t) => raise Fail "update_pending invariant failure 1"
      | SOME (Pending []) => raise Fail "update_pending invariant failure 2"
      | SOME (Pending (ds as (_ :: _))) => let
          fun foldthis (d,acc) = m(acc, valOf (r d))
          val ds' = List.rev ds
        in
          insert(inmap,thydataty,
                 Loaded (List.foldl foldthis (valOf (r (hd ds'))) (tl ds')))
        end
  fun foldthis (k,v,acc) = insert(acc,k,update1 v)
  val _ = allthydata := Binarymap.foldl foldthis
                                        (Binarymap.mkDict String.compare)
                                        (!allthydata)
  val {thid,facts,adjoin,thydata} = theCT()
in
  makeCT {thid=thid,facts=facts,adjoin=adjoin,thydata = update1 thydata}
end

fun 'a new {thydataty, merge, read, write} = let
  val (mk : 'a -> t, dest) = UniversalType.embed ()
  fun vdest t = valOf (dest t)
  fun merge' (t1, t2) = mk(merge(vdest t1, vdest t2))
  fun read' s = Option.map mk (read s)
  fun write' t = write (vdest t)
in
  dataops := Binarymap.insert(!dataops,
                              thydataty,
                              {merge=merge', read=read', write=write'});
  update_pending (merge',read') thydataty;
  (mk,dest)
end


end (* struct *)



(*---------------------------------------------------------------------------*
 *         PRINTING THEORIES OUT AS ML STRUCTURES AND SIGNATURES.            *
 *---------------------------------------------------------------------------*)

fun theory_out width f ostrm =
 let val ppstrm = Portable.mk_ppstream
                    {consumer = Portable.outputc ostrm,
                     linewidth=75, flush = fn () => Portable.flush_out ostrm}
 in f ppstrm handle e => (Portable.close_out ostrm; raise e);
    Portable.flush_ppstream ppstrm;
    Portable.close_out ostrm
 end;

fun unkind facts =
  List.foldl (fn ((s,Axiom (_,th)),(A,D,T)) => ((s,th)::A,D,T)
               | ((s,Defn th),(A,D,T))     => (A,(s,th)::D,T)
               | ((s,Thm th),(A,D,T))     => (A,D,(s,th)::T)) ([],[],[]) facts;

(* automatically reverses the list, which is what is needed. *)

fun unadjzip [] A = A
  | unadjzip ({sig_ps,struct_ps}::t) (l1,l2) =
       unadjzip t (sig_ps::l1, struct_ps::l2)


(*---------------------------------------------------------------------------
    We always export the theory, except if it is the initial theory (named
    "scratch") and the initial theory is empty. If the initial theory is
    *not* empty, i.e., the user made some definitions, or stored some
    theorems or whatnot, then the initial theory will be exported.
 ----------------------------------------------------------------------------*)

fun total_cpu {usr,sys} = Time.+(usr,sys)
val new_theory_time = ref (total_cpu (Timer.checkCPUTimer Globals.hol_clock))

val report_times = ref true
val _ = Feedback.register_btrace ("report_thy_times", report_times)

local
  val mesg = Lib.with_flag(Feedback.MESG_to_string, Lib.I) HOL_MESG
  fun maybe_log_time_to_disk thyname timestr = let
    open FileSys
    fun concatl pl = List.foldl (fn (p2,p1) => Path.concat(p1,p2))
                                (hd pl) (tl pl)
    val filename_opt = let
      val build = Systeml.build_log_file
      val currentdir = Systeml.make_log_file
    in
      List.find (fn s => access(s, [A_WRITE])) [build, currentdir]
    end
  in
    case filename_opt of
      SOME s => let
        val fs = TextIO.openAppend s
      in
        TextIO.output(fs, thyname ^ " " ^ timestr ^ "\n");
        TextIO.closeOut fs
      end
    | NONE => ()
  end
in
fun export_theory () = let
  val {thid,facts,adjoin,thydata} = scrubCT()
  val concat = String.concat
  val thyname = thyid_name thid
  val name = CTname()^"Theory"
  val (A,D,T) = unkind facts
  val (sig_ps, struct_ps) = unadjzip adjoin ([],[])
  val sigthry = {name = thyname,
                 parents = map thyid_name (Graph.fringe()),
                 axioms = A,
                 definitions = D,
                 theorems = T,
                 sig_ps = sig_ps}
  fun mungethydata dmap = let
    fun foldthis (k,v,acc) =
        case v of
          Loaded t => let
            val w = #write (Binarymap.find(!LoadableThyData.dataops, k))
          in
            Binarymap.insert(acc,k,w t)
          end
        | _ => acc
  in
    Binarymap.foldl foldthis (Binarymap.mkDict String.compare) dmap
  end
  val structthry =
      {theory = dest_thyid thid,
       parents = map dest_thyid (Graph.fringe()),
       types = thy_types thyname,
       constants = Lib.mapfilter Term.dest_const (thy_constants thyname),
       axioms = A,
       definitions = D,
       theorems = T,
       struct_ps = struct_ps,
       thydata = mungethydata thydata}
  val five_minutes = 300
  val one_hour = 60 * 60
  fun divmod (x,y) = (x div y, x mod y)
  fun tstr t = let
    val secs = Time.toSeconds t
    val pad2 = StringCvt.padLeft #"0" 2
  in
    if secs > five_minutes then let
        val (minutes, secs) = divmod(secs, 60)
      in
        if minutes > 60 then let
            val (hours,  minutes) = divmod(minutes, 60)
          in
            Int.toString hours ^ "h" ^
            pad2 (Int.toString minutes) ^ "m" ^
            pad2 (Int.toString secs) ^ "s"
          end
        else Int.toString minutes ^ "m" ^ pad2 (Int.toString secs)
      end
    else let
        val msecs = Time.toMilliseconds t
        val (secs,msecs) = divmod(msecs, 1000)
      in
        Int.toString secs ^ "." ^
        StringCvt.padLeft #"0" 3 (Int.toString msecs) ^ "s"
      end
  end
 in
   case filter (not o Lexis.ok_sml_identifier) (map fst (A@D@T)) of
     [] =>
     (let val ostrm1 = Portable.open_out(concat["./",name,".sig"])
          val ostrm2 = Portable.open_out(concat["./",name,".sml"])
          val time_now = total_cpu (Timer.checkCPUTimer Globals.hol_clock)
          val time_since = Time.-(time_now, !new_theory_time)
          val tstr = tstr time_since
      in
        mesg ("Exporting theory "^Lib.quote thyname^" ... ");
        theory_out 85 (TheoryPP.pp_sig (!pp_thm) sigthry) ostrm1;
        theory_out 75 (TheoryPP.pp_struct structthry) ostrm2;
        mesg "done.\n";
        if !report_times then
          (mesg ("Theory "^Lib.quote thyname^" took "^ tstr ^ " to build\n");
           maybe_log_time_to_disk thyname (Time.toString time_since))
        else ()
      end
        handle e => (Lib.say "\nFailure while writing theory!\n"; raise e))

   | badnames =>
     (HOL_MESG
        (String.concat
           ["\nThe following ML binding names in the theory to be exported:\n",
            String.concat (Lib.commafy (map Lib.quote badnames)),
            "\n are not acceptable ML identifiers.\n",
            "   Use `set_MLname <bad> <good>' to change each name."]);
        raise ERR "export_theory" "bad binding names")
end
end;


(* ----------------------------------------------------------------------
    "on load" stuff
   ---------------------------------------------------------------------- *)

val onloadfns = ref ([] : (string -> unit) list)
fun register_onload f = (onloadfns := !onloadfns @ [f])

fun load_complete thyname = List.app (fn f => f thyname) (!onloadfns)


(*---------------------------------------------------------------------------*
 *    Allocate a new theory segment over an existing one. After              *
 *    that, initialize any registered packages. A package registers          *
 *    with a call to "after_new_theory".                                     *
 *---------------------------------------------------------------------------*)

local val initializers = ref [] : (string * string -> unit) list ref
in
fun after_new_theory f = (initializers := f :: !initializers)
fun initialize oldname =
  let val ct = current_theory()
      fun rev_app [] = ()
        | rev_app (f::rst) =
            (rev_app rst;
             f (oldname, ct) handle e =>
                let val errstr =
                   case e
                    of HOL_ERR r => !ERR_to_string r
                     | otherwise => General.exnMessage e
                in
                  WARN "new_theory.initialize"
                        ("an initializer failed with message: "
                         ^errstr^"\n ... continuing anyway. \n")
                end)
  in rev_app (!initializers)
  end
end;


fun new_theory str =
    if not(Lexis.ok_identifier str) then
      raise ERR "new_theory"
                ("proposed theory name "^Lib.quote str^" is not an identifier")
    else let
        val thy as {thid, ...} = theCT()
        val thyname = thyid_name thid
        fun mk_thy () = (HOL_MESG ("Created theory "^Lib.quote str);
                         makeCT(fresh_segment str); initialize thyname)
        val _ =
            new_theory_time := total_cpu (Timer.checkCPUTimer Globals.hol_clock)
      in
        if str=thyname then
          (HOL_MESG("Restarting theory "^Lib.quote str);
           zapCT str; initialize thyname)
        else if mem str (ancestry thyname) then
          raise ERR"new_theory" ("theory: "^Lib.quote str^" already exists.")
        else if thyname="scratch" andalso empty_segment thy then
          mk_thy()
        else
          (export_theory ();
           Graph.add (thid, Graph.fringe()); mk_thy ())
      end


(* ----------------------------------------------------------------------
    Function f tries to extend current theory. If that fails then
    revert to previous state.

    We do not (yet) track changes to the state used by adjoin_to_theory or
    after_new_theory.
   ---------------------------------------------------------------------- *)

fun try_theory_extension f x =
  let infix ?>
      open Term
      val tnames1 = map fst (types"-")
      val cnames1 = map (fst o dest_const) (constants"-")
      fun revert _ =
        let val tnames2 = map fst (types"-")
            val cnames2 = map (fst o dest_const) (constants"-")
            val new_tnames = Lib.set_diff tnames2 tnames1
            val new_cnames = Lib.set_diff cnames2 cnames1
        in map delete_type new_tnames;
           map delete_const new_cnames;
           scrub()
        end
  in
    f x handle e => (revert(); raise e)
  end;

end (* Theory *)
