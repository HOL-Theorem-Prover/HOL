signature Sig =
sig
  type ty
  type thm = KernelTypes.thm
  type id = KernelTypes.id
  type witness = KernelTypes.witness

  type entry = {const   : ty,
                witness : witness option}
  val id_of       : ty -> id

  datatype status
       = INITIAL of entry
       | CLOBBER of entry

  val insert      : ty -> status
  val delete      : string * string -> bool
  val lookup      : string * string -> entry option
  val resolve     : string -> entry list
  val add_witness : string * string * witness -> unit

  val app         : (entry list -> entry list) -> unit
  val slice       : string -> entry list
  val filter      : (entry -> bool) -> unit
  val scope       : (entry -> bool) -> unit
  val del_segment : string -> unit
  val all_entries : unit -> entry list
end;


(*---------------------------------------------------------------------------
     An abstract HOL signature, to be instantiated to
     types and terms.
 ---------------------------------------------------------------------------*)

functor SIG (type ty
             val key : ty -> string * string (* name * theory *)
             val id_of : ty -> KernelTypes.id
             val ERR : string -> string -> exn
             val table_size : int) : Sig =
struct

type ty = ty;
val id_of = id_of

open Lib KernelTypes;

(*---------------------------------------------------------------------------
      The type of signature entries
 ---------------------------------------------------------------------------*)

type entry = {const   : ty,
              witness : witness option}

fun retire const = KernelTypes.retire (id_of const);

(*---------------------------------------------------------------------------
        Hash tables are used to represent signatures
 ---------------------------------------------------------------------------*)

val theSig = Array.array(table_size, ([]:entry list))

val hasher = Lib.hash table_size;
fun hash s = hasher s (0,0);


(*---------------------------------------------------------------------------
    When inserting elements into the signature, we have to be aware
    if we overwrite an existing element.

       INITIAL entry  -- there was no pre-existing entry.
       CLOBBER entry  -- an existing entry e was overwritten by entry
 ---------------------------------------------------------------------------*)

datatype status
     = INITIAL of entry
     | CLOBBER of entry


(*---------------------------------------------------------------------------
       Insert an element into the signature, perhaps replacing
       a previous version. It is externally enforced that the
       replacement can only happen in the current theory segment.
 ---------------------------------------------------------------------------*)

local val clobbered = ref false
in
fun insert item =
 let val p as (name,_) = key item
     val i = hash name
     val entry = {const=item, witness=NONE}
     fun add [] = [entry]  (* new addition *)
       | add ((e as {const, ...}) :: rst)
          = if p = key const (* replace an existing resident *)
            then (retire const; clobbered := true; entry::rst)
            else e::add rst
 in
   clobbered := false
   ; Array.update(theSig, i, add (Array.sub(theSig, i)))
   ; (if !clobbered then CLOBBER else INITIAL) entry
 end
end;


(*---------------------------------------------------------------------------
       Add a witness to an existing element in the signature.
 ---------------------------------------------------------------------------*)

fun add_witness (name, theory, wit) =
 let val p = (name,theory)
     val i = hash name
     val L = Array.sub(theSig, i)
     fun get [] = raise ERR "add_witness" "no such constant"
       | get ((e as {const, witness}) :: rst)
           = if p = key const
             then {const=const, witness=SOME wit} :: rst
             else e::get rst
 in
    Array.update(theSig, i, get L)
 end;


(*---------------------------------------------------------------------------
      Remove an element from a signature. Return a bit reporting
      on whether successful.
 ---------------------------------------------------------------------------*)

fun delete (p as (name,_)) =
 let val i = hash name
     fun del [] = raise ERR "" ""
       | del ((e as {const,witness}) :: rst) =
          if p = key const then (retire const; rst) else e::del rst
 in
   Array.update(theSig, i, del (Array.sub(theSig, i)))
   ; true
 end
 handle Feedback.HOL_ERR _ => false;


(*---------------------------------------------------------------------------
      Find an element based on name and segment.
 ---------------------------------------------------------------------------*)

fun lookup (p as (name,_)) =
 let fun look [] = NONE
       | look ((e as {const,witness})::rst) = if p = key const then SOME e
                                              else look rst
 in
   look (Array.sub(theSig, hash name))
 end;


(*---------------------------------------------------------------------------
      Find all elements in the current theory having the given name.
 ---------------------------------------------------------------------------*)

fun resolve name =
 let fun look [] = []
       | look ((e as {const,witness})::rst) =
           if name = #1 (key const) then e::look rst else look rst
 in
   look (Array.sub(theSig, hash name))
 end;


(*---------------------------------------------------------------------------*
 * Filter theSig by a predicate. Apply a function to all entries.            *
 *---------------------------------------------------------------------------*)

fun app f =
  for_se 0 (table_size - 1)
      (fn i => Array.update(theSig,i, f (Array.sub(theSig,i))))

fun filter P = app (Lib.gather P)
fun scope P  = app (op@ o Lib.partition P);

fun del_segment seg =
    let fun doit (e as {witness,const}) =
            if seg = #2 (key const) then (retire const; false)
            else true
    in
      filter doit
    end

(*---------------------------------------------------------------------------
      Find all elements in a specified segment.
 ---------------------------------------------------------------------------*)

fun foldl f b = Array.foldl (fn (L, A) => List.foldl f A L) b theSig;

fun slice segment =
  foldl (fn (e as {witness,const},D) => if segment = #2 (key const) then e::D
                                        else D)
        [];

fun all_entries() = foldl (op::) [];;

end (* SIG *)
