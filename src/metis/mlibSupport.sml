(* ========================================================================= *)
(* THE SET OF SUPPORT                                                        *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

(*
app load ["mlibHeap", "UNLINK", "mlibThm", "Subsumers1"];
*)

(*
*)
structure mlibSupport :> mlibSupport =
struct

infix |->;

open mlibUseful mlibTerm;

structure H = mlibHeap; local open mlibHeap in end;
structure C = mlibClause; local open mlibClause in end;

type 'a heap = 'a H.heap;
type clause  = C.clause;

(* ------------------------------------------------------------------------- *)
(* Parameters.                                                               *)
(* ------------------------------------------------------------------------- *)

type parameters = {size_bias : int}

val defaults = {size_bias = 10};

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

(* This clause_size function ignores type annotations *)
(* We use the square root function to favour clauses with fewer literals. *)
local
  fun sz n []                         = n
    | sz n (Fn (":", [tm, _]) :: tms) = sz n (tm :: tms)
    | sz n (Var _ :: tms)             = sz (n + 1) tms
    | sz n (Fn (_, l) :: tms)         = sz (n + 1) (l @ tms);
  val sq = Math.sqrt o Real.fromInt o sz 0 o wrap o dest_atom o literal_atom;
in
  val clause_size = foldl (fn (h, t) => sq h + t) 0.0 o C.clause_lits;
end;

(* ------------------------------------------------------------------------- *)
(* Clause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  val i2r = Real.fromInt;
  val is_contr = null o C.clause_lits;
  fun is_refl cl =
    let val f = dest_eq o literal_atom o unwrap o C.clause_lits
    in case total f cl of NONE => false | SOME (x,y) => x = y
    end;
in
  fun clause_weight (parm : parameters) (n, cl) =
    let
      val s = 1.0 + clause_size cl
    in
      if is_contr cl then ~1.0
      else if is_refl cl then ~1.0 + (1.0 / s)
      else
        let
          val {size_bias, ...} = parm
          val r_n = i2r n
          val (r_a, r_s) =
            if size_bias = 0 then (1.0, 1.0) else (i2r size_bias, s)
        in
          (r_n + r_a) * r_s / r_a
        end
    end;
end;

(* ------------------------------------------------------------------------- *)
(* The set of support.                                                       *)
(* ------------------------------------------------------------------------- *)

datatype sos = SOS of
  {parm    : parameters,
   next    : int,
   clauses : (real * (int * clause)) heap};

fun update_next n sos =
  let val SOS {parm = p, next = _, clauses = c} = sos
  in SOS {parm = p, next = n, clauses = c}
  end;

fun update_clauses c sos =
  let val SOS {parm = p, next = n, clauses = _} = sos
  in SOS {parm = p, next = n, clauses = c}
  end;

local
  fun order ((m, _), (n, _)) = Real.compare (m, n);
in
  fun new p = SOS {parm = p, next = 0, clauses = H.empty order};

  fun reset (SOS {parm = p, ...}) =
    SOS {parm = p, next = 0, clauses = H.empty order};
end;

fun size (SOS {clauses, ...}) = H.size clauses;

local
  fun add1 (cl, sos) =
    let
      val SOS {parm, next, clauses, ...} = sos
      val w = clause_weight parm (next, cl)
      val sos = update_clauses (H.add (w, (next, cl)) clauses) sos
    in
      sos
    end;
in
  fun addl cls sos =
    let val SOS {next, ...} = sos
    in foldl add1 (update_next (next + 1) sos) cls
    end;

  fun add c = addl [c];
end;

fun remove sos =
  let
    val SOS {clauses, ...} = sos
  in
    if H.is_empty clauses then NONE else
      let
        val ((_, (_, cl)), cls) = H.remove clauses
        val sos = update_clauses cls sos
      in
        SOME (cl, sos)
      end
  end;

end
