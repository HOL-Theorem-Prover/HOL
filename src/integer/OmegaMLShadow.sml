structure OmegaMLShadow =
struct

(* ----------------------------------------------------------------------
    Implementation of "shadow chasing" in ML.  This procedure can find
    a real shadow refutation without forcing all of the shadow to be
    computed in the logic; a path to false can be found that only
    involves a small proportion of the possible logical inferences.

    Alternatively, if the shadow is exact, then this procedure can
    also generate witnesses for the logic to exploit, again saving it
    from having to do a lot of calculation internally.
   ---------------------------------------------------------------------- *)

open HolKernel boolLib

open intSyntax

(* ----------------------------------------------------------------------
    The factoid datatype

    A factoid c[0..n] represents the term
       0 <= c[0] * v_0 + .. + c[n-1] * v_{n-1} + c[n] * 1
    The factoid "key" is the vector of variable coefficients, leaving
    out the constant part.
   ---------------------------------------------------------------------- *)

datatype factoid =
         ALT of Arbint.int Vector.vector

type factoid_key = Arbint.int Vector.vector

fun factoid_key f =
    case f of
      ALT av => Vector.extract(av, 0, SOME (Vector.length av - 1))
fun factoid_constant f =
    case f of
      ALT av => Vector.sub(av, Vector.length av - 1)

fun split_factoid f = (factoid_key f, factoid_constant f)

fun zero_var_factoid f =
    Vector.foldl (fn (ai, b) => b andalso ai = Arbint.zero) true
                 (factoid_key f)

val the_false_factoid = ALT (Vector.fromList [Arbint.fromInt ~1])
fun false_factoid f =
    zero_var_factoid f andalso Arbint.<(factoid_constant f, Arbint.zero)
fun true_factoid f =
    zero_var_factoid f andalso Arbint.<=(Arbint.zero, factoid_constant f)

fun eval_factoid_rhs vmap f = let
  open Arbint Vector
  fun foldthis (i, ai, acc) =
      if ai = zero then acc
      else ai * PIntMap.find i vmap + acc
in
  case f of
    ALT fv => foldli foldthis zero (fv, 0, NONE)
end

val negate_key = Vector.map Arbint.~

fun keyhash v =
    if Arbint.<=(Arbint.zero,Vector.sub(v, 0)) then Polyhash.hash v
    else ~(Polyhash.hash (Vector.map Arbint.~ v))


(* "prints" factoids *)
fun factoid_pairings vars f =
    case f of
      ALT av => Vector.foldri
                (fn (i, ai, list) =>
                    (Arbint.toString ai, List.nth(vars, i)) :: list)
                [] (av, 0, NONE)

(* ----------------------------------------------------------------------
    combine_factoids i f1 f2

    takes two factoids and produces a fresh one by "variable
    elimination" over the i'th variable in the vector.  It requires
    that the coefficient of v_i is strictly positive in f1, and
    strictly negative in f2.  The combination may produce a factoid where
    the coefficients can all be divided through by some number, but
    this factor won't be the gcd of the coefficients of v_i; this
    factor is eliminated from the outset.
   ---------------------------------------------------------------------- *)

fun combine_factoids i f1 f2 =
    case (f1, f2) of
      (ALT av1, ALT av2) => let
        open Arbint Vector CooperMath
        val c0 = sub(av1, i)
        val d0 = Arbint.~ (sub(av2, i))
        val l = lcm (c0, d0)
        val c = l div d0
        val d = l div c0
        fun gen j = c * sub(av2, j) + sub(av1, j) * d
      in
        ALT (tabulate(length av1, gen))
      end

(* ----------------------------------------------------------------------
    factoid_gcd f

    eliminates common factors in the variable coefficients of a factoid,
    or raises the exception no_gcd, if there is no common factor.
   ---------------------------------------------------------------------- *)

exception no_gcd
fun factoid_gcd f =
    case f of
      ALT av => let
        open Vector CooperMath
        val g = foldli (fn (_, c, g0) => gcd (c, g0))
                       Arbint.zero
                       (av, 0, SOME (length av - 1))
      in
        if g = Arbint.one then raise no_gcd
        else ALT (map (fn c => Arbint.div(c, g)) av)
      end

(* ----------------------------------------------------------------------
    term_to_factoid tm

    returns the factoid corresponding to tm.  tm is thus of the form
      0 <= c1 * v1 + ... + cn * vn + num
    Assumes that the variables are in the "correct" order.
   ---------------------------------------------------------------------- *)

fun term_to_factoid tm = let
  val summands = strip_plus (rand tm)
  fun sum2c t =
      int_of_term (#1 (dest_mult t))
      handle HOL_ERR _ => int_of_term t
in
  ALT (Vector.fromList (map sum2c summands))
end

(* ----------------------------------------------------------------------
    factoid_to_term vars f

    returns the term corresponding to f, interpreting f over the list of
    variables vars.
   ---------------------------------------------------------------------- *)

fun factoid_to_term vars f =
    case f of
      ALT av => let
        open Vector
        fun varcoeff (i, c, t0) =
            if c = Arbint.zero then t0
            else let
                val cv = mk_mult(term_of_int c, List.nth(vars, i))
              in
                case t0 of NONE => SOME cv | SOME t => SOME (mk_plus(t, cv))
              end
        val varpart = foldli varcoeff NONE (av, 0, SOME (length av - 1))
        val numpart = term_of_int (sub(av,length av - 1))
      in
        case varpart of
          NONE => numpart
        | SOME t => mk_plus(t, numpart)
      end

(* ----------------------------------------------------------------------
    The derivation datatype
   ---------------------------------------------------------------------- *)

(* a derivation represents a proof of a factoid *)
datatype derivation =
         ASM of term
       | REAL_COMBIN of int * derivation * derivation
       | GCD_CHECK of derivation
       | DIRECT_CONTR of derivation * derivation

datatype result = CONTR of derivation
                | SATISFIABLE of Arbint.int PIntMap.t
                | NO_CONCL

fun direct_contradiction(d1, d2) = CONTR (DIRECT_CONTR(d1, d2))

fun combine_dfactoids i ((f1, d1), (f2, d2)) =
    (combine_factoids i f1 f2, REAL_COMBIN(i, d1, d2))

fun gcd_check_dfactoid (f, d) = (factoid_gcd f, GCD_CHECK d)

fun split_dfactoid (f, d) = (factoid_key f, (factoid_constant f, d))
fun dfactoid_key (f, d) = factoid_key f

(* ----------------------------------------------------------------------
    The "ptree" datatype

    I'm using a Patricia tree to store my sets of constraints.  The keys
    are the hashes of the constraint keys.  The items are lists
    (buckets) of dfactoids.
   ---------------------------------------------------------------------- *)

fun fkassoc k alist =
    case List.find (fn (f, data) => k = factoid_key f) alist of
      NONE => raise PIntMap.NotFound
    | SOME x => x

fun lookup_fkey ptree fk =
  fkassoc fk (PIntMap.find (keyhash fk) ptree)

val dbempty = PIntMap.empty

fun dbfold (f : ((factoid * derivation) * 'a) -> 'a) (acc:'a) ptree =
    PIntMap.fold (fn (i,b,acc) => List.foldl f acc b) acc ptree

fun dbapp (f : factoid * derivation -> unit) ptree =
    PIntMap.app (fn (i,b) => List.app f b) ptree

fun dbinsert (df as (f,d)) ptree =
    #1 (PIntMap.addf (fn b => df :: b) (keyhash (factoid_key f)) [df] ptree)

(* ----------------------------------------------------------------------
    add_factoid ptree df

    Precondition: df is neither a trivially true nor false factoid.

    adds a dfactoid (i.e., a factoid along with its derivation) to a
    Patricia tree of accumulating factoids.  If the factoid is
    actually redundant, because there is already a factoid with the
    same constraint key in the tree with a less or equal constant,
    then the tree is returned unchanged.  The return value is the new
    tree coupled with a boolean which is true iff the tree changed.
   ---------------------------------------------------------------------- *)

fun add_factoid ptree (df as (f,d)) = let
  val fkc as (fk, fc) = split_factoid f
  exception Redundant
  fun merge alist = let
    val ((f',_), samehashes) =
        Lib.pluck (fn (f', _) => factoid_key f' = fk) alist
  in
    if Arbint.<(fc, factoid_constant f') then df :: samehashes
    else raise Redundant
  end handle HOL_ERR _ => df :: alist (* HOL_ERR might come from Lib.pluck *)
in
  (#1 (PIntMap.addf merge (keyhash fk) [df] ptree), true)
  handle Redundant => (ptree, false)
end

(* ----------------------------------------------------------------------
    add_check_factoid ptree df

    Precondition: df is neither a trivially true nor false factoid

   ---------------------------------------------------------------------- *)

fun add_check_factoid ptree0 (df as (f,d)) kont = let
  val (ptree, changed) = add_factoid ptree0 df
in
  if not changed then kont ptree
  else let
      val (fk,fc) = split_factoid f
      val (negdf as (negf, negd)) = lookup_fkey ptree (negate_key fk)
      val negc = factoid_constant negf
      open Arbint
    in
      if negc < ~fc then direct_contradiction(d, negd)
      else kont ptree
    end handle PIntMap.NotFound => kont ptree
end

(* ----------------------------------------------------------------------
    add_factoids ptree dfl kont

    Adds all of the factoids in dfl to ptree, and then continues with
    continuation kont (of type :ptree -> result)
   ---------------------------------------------------------------------- *)

fun add_factoids ptree dfl kont =
    case dfl of
      [] => kont ptree
    | (df :: dfs) => add_check_factoid ptree df
                                       (fn pt => add_factoids pt dfs kont)


(* ----------------------------------------------------------------------
    has_one_var ptree

    returns true if all of ptree's factoids are over just one variable
    (and they're all the same variable)
   ---------------------------------------------------------------------- *)

fun has_one_var ptree = let
  exception return_false
  fun checkkey (i,c,acc) =
      if c = Arbint.zero then acc
      else
        case acc of
          NONE => SOME i
        | _ => raise return_false
  fun check ((f,d),a) = let
    val fk = factoid_key f
    val fk_single = valOf (Vector.foldli checkkey NONE (fk, 0, NONE))
  in
    case a of
      NONE => SOME fk_single
    | SOME i => if i = fk_single then a else raise return_false
  end
in
  (dbfold check NONE ptree; true) handle return_false => false
end


(* ----------------------------------------------------------------------
    one_var_analysis ptree

    Precondition: the dfactoids in ptree have just one variable with a
    non-zero coefficient, and its everywhere the same variable.  Our aim
    is to either derive a contradiction, or to return a satisfying
    assignment.  Our gcd_checks will have ensured that our variable
    (call it x) will only have coefficients of one at this point, so
    we just need to check that the maximum of the lower bounds is less
    than or equal to the minimum of the lower bounds.  If it is then
    return either as a satisfying valuation for x.  Otherwise return
    false, combining the maximum lower and the minimum upper constraint.
   ---------------------------------------------------------------------- *)

fun one_var_analysis ptree = let
  val (_, (_, a_bucket)) = PIntMap.choose ptree
  val (a_constraint, _) = hd a_bucket
  fun find_var (i, ai, NONE) = if ai <> Arbint.zero then SOME i else NONE
    | find_var (_, _, v as SOME _) = v
  val x_var =
      valOf (Vector.foldli find_var NONE (factoid_key a_constraint, 0, NONE))
  open Arbint
  fun assign_factoid (df, acc as (upper, lower)) = let
    val (fk, (fc, d)) = split_dfactoid df
  in
    if Vector.sub(fk, x_var) < zero then
      case upper of
        NONE => (SOME (fc, d), lower)
      | SOME (c', d') => if fc < c' then (SOME (fc, d), lower) else acc
    else
      case lower of
        NONE => (upper, SOME (~fc, d))
      | SOME (c', d') => if ~fc > c' then (SOME (~fc,d), lower) else acc
  end
  val (upper, lower) =
      PIntMap.fold (fn (_,b,acc) => foldl assign_factoid acc b)
                   (NONE,NONE)
                   ptree
in
  case (upper, lower) of
    (NONE, NONE) => raise Fail "one_var_analysis: this can't happen"
  | (SOME (c, _), NONE) => SATISFIABLE (PIntMap.add x_var c PIntMap.empty)
  | (NONE, SOME (c, _)) => SATISFIABLE (PIntMap.add x_var c PIntMap.empty)
  | (SOME (u,du), SOME (l, dl)) =>
    if u < l then direct_contradiction(du,dl)
    else SATISFIABLE (PIntMap.add x_var u PIntMap.empty)
end

(* ----------------------------------------------------------------------
    throwaway_redundant_factoids ptree kont

    checks ptree for variables that are constrained only in one sense.
    If such a variable exists, then it can be chucked, as can all of
    the constraints that mention it.  Call ourselves recursively with
    the new ptree as there may be more variable eliminable, and
    examine the result that comes back from this application.  If it
    indicates that the system is satisfiable, then we need to update
    the map that is returned with a value for the variable we
    eliminated.  If there isn't a redundant variable, just continue
    directly with kont.
   ---------------------------------------------------------------------- *)

fun throwaway_redundant_factoids ptree kont = let
  val (_, (_, a_bucket)) = PIntMap.choose ptree
  val (a_constraint, _) = hd a_bucket
  val numvars = Vector.length (factoid_key a_constraint)
  val has_low = Array.array(numvars, false)
  val has_up = Array.array(numvars, false)

  fun assess fk = let
    fun appthis (i, ai) = let
      open Arbint
    in
      case compare(ai,zero) of
        LESS => Array.update(has_up, i, true)
      | EQUAL => ()
      | GREATER => Array.update(has_low, i, true)
    end
  in
    Vector.appi appthis (fk, 0, NONE)
  end
  val () = dbapp (fn (f,d) => assess (factoid_key f)) ptree

  fun find_redundant_var i =
      if i = numvars then NONE
      else if Array.sub(has_up, i) = Array.sub(has_low, i) then
        find_redundant_var (i + 1)
      else SOME (i, Array.sub(has_up, i))
in
  case find_redundant_var 0 of
    NONE => kont ptree
  | SOME(i, hasupper) => let
      fun partition (df as (f,d), (pt, elim)) = let
        open Arbint
      in
        if Vector.sub(factoid_key f, i) = zero then
          (dbinsert df pt, elim)
        else
          (pt, df :: elim)
      end
      val (newptree, elim) = dbfold partition (dbempty, []) ptree
    in
      case throwaway_redundant_factoids newptree kont of
        SATISFIABLE vmap => let
          val evaluated = map (eval_factoid_rhs vmap o #1) elim
          val foldfn = if hasupper then Arbint.min else Arbint.max
        in
          SATISFIABLE (PIntMap.add i (foldl foldfn (hd evaluated)
                                            (tl evaluated))
                                   vmap)
        end
      | x => x
    end
end

(* ----------------------------------------------------------------------
    exact_var ptree

    An exact var is one that has coefficients of one in either all of its
    upper bounds or all of its lower bounds.  This function returns
    SOME v if v is an exact var in ptree, or NONE if there is no exact
    var.
   ---------------------------------------------------------------------- *)

fun exact_var ptree = NONE

(* ----------------------------------------------------------------------
    one_step ptree kont

    Assume that ptree doesn't contain anything directly contradictory,
    and that there aren't any redundant constraints around (these have
    been thrown away by throwaway_redundant_factoids).

    Perform one step of the shadow calculation algorithm:
      (a) if there is only one variable left in all of the constraints
          in ptree do one_var_analysis to return some sort of result
      (b) otherwise, decide on a variable to eliminate.  If there's a
          variable that allows for an exact shadow (has coefficients of
          one in all of its lower-bound or upper-bound occurrences),
          pick this.  Otherwise, take the variable whose coefficients'
          absolute values sum to the least amount.
      (c) the initial tree of the result contains all of those
          constraints from the original which do not mention the
          variable to be eliminated.
      (d) divide the constraints that do mention the variable to be
          eliminated into upper and lower bound sets.
      (e) work through all of the possible combinations in
            upper x lower
          using combine_dfactoids.  Each new dfactoid has to be added
          to the accumulating tree.  This may produce a direct
          contradiction, in which case, stop and return this.  Otherwise
          keep going.
      (f) pass the completed new ptree to kont.
   ---------------------------------------------------------------------- *)

fun one_step ptree kont =
    if has_one_var ptree then
      one_var_analysis ptree
    else
      case exact_var ptree of
        x => raise Fail "Not implemented yet"





end (* struct *)