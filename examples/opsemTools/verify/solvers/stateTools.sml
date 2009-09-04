(*=============================================================== *)
(* Some tools to compute and simplify states.

   Used by the symbolic execution or by RUN, with constraint solver
   or SMT solver.
*)
(*=============================================================== *)

open HolKernel Parse boolLib
     newOpsemTheory bossLib pairSyntax intLib intSimps
     computeLib finite_mapTheory  stringLib intSyntax;



(*====================================== *)
(* functions to generate symbolic states *)
(* ===================================== *)


(* to make the initial state from the program given in opsem
   syntax.
   can be quite long
*)

(* take a term that corresponds to a program in opSem syntax
   and build a symbolic state that represents all
   its variables *)
(* Functions  written by Mike Gordon in PATH_EVAL *)
(* Have been modified to get also array variables *)

(* Functions below return a pair ([var ident], [array ident]) *)
(* ---------------------------------------------------------- *)

(* Get set of variables read in a numerical expression (nexp) *)
fun nexp_vars nex =
 let val (opr,args) = strip_comb nex  (* syntax error if "op" instead of "opr" *)
     val _ = if not(is_const opr)
              then (print_term opr;
                    print " is not a constant\n";
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Var","Arr","Const","Plus","Times","Div","Sub","Min"])
              then (print name;
                    print " is not an nexp constructor\n";
                    fail())
              else ()
 in
  case name of
    "Var"      => ([el 1 args],[])
  | "Arr"      =>  (fst (nexp_vars(el 2 args)),
                    insert (el 1 args) (snd(nexp_vars(el 2 args))))
  | "Const"    => ([],[])
  | "Plus"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Times"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Sub"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Div"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Min"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | _          => (print "BUG in nexp_vars! "; print name; fail())
 end;



(* Get set of variables read in a boolean expression (bexp) *)
fun bexp_vars bex =
 let val (opr,args) = strip_comb bex  (* syntax error if "op" instead of "opr" *)
     val _ = if not(is_const opr)
              then (print_term opr;
                    print " is not a constant\n";
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Equal","Less","LessEq","And","Or","Not"])
              then (print name;
                    print " is not a bexp constructor\n";
                    fail())
              else ()
 in
  case name of
   "Equal"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Less"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "LessEq"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "And"     => (union (fst (bexp_vars(el 1 args))) (fst (bexp_vars(el 2 args)))
                  , union (snd (bexp_vars(el 1 args))) (snd (bexp_vars(el 2 args))))
  | "Or"     => (union (fst (bexp_vars(el 1 args))) (fst (bexp_vars(el 2 args)))
                  , union (snd (bexp_vars(el 1 args))) (snd (bexp_vars(el 2 args))))
  | "Not"      => bexp_vars(el 1 args)
  | _          => (print "BUG in bexp_vars! "; print name; fail())
 end;


(* Get set of variables read or assigned to in a program *)

local
(* to transform GenAssign into Assign or ArrayAssign *)
(* needed when using arrays to represent states, to get variables
   which occurs in the command to execute with MLnextState *)
fun getConcreteAssign i =
  if is_comb(i)
  then
    let val (inst,args) = strip_comb(i)
    in
      if inst = ``GenAssign``
      then
         let val (ty,vall) = dest_comb(el 2 args)
         in
           if ty = ``(INL :nexp -> nexp + aexp)``
           then ``Assign ^(el 1 args) ^vall``
           else
              let val (_,arrUpdate) = strip_comb vall
              in
                ``ArrayAssign ^(el 1 args) ^(el 2 arrUpdate) ^(el 3 arrUpdate)``
              end
         end
      else i
     end
  else i;

in
fun program_vars c =
 let val (opr,args) = strip_comb c  (* N.B. syntax error if "op" instead of "opr" *)
     val _ = if not(is_const opr)
              then (print_term opr;
                    print " is not a constant\n";
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Skip","Assign","ArrayAssign","GenAssign","Dispose","Seq",
                              "Cond","While","Local","Assert"])
              then (print name;
                    print " is not a program constructor\n";
                    fail())
              else ()
 in
  case name of
    "Skip"     => ([],[])
  | "Assign"   => let val exp2= nexp_vars(el 2 args)
                  in
                     (insert (el 1 args) (fst exp2),
                      snd exp2)
                  end

  | "ArrayAssign"   => let val exp2=nexp_vars(el 2 args)
                         val exp3 = nexp_vars(el 3 args)
                       in
			   ((union (fst exp2) (fst exp3)),
			    insert (el 1 args)
				   (union (snd exp2)
					  (snd exp3)))
                       end
  | "GenAssign"   => let val ass = getConcreteAssign c
                     in
                        program_vars ass
                     end

  | "Dispose"  => ([],[])
  | "Seq"      => let val p1= program_vars(el 1 args)
                     val p2= program_vars(el 2 args)
                  in
		   (union  (fst p1) (fst p2),
		    union (snd p1) (snd p2))
                  end
  | "Cond"     =>  let val p2= program_vars(el 2 args)
                     val p3= program_vars(el 3 args)
                     val exp1 = bexp_vars(el 1 args)
                  in
		    (union
			 (fst exp1)
			 (union (fst p2) (fst p3)),
		     union
			 (snd exp1)
			 (union (snd p2) (snd p3)))
		   end

  | "While"    => let val p2= program_vars(el 2 args)
                     val exp1 = bexp_vars(el 1 args)
                  in
		     (union (fst exp1) (fst p2),
		      union (snd exp1) (snd p2))
		  end
  | "Local"    => ([],[])
  | "Assert"   => ([],[])
  | _          => (print "BUG in program_vars! "; print name; fail())
 end
end;


(* ==================================== *)
(* functions to make the initial state  *)
(* ==================================== *)
val MAX_ARRAY_SIZE = 10;


(* to know if a variable is the length of an array *)
fun isArrayLength tm =
  let val s = fromHOLstring tm
  in
     if (size s) > 6
     then
       String.extract (s,(size s) -6, NONE) = "Length"
     else false
  end;


(*
Construct: FEMPTY |++ [("v1",v1);...;("vn",vn)]
where v1,...,vn are the integer variables read or written in c

TODO: build the length of the array from preconditions
*)

fun varPairs vars =
  let val maxTerm = term_of_int(Arbint.fromInt(MAX_ARRAY_SIZE))
  in
    map
      (fn tm =>
         if isArrayLength tm
         then ``(^tm,Scalar ^maxTerm)``
         else
           ``(^tm, Scalar ^(mk_var(fromHOLstring tm,``:int``)))``)
    vars
  end;



(*
Construct a pair (name,value) where name is the name of an array variable
and (value) is a finite_map that represents symbolic initial value of the array.
assuming that the maximum array size is MAX_ARRAY_SIZE.

FEMPTY |++ [("v1",(FEMPTY |++ (0,v1_0) |+ (1,v1_1) |+ ...
   |+ (MAX_ARRAY_SIZE-1,v1_MAX_ARRAY_SIZE-1));...;("vn",(FEMPTY |++ (0,vn_0) |+ (1,vn_1) |+ ...
   |+ (MAX_ARRAY_SIZE,vn_MAX_ARRAY_SIZE-1))]
where v1,...,vn are the array variables read or written in c.

*)

local

fun generateValues(n,l) =
  let val symbVal = mk_var(n ^ "_"  ^ Int.toString(l),``:int``);
  in
  if (l=0)
  then ``(FEMPTY |+ (0:num,^symbVal))``
  else
    let
        val arr = generateValues(n,l-1);
    in
      ``^arr |+ (^(numSyntax.mk_numeral(Arbnum.fromInt(l))),^symbVal)``
    end
end;


fun generateArray(n) =
  let val values = generateValues(n,MAX_ARRAY_SIZE-1);
      val nt = stringSyntax.fromMLstring(n);
  in
    ``(^nt, Array(^values))``
end;


in

fun arrayPairs vars =
 map
   (fn tm => generateArray(fromHOLstring(tm)))
 vars

end;


(* --------------------------------- *)
(* main function to create the state *)
(* --------------------------------- *)
(* for each array "arr", add an int variable "arrLength"
   that corresponds to arr.length *)
(* if the length of the array is given in the precondition,
   then it is fixed to this value, else it is fixed to
   MAX_ARRAY_SIZE *)

local

(* add a variable xxxLength for each array xxx
   in the list of int variables *)
fun addArrLength varNames arrNames =
 if arrNames = []
 then varNames
 else
   List.concat(
    (map
      (fn tm =>
        insert
        (stringSyntax.fromMLstring(fromHOLstring(tm)^ "Length"))
        varNames
      )
      arrNames));

(* TODO
fun  getArrayLength pre =
    take the precondition and return a list of pairs
   ("arrLength", val) where val is the length of array arr
   given in the precondition or is MAX_ARRAY_SIZE if no information is
   given in the precondition *)

in

(* ----------------------------------- *)
(* Returns a pair (listVar, st)
   where listVar is a list of String that contains all variables
         s is a symbolic state built from listVar
*)
(* ----------------------------------- *)

(* make the state from the list of variables
   which has been built during translation from Java to opsem
   and is stored under definition intVar_def and arrVar_def
*)
fun makeStateFromVars v =
 let  val varNames = fst v;
    val arrNames = snd v;
    val varAndLengthNames = addArrLength varNames arrNames;
    val vars = varPairs varAndLengthNames;
    val arrayVars = arrayPairs arrNames
  in
     (varAndLengthNames,
      ``FEMPTY |++ ^(listSyntax.mk_list(vars@arrayVars,``:string#value``))``
     )
  end;

fun makeState c =
  let val names = program_vars c;
  in
     makeStateFromVars names
  end;

fun makeStateListFromVars v =
 let  val varNames = fst v;
    val arrNames = snd v;
    val varAndLengthNames = addArrLength varNames arrNames;
    val vars = varPairs varAndLengthNames;
    val arrayVars = arrayPairs arrNames
  in
      listSyntax.mk_list(vars@arrayVars,``:string#value``)
  end;

fun makeStateList c =
  let val names = program_vars c;
  in
     makeStateListFromVars names
  end;



end;



(* end of functions to generate symbolic states *)
(* ============================================ *)

(* ---------------------------------------------- *)
(* function to transform the list of solutions
   as a finite map that can be used as outcome

  st: the state
  l: a list of solution of the form (var,val)
*)
(* ---------------------------------------------- *)

local
fun addSol st nt vt =
  ``^st |+ (^nt,Scalar ^vt)``;

in
fun finiteMapSol l st =
  if null l
  then st
  else
    let val (n,v) = (fst(hd(l)),snd(hd(l)));
      val (nt,vt) = (stringSyntax.fromMLstring(n),
                     intSyntax.term_of_int(Arbint.fromString(v)));
      val newSt = addSol st nt vt
      in
        finiteMapSol (tl l) newSt
    end
end;


(* --------------------------------- *)
(* functions to simplify finite_maps *)
(* --------------------------------- *)

(* Test if a term is FEMPTY or of the form FEMPTY |+ (x1,y1) .... |+ (xn,yn) *)
fun is_finite_map fm =
 (is_const fm andalso fst(dest_const fm) = "FEMPTY")
 orelse (let val (opr,args) = strip_comb fm
         in
          is_const opr
          andalso fst(dest_const opr) = "FUPDATE"
          andalso (length args = 2)
          andalso is_finite_map(el 1 args)
          andalso is_pair(el 2 args)
         end);


(* Remove overwritten entries in a finite map *)
fun PRUNE_FINITE_MAP_CONV  fm =
 if not(is_finite_map fm) orelse
    (is_const fm andalso fst(dest_const fm) = "FEMPTY")
  then REFL fm
  else (REWR_CONV FUPDATE_PRUNE
         THENC RATOR_CONV(RAND_CONV(EVAL THENC PRUNE_FINITE_MAP_CONV)))
       fm;


(* to prune arrays. Keep only the last value that have been assigned
   for each index *)
fun pruneArray fm =
  if is_const fm
  then fm
  else
    let val (_,args1) = strip_comb fm
       val fnext = (el 1 args1)
       val v = (el 2 args1)
       val (_,args2) = strip_comb v
       val name = (el 1 args2)
       val value = (el 2 args2)
       val pruneNext =  pruneArray(fnext)
       in
         if is_comb value andalso fst(dest_comb(value))=``Array``
         then
          let val pruneArr =  snd(dest_comb(concl(PRUNE_FINITE_MAP_CONV(snd(dest_comb(value))))))
            val newVal = ``(^name, Array ^pruneArr)``
          in
            ``(^pruneNext |+ ^newVal)``
          end
         else ``(^pruneNext |+ ^v)``
        end;

(* to keep only final values *)
fun pruneState st =
   let val ps = snd(dest_comb(concl(PRUNE_FINITE_MAP_CONV  st)))
   in
      pruneArray ps
end;



(* --------------------------------------------------*)
(* to print a condition in the program as a condition
   on variables instead of functions of state        *)

(* (Cond (Less i j)) will be printed as i<j
   instead of (ScalarOf 'i) < (ScalarOf 'j)          *)
(* --------------------------------------------------*)
local

(* Get set of string terms in a term *)
(* Written by Mike Gordon in verifier.ml    *)
fun get_strings tm =
 if is_string tm
  then [tm] else
 if is_var tm orelse is_const tm
  then [] else
 if is_comb tm
  then union (get_strings(rator tm)) (get_strings(rand tm)) else
 if is_abs tm
  then get_strings(body tm)
  else (print "error in get_strings"; fail());

fun makeStateFromPair l =
  if ((length l) = 1)
  then ``(FEMPTY |+ ^(hd l)) ``
  else
      let
        val map = makeStateFromPair (tl l);
      in
         ``^map |+ ^(hd l)``
end;

in

fun pretty_string tm =
 let val var_tms = get_strings tm;
     val pairs = map
                  (fn tm => pairSyntax.mk_pair
                      let val v = mk_var(fromHOLstring tm,``:int``)
                      in
		      (tm,``Scalar ^v``)
			end
		  )
                  var_tms;
     val st = makeStateFromPair pairs;
     val (_,res) = strip_comb(concl(EVAL ``beval ^tm ^st``));
     in
       term_to_string(el 2 res)
     end
end;

