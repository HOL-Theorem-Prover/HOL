structure ConstMapML :> ConstMapML =
struct

local open boolTheory in end;

open HolKernel

val ERR = mk_HOL_ERR "ConstMapML";

fun LEX c1 c2 ((x1,x2),(y1,y2)) =
  case c1 (x1,y1)
   of EQUAL => c2 (x2,y2)
    | other => other;

val qmk_vartype = with_flag (Feedback.emit_WARNING,false) mk_vartype;

val eq_alpha = qmk_vartype "''a";

(* ----------------------------------------------------------------------
    The initial constant map has equality, conjunction, disjunction,
    negation, true, and false in it. The range is 4-tuples of the form
    (is_constructor,structure name,value name, type).
   ---------------------------------------------------------------------- *)



structure CMap :> sig
  type 'a dict
  val empty : unit -> 'a dict
  val insert : ('a dict * term * 'a) -> 'a dict
  val peek : 'a dict * term -> 'a option
  val exact_peek : 'a dict * term -> 'a option
end =
struct
  structure RBM = Redblackmap
  fun tstamp () = Time.toReal (Time.now())
  type 'a dict = ({Name:string,Thy:string}, ('a * real) TypeNet.typenet)RBM.dict
  fun insert (d,k,v) = let
    val v = (v,tstamp())
    val {Name,Thy,Ty} = dest_thy_const k
    val rbk = {Name = Name, Thy = Thy}
  in
    case RBM.peek(d, rbk) of
      NONE => RBM.insert(d,rbk,TypeNet.insert(TypeNet.empty,Ty,v))
    | SOME tynet => let
        val tynet' = TypeNet.insert(tynet,Ty,v)
      in
        RBM.insert(d,rbk,tynet')
      end
  end

  fun peek(d,k) = let
    val {Name,Thy,Ty} = dest_thy_const k
    val rbk = {Name = Name, Thy = Thy}
  in
    case RBM.peek(d,rbk) of
      NONE => NONE
    | SOME tynet => let
      in
        case TypeNet.match(tynet, Ty) of
          [] => NONE
        | possresults => let
            fun possmatch (pat,data) =
                case Lib.total (fn ty => raw_match_type pat ty ([],[])) Ty of
                  NONE => NONE
                | SOME (inst,eqs) => SOME (map (fn ty => ty |-> ty) eqs @ inst,
                                           data)
            val insts0 = List.mapPartial possmatch possresults
            fun isize sigma =
                List.foldl (fn ({residue,...},acc) => acc + type_size residue)
                           0
                           sigma
            val icmp0 = pair_compare (measure_cmp isize,
                                      flip_order o Real.compare)
            val icmp = inv_img_cmp (fn (i,(d,t)) => (i,t)) icmp0
            val insts = Listsort.sort icmp insts0
          in
            case insts of
              [] => NONE
            | (i,(d,t)) :: _ => SOME d
          end
      end
  end
  fun cmp ({Name=n1,Thy=t1},{Name=n2,Thy=t2}) =
      pair_compare(String.compare,String.compare) ((n1,t1),(n2,t2))
  fun empty() = RBM.mkDict cmp

  fun exact_peek (d : 'a dict,k) = let
    val {Name,Thy,Ty} = dest_thy_const k
    val rbk = {Name = Name, Thy = Thy}
  in
    case RBM.peek(d,rbk) of
      NONE => NONE
    | SOME tynet => Option.map #1 (TypeNet.peek(tynet,Ty))
  end

end (* struct *)

open CMap

type constmap = (bool*string*string*hol_type)dict


(*---------------------------------------------------------------------------*)
(* Need to call same_const in order to get the notion of equality desired,   *)
(* otherwise could just use Term.compare.                                    *)
(*---------------------------------------------------------------------------*)

val initConstMap : constmap = empty()

local val equality = prim_mk_const{Name="=",Thy="min"}
      val negation = prim_mk_const{Name="~",Thy="bool"}
      val T        = prim_mk_const{Name="T",Thy="bool"}
      val F        = prim_mk_const{Name="F",Thy="bool"}
      val conj     = prim_mk_const{Name="/\\",Thy="bool"}
      val disj     = prim_mk_const{Name="\\/",Thy="bool"}
in
val ConstMapRef = ref
  (insert(insert(insert(insert(insert(insert
    (initConstMap,
     equality, (false,"","=",    eq_alpha-->eq_alpha-->bool)),
     negation, (false,"","not",  bool-->bool)),
     T,        (false,"","true", bool)),
     F,        (false,"","false",bool)),
     conj,     (false,"","andalso",bool-->bool-->bool)),
     disj,     (false,"","orelse", bool-->bool-->bool)))
end;

fun theConstMap () = !ConstMapRef;

(*---------------------------------------------------------------------------*)
(* Checks for "*" are to avoid situation where prefix multiplication has an  *)
(* open paren just before it ... which is interpreted as beginning of a      *)
(* comment.                                                                  *)
(*---------------------------------------------------------------------------*)

local fun check_name(is_type_cons,Thy,Name,Ty) =
       let val Name' = if String.sub(Name,0) = #"*" orelse
                          String.sub(Name,String.size Name -1) = #"*"
                       then " "^Name^" "
                       else Name
       in (is_type_cons,Thy,Name',Ty)
       end
in
fun prim_insert (c,t) = (ConstMapRef := insert(theConstMap(),c,check_name t))
end;


fun insert c =
 let val {Name,Thy,Ty} = dest_thy_const c
 in prim_insert(c,(false,Thy,Name,Ty))
 end;

fun insert_cons c =
 let val {Name,Thy,Ty} = dest_thy_const c
 in prim_insert(c,(true,Thy,Name,Ty))
 end;

fun apply c =
 case peek(theConstMap(),c)
   of SOME triple => triple
    | NONE => let val {Name,Thy,Ty} = dest_thy_const c
              in raise ERR "apply"
                       ("no binding found for "^Lib.quote(Thy^"$"^Name))
              end

fun exact_peek c = CMap.exact_peek(theConstMap(), c)

end
