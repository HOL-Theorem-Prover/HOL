structure quote =
struct

open HolKernel Parse quoteTheory;

infix THEN THENL |->;

fun QUOTE_ERR function message =
    HOL_ERR{origin_structure = "quote",
		      origin_function = function,
		      message = message};

fun mk_comb2 (a,b,c) = mk_comb(mk_comb(a,b),c);
fun mk_comb3 (a,b,c,d) = mk_comb(mk_comb2(a,b,c),d);

(* reify varmap *)
val mevm = --`Empty_vm : 'a varmap`--;
val mnvm = --`Node_vm : 'a->'a varmap->'a varmap->'a varmap`--;
fun vm_ty ty = inst [alpha |-> ty];


datatype varnode
    = Lf
    | Nd of term * varnode ref * varnode ref

type varmap = varnode ref;

fun meta_map ty =
  let val mevm = vm_ty ty mevm
      val mnvm = vm_ty ty mnvm
      fun meta_rec (ref Lf) = mevm
        | meta_rec (ref (Nd(t,v1,v2))) =
	    mk_comb3(mnvm,t,meta_rec v1, meta_rec v2)
  in meta_rec
  end
;



(* abstract term and compute the varmap *)

datatype index = Li of index | Lr of index | Ei;

val mli = --`Left_idx`--
val mri = --`Right_idx`--
val mei = --`End_idx`--;

fun meta_index Ei = mei
  | meta_index (Li i) = mk_comb(mli, meta_index i)
  | meta_index (Lr i) = mk_comb(mri, meta_index i)
;


fun search_term t vm =
  case !vm of
    Lf => NONE
  | Nd(x,v1,v2) =>
      (if aconv t x then SOME Ei
      else case search_term t v1 of
	SOME i => SOME (Li i)
      |	NONE =>
	  (case search_term t v2 of
	    SOME i => SOME (Lr i)
	  | NONE => NONE));


fun add_term t vm i =
  case (i, !vm) of
    (1, Lf) => (vm := Nd(t,ref Lf, ref Lf); Ei)
  | (n, Nd(_,v1,v2)) =>
      if n mod 2 = 0 then Li (add_term t v1 (i div 2))
      else Lr (add_term t v2 (i div 2))
  | _ => raise QUOTE_ERR "add_term" "";

local
  val vm = ref Lf
  val size = ref 0
in
fun empty_map () =
  (vm := Lf; size := 0)

and get_map ty =
  let val meta = meta_map ty
      fun get_it() =
        let val m = meta vm in
  	empty_map();
  	m
        end
  in get_it
  end

and term_index t =
  case search_term t vm of
    SOME i => i
  | _ =>
      let val _ = size := (!size) + 1 in
      add_term t vm (!size)
      end
end;



datatype expr =
    Pvar of index
  | Pquote of term
  | Pnode of term * expr list
;

fun is_quote (Pquote _) = true | is_quote _ = false;
fun mk_op t h l = if all is_quote l then Pquote t else Pnode(h,l);



fun op_assoc x [] = NONE
  | op_assoc x ((y,v)::l) = if (aconv x y) then SOME v else op_assoc x l
;


fun meta_expr ty is_qu { Op1, Op2, Vars, Csts } =
  let fun meta_rec t =
        if is_qu t then Pquote t
        else
	  let val oper =
    	    if is_comb t then
	      let val (r1,a1) = dest_comb t in
	      case op_assoc r1 Op1 of
		SOME ope => SOME(mk_op t ope [meta_rec a1])
	      |	NONE =>
		  if is_comb r1 then
      	    	    let val (r2,a2) = dest_comb r1 in
    	    	    case op_assoc r2 Op2 of
		      SOME ope =>
			SOME(mk_op t ope [meta_rec a2, meta_rec a1])
		    | NONE => NONE
	    	    end
		  else NONE
	      end
    	    else NONE
	  in case oper of
    	    SOME mt => mt
	  | NONE => Pvar (term_index t)
	  end

      fun meta_pol (Pvar i) = mk_comb(Vars,meta_index i)
        | meta_pol (Pquote t) = mk_comb(Csts,t)
	| meta_pol (Pnode(h,l)) = foldl(fn(a,ht) => mk_comb(ht,meta_pol a)) h l

      fun non_trivial (Pvar _) =
	    raise QUOTE_ERR "meta_expr" "unrecognized polynomial expression"
	| non_trivial p = p

      val mpol = meta_pol  o  non_trivial  o  meta_rec
      val mk_map = get_map ty

      fun meta_list lt =
        let val _ = empty_map()
	    val lmt = map mpol lt
	    val mm = mk_map()
  	in {Metamap=mm,Poly=lmt} end
  in meta_list
  end;


end;
