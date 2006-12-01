structure DiskFilesHeader :> DiskFilesHeader =
struct

open HolKernel

type id = {Thy:string,Name:string}

datatype pretype = ptv of string | ptop of int * int list
datatype pre_vc = ptm_v of string * int | ptm_c of int * int
datatype preterm = app of preterm * preterm | abs of int * preterm
                 | atom of int
type prethm = preterm list * preterm
type 'a array = (int,'a)Binarymap.dict
type parse_result =
     id array * pretype array * pre_vc array * (string * prethm) list

infix !
fun (a ! n) = Binarymap.find (a, n)

fun push (a, item) = Binarymap.insert(a, Binarymap.numItems a, item)

fun convert_pretype (ids : id array) (k, prety, acc : hol_type array) = let
  val result =
      case prety of
        ptv s => mk_vartype s
      | ptop (opnum, arglist) => let
          val {Thy,Name} = ids ! opnum
          val args = map (fn n => acc ! n) arglist
        in
          mk_thy_type { Args = args, Thy = Thy, Tyop = Name }
        end
in
  push(acc, result)
end

fun convert_atom
      (ids : id array, types : hol_type array)
      (k, pre_atom, acc : term array)
  = let
    val result =
        case pre_atom of
          ptm_v (s, tyn) => mk_var(s, types ! tyn)
        | ptm_c (idn, tyn) => let
            val {Thy,Name} = ids ! idn
            val ty = types ! tyn
          in
            mk_thy_const {Thy = Thy, Name = Name, Ty = ty}
          end
  in
    push(acc, result)
  end

fun convert_term (atoms : term array, pre_term) = let
  fun c t = convert_term(atoms, t)
in
  case pre_term of
    app(t1, t2) => mk_comb(c t1, c t2)
  | abs(an, t) => mk_abs(atoms ! an, c t)
  | atom i => atoms ! i
end

fun convert_thm (atoms : term array, (h,c)) = let
  val hyps = map (fn pt => convert_term (atoms, pt)) h
  val c_t = convert_term (atoms, c)
in
  mk_thm(hyps, c_t)
end

fun convert_prethms (ids, types, atoms, named_ths) = let
  val types = Binarymap.foldl (convert_pretype ids)
                              (Binarymap.mkDict Int.compare)
                              types
  val atoms = Binarymap.foldl (convert_atom (ids, types))
                              (Binarymap.mkDict Int.compare)
                              atoms
in
  map (fn (s, pth) => (s, convert_thm(atoms, pth))) named_ths 
end




end;
