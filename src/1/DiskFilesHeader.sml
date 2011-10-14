structure DiskFilesHeader :> DiskFilesHeader =
struct

open HolKernel
infixr 3 ==>

type id = {Thy:string,Name:string}

datatype prekind = pkv of string * int | pkty of int | pkarr of int * int
datatype pretype = ptv of string * int | ptc of int * int
                 | ptapp of int * int | ptabs of int * int
                 | ptuni of int * int | ptexi of int * int
datatype pre_vc = ptm_v of string * int | ptm_c of int * int
datatype preterm = app of preterm * preterm | abs of int * preterm
                 | tyapp of preterm * int | tyabs of int * preterm
                 | atom of int
type prethm = preterm list * preterm
type 'a array = (int,'a)Binarymap.dict
type parse_result =
     id array * prekind array * pretype array * pre_vc array * (string * prethm) list

infix !
fun (a ! n) = Binarymap.find (a, n)

fun push (a, item) = Binarymap.insert(a, Binarymap.numItems a, item)

fun convert_prekind (ids : id array) (k, prekd, acc : kind array) = let
  val result =
      case prekd of
        pkv (s,rk) => mk_var_kind (s,rk)
      | pkty rk => mk_type_kind rk
      | pkarr (dom,rng) => (acc ! dom) ==> (acc ! rng)
in
  push(acc, result)
end

fun convert_pretype (ids : id array, kinds : kind array) (k, prety, acc : hol_type array) = let
  val result =
      case prety of
        ptv (s, kindnum) => mk_var_type (s, kinds ! kindnum)
      | ptc (opnum, kindnum) => let
          val {Thy,Name} = ids ! opnum
          val Kind = kinds ! kindnum
        in
          mk_thy_con_type { Thy = Thy, Tyop = Name, Kind = Kind }
        end
      | ptapp (opr, arg)  => mk_app_type(acc ! opr, acc ! arg)
      | ptabs (bvar,body) => mk_abs_type(acc ! bvar, acc ! body)
      | ptuni (bvar,body) => mk_univ_type(acc ! bvar, acc ! body)
      | ptexi (bvar,body) => mk_exist_type(acc ! bvar, acc ! body)
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

fun convert_term (atoms : term array, types : hol_type array, pre_term) = let
  fun c t = convert_term(atoms, types, t)
in
  case pre_term of
    app(t1, t2) => mk_comb(c t1, c t2)
  | abs(an, t) => mk_abs(atoms ! an, c t)
  | tyapp(t, tyn) => mk_tycomb(c t, types ! tyn)
  | tyabs(tyn, t) => mk_tyabs(types ! tyn, c t)
  | atom i => atoms ! i
end

fun convert_thm (atoms : term array, types : hol_type array, (h,c)) = let
  val hyps = map (fn pt => convert_term (atoms, types, pt)) h
  val c_t = convert_term (atoms, types, c)
in
  mk_thm(hyps, c_t)
end

fun convert_prethms (ids, kinds, types, atoms, named_ths) = let
  val kinds = Binarymap.foldl (convert_prekind ids)
                              (Binarymap.mkDict Int.compare)
                              kinds
  val types = Binarymap.foldl (convert_pretype (ids, kinds))
                              (Binarymap.mkDict Int.compare)
                              types
  val atoms = Binarymap.foldl (convert_atom (ids, types))
                              (Binarymap.mkDict Int.compare)
                              atoms
in
  map (fn (s, pth) => (s, convert_thm(atoms, types, pth))) named_ths
end




end;
