structure parse_bnf :> parse_bnf =
struct

open bnfBase_dtype ParseDatatype HolKernel

fun one_ty() = mk_thy_type {Thy = "one", Tyop = "one", Args = []}

fun isExisting_pty pty =
    case pty of
        dVartype _ => true
      | dAQ _ => true
      | dTyop{Thy,Tyop,Args} => isSome Thy andalso List.all isExisting_pty Args


fun omap f l =
    let
      fun mpk l A =
          case l of
              [] => SOME (List.rev A)
            | h::t =>
              case f h of
                  NONE => NONE
                | SOME fx => mpk t (fx::A)
    in
      mpk l []
    end

fun build_existing pty =
    case pty of
        dVartype s => SOME (mk_vartype s)
      | dAQ ty => SOME ty
      | dTyop {Tyop,Thy,Args} =>
        case Thy of
            NONE => NONE
          | SOME thy =>
            case omap build_existing Args of
                NONE => NONE
              | SOME args =>
                SOME (mk_thy_type {Tyop = Tyop, Thy = thy, Args = args})

fun mk_bintyop thy tyop bty1 bty2 =
    case (bty1,bty2) of
        (constty ty1, constty ty2) =>
        constty (
          Type.mk_thy_type{Thy = thy, Tyop = tyop, Args = [ty1,ty2]}
        )
      | _ => ftor({Thy=thy, Name=tyop}, [bty1,bty2])

val mk_sum = mk_bintyop "sum" "sum"
val mk_prod = mk_bintyop "pair" "prod"

(* both of these nest to the right, which is how the shape is read back:
   a sum of products is taken apart along its right spine *)
fun list_mk_prod [] = constty (one_ty())
  | list_mk_prod [bty] = bty
  | list_mk_prod (bty::rest) = mk_prod bty (list_mk_prod rest)

fun list_mk_sum [bty] = bty
  | list_mk_sum (bty::rest) = mk_sum bty (list_mk_sum rest)
  | list_mk_sum [] = raise Fail "parse_bnf: no constructors"

fun dest_constty (constty ty) = SOME ty
  | dest_constty _ = NONE

fun parse_one_pty fmap nm pty =
    case pty of
        dVartype s => constty (mk_vartype s)
      | dAQ ty => constty ty
      | dTyop{Thy=SOME thy,Tyop,Args} =>
        (* a specification may name one of its own types the way any
           other type is named — `num = C10 num$num | C12 scratch$num`
           says both the numbers and the type being defined — and the
           qualified name is then the member, not a type that exists *)
        if thy = current_theory() andalso
           (Tyop = nm orelse isSome (Symtab.lookup fmap Tyop))
        then parse_one_pty fmap nm (dTyop{Thy = NONE, Tyop = Tyop,
                                          Args = Args})
        else
        let val args = map (parse_one_pty fmap nm) Args
        in
          case omap dest_constty args of
              NONE => ftor({Thy=thy,Name=Tyop}, args)
            | SOME tys => constty (mk_thy_type {Thy=thy,Tyop=Tyop,Args = tys})
        end
      | dTyop{Thy=NONE,Tyop,Args} =>
        if Tyop = nm then the_arg
        else
          case Symtab.lookup fmap Tyop of
              NONE => raise Fail "new user type not in symtab"
            | SOME bnf => bnf

fun parse_one_constructor fmap nm ((* constructor name *) _, ptys) =
    let
      val multiplicands = map (parse_one_pty fmap nm) ptys
    in
      list_mk_prod multiplicands
    end


fun parse_one_ast fmap (nm, dtyform) =
    case dtyform of
        Record flds =>
        parse_one_ast fmap (nm, Constructors [(nm, map snd flds)])
      | Constructors cs =>
        (nm, list_mk_sum (map (parse_one_constructor fmap nm) cs))

fun parse2ftor asts =
    let
      open ParseDatatype
      val names = map fst asts
      val fmap = Symtab.make (map (fn n => (n,mutrec_var n)) names)
    in
      map (parse_one_ast fmap) asts
    end

end
