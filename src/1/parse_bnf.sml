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

fun list_mk_prod [] = constty (one_ty())
  | list_mk_prod (bty::rest) =
    List.foldl (fn (ty1, ty2) => mk_prod ty2 ty1) bty rest

fun dest_constty (constty ty) = SOME ty
  | dest_constty _ = NONE

fun parse_one_pty fmap nm pty =
    case pty of
        dVartype s => constty (mk_vartype s)
      | dAQ ty => constty ty
      | dTyop{Thy=SOME thy,Tyop,Args} =>
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
        let
          val bnfs = map (parse_one_constructor fmap nm) cs
        in
          case bnfs of
              [] => raise Fail "parse_bnf: no constructors"
            | b::rest =>
              (nm, List.foldl (fn (ty1, ty2) => mk_sum ty2 ty1) b rest)
        end

fun parse2ftor asts =
    let
      open ParseDatatype
      val names = map fst asts
      val fmap = Symtab.make (map (fn n => (n,mutrec_var n)) names)
    in
      map (parse_one_ast fmap) asts
    end

end
