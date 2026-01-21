structure parse_bnf :> parse_bnf =
struct

open bnfBase_dtype ParseDatatype
fun one_ty() = mk_thy_type {Thy = "one", Tyop = "one", Args = []}

fun isExisting_pty pty =
    case pty of
        dVartype _ => true
      | dAQ _ => true
      | dTyop{Thy,Tyop,Args} => isSome Thy andalso List.all isExisting_pty Args

fun omap f [] = SOME []
  | omap f (x::xs) =
    case f x of
        NONE => NONE
      | SOME y =>
        case omap f xs of
            NONE => NONE
          | SOME ys => SOME(y::ys)

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

fun mk_sum bty1 bty2 = ftor({Thy="sum", Name="sum"}, [bty1,bty2])
fun mk_prod bty1 bty2 = ftor({Thy="pair", Name="prod"}, [bty1,bty2])

fun list_mk_prod [] = constty (one_ty())
  | list_mk_prod (bty::rest) = rev_itlist mk_prod rest bty

fun buildfold f args st0 = let
  fun recurse Vs st args =
    case args of
        [] => (st,List.rev Vs)
      | a::rest => let val (st',v) = f st0 a
                   in
                     recurse (v::Vs) st' rest
                   end
in
  recurse [] st0 args
end

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
    val multiplicands = map (parse_one_pty fmap nm) ptys
    val parse_one

fun parse_one_ast fmap (nm, dtyform) =
    case dtyform of
        Record flds =>
        parse_one_ast fmap (nm, Constructors [(nm, map snd flds)])
      | Constructors cs =>
        let
          val bnfs = map (parse_one_constructor nm fmap) cs
          val sum_bnf =
              case bnfs of
                  [] => raise Fail "parse_bnf: no constructors"
                | b::rest => rev_itlist mk_sum rest b
          val fmap' =
        in
          case btys of
            | b::bs => (fmap', )
        end

fun parse2ftor asts =
    let
      open ParseDatatype
      val names = map fst asts
      val fmap0 = Symtab.make (map (fn n => (n,mutrec_var n)) names)
    in
      buildfold parse_one_ast asts fmap0
    end

end
