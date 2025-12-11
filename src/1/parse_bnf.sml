structure parse_bnf :> parse_bnf =
struct

open bnfBase_dtype ParseDatatype
val one_ty = mk_thy_type {Thy = "one", Tyop = "one", Args = []}

fun isExisting_pty pty =
    case pty of
        dVartype _ => true
      | dAQ _ => true
      | dTyop{Thy,Tyop,Args} => isSome Thy andalso List.all isExisting_pty Args

fun build_existing pty =
    case pty of
        dVartype s => mk_vartype s
      | dAQ ty => ty
      | dTyop {Tyop,Thy,Args} =>
        mk_thy_type {Tyop = Tyop, Thy = valOf Thy,
                     Args = map build_existing Args}

fun mk_sum bty1 bty2 = ftor({Thy="sum", Name="sum"}, [bty1,bty2])

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

fun parse_one_constructor fmap (cnm, ptys) =
    raise Fail "Unimplemented"

fun parse_one_ast fmap (nm, dtyform) =
    case dtyform of
        Record flds =>
        parse_one_ast fmap (nm, Constructors [("record_" ^ nm, map snd flds)])
      | Constructors cs =>
        let
          val (fmap',btys) = buildfold parse_one_constructor cs fmap
        in
          case btys of
              [] => raise Fail "parse_bnf: no constructors"
            | b::bs => (fmap', rev_itlist mk_sum bs b)
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
