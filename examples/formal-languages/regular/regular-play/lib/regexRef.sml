open regexpMatch;
(* /opt/hol_bir/tools/Holmake/regexpMatch.sml *)

structure regexRef :> regex =
struct

  open regexType;

(*
  datatype regexp
    = Epsilon
    | Symbs of char Binaryset.set
    | Not of regexp
    | Sum of regexp * regexp
    | And of regexp * regexp
    | Dot of regexp * regexp
    | Star of regexp

  val empty_cset : char Binaryset.set
  val univ_cset : char Binaryset.set
  val pred_to_set : (char -> bool) -> char Binaryset.set

  structure POSIX : sig
    val alnum_set  : char Binaryset.set
    val alpha_set  : char Binaryset.set
    val ascii_set  : char Binaryset.set
    val blank_set  : char Binaryset.set
    val cntrl_set  : char Binaryset.set
    val digit_set  : char Binaryset.set
    val graph_set  : char Binaryset.set
    val lower_set  : char Binaryset.set
    val print_set  : char Binaryset.set
    val punct_set  : char Binaryset.set
    val space_set  : char Binaryset.set
    val upper_set  : char Binaryset.set
    val xdigit_set : char Binaryset.set
    val word_set   : char Binaryset.set
  end

  val regexp_compare : regexp * regexp -> order
  val regexpEqual : regexp -> regexp -> bool

  val regexp_to_dfa_arrays
      : regexp -> {delta : int vector vector,
                   start : int,
                   final : bool vector}

  val match : regexp -> string -> bool

*)



  fun mapToRegRef r =
        case r of
            Eps        => regexpMatch.Epsilon
          | Sym c      => regexpMatch.Symbs (pred_to_set (fn x => x = c))
          | Alt (p, q) => regexpMatch.Sum (mapToRegRef p, mapToRegRef q)
          | Seq (p, q) => regexpMatch.Dot (mapToRegRef p, mapToRegRef q)
          | Rep r      => regexpMatch.Star (mapToRegRef r)


  fun match (r:Reg) (s:string) = regexpMatch.match (mapToRegRef r) s;


end
