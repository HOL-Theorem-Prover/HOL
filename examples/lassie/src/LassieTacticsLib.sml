structure LassieTacticsLib =
struct

  open LassieUtilsLib;

(* Exception to be raised if no valid pattern can be found *)
exception PATGENERROR of string;

(* Turn string sl into a "pattern" for Q tactics *)
fun mk_tm_quote sl :term quotation = [QUOTE (String.concatWith  " " sl)];

(* Utility function, check if pattern p is unique for assumptions asl and
  conclusion tm
  The check is implemented by running qpat_x_assum twice.
  The first call must succeed, and the second fail for the pattern to be unique.
*)
fun is_unique p asl tm =
  let
    (* mp_tac to keep variables of the matched agains assumption in context *)
    val (gls, _) = qpat_x_assum p mp_tac (asl, tm);
    val r =
      let val _ = qpat_x_assum p kall_tac (hd(gls)) in false end
        handle HOL_ERR _ => true;
  in r end
  handle HOL_ERR _ => false;

(* Pattern generation algorithm
  Generates a list of patterns for the pattern sl given as a list of strings.
  Parameter n determines from which index to start replacing variables/values by
  _, asl is the assumption list from the proof and tm the conclusion *)
fun gen_pats sl (n:int) asl tm : string list list=
  (* The initially given pattern must be unique to be generalized *)
  if (is_unique (mk_tm_quote sl) asl tm)
  then
    if (Int.< (n,(List.length sl))) (* check that we can replace a part by _ *)
    then
      let
        val thePat = LassieUtilsLib.list_replace n "_" sl
        val r1 = gen_pats thePat (n+1) asl tm
                handle PATGENERROR s => []
        val r2 = gen_pats sl (n+1) asl tm
                handle PATGENERROR s => []
      in
        r1 @ r2
      end
    else (* List length exceeded, pattern was unique -> return *)
      [sl]
  else (* pattern was not unique -> fail with an error *)
    raise PATGENERROR "Pattern not unique";

(* Takes the nth assumption, generates a most-general pattern from it and uses
   that as input to ttac *)
fun get_tac (n:int) (ttac:term quotation -> tactic) : tactic =
  fn (g as (asl, tm)) =>
    let
      val theAsm = List.nth (asl, n)
      val strList = LassieUtilsLib.string_split (term_to_string theAsm) #" "
      val finalList = LassieUtilsLib.rejoin_pars strList
      val pats = gen_pats strList n asl tm
      val thePat = hd pats
      val _ = print (
        "\nAssumption " ^ (Int.toString n) ^ " can be obtained with pattern "
        ^ (String.concatWith " " thePat) ^ "\n"
        ^ "using the tactic qpat_x_assum " ^ (String.concatWith " " thePat)
        ^ "ttac\n");
      val theQuote = (mk_tm_quote (hd pats)) (* TODO: Find good heuristic for picking a quotation *)
    in
      ttac theQuote g
    end;

rpt strip_tac
get_tac 0 (fn p => qpat_x_assum p mp_tac)

(*
val quot_ls = ["f", "a", "b"];
val tmquot_test :Term.term bossLib.quotation = mk_tm_quote quot_ls;
val asms = [``(f:'a -> 'b -> bool) a b``, ``(g:'a -> 'b -> bool) a c``];
val gl = ``T``;

val (r,_) = qpat_x_assum tmquot_test kall_tac (asms, gl);
val (r, _) = qpat_x_assum tmquot_test kall_tac (hd r);


gen_pats ["f", "a", "b"] 0 asms ``T``;

g `f a b /\ g a b==> T`
rpt strip_tac

get_tac 0 (fn (t) => qpat_x_assum (mk_tm_quote (string_split (term_to_string t) #" ")) mp_tac)

get 0 (fn tm =>
        (fn g as (asl, gl) =>
          let
                val pat = gen_pat (string_split (term_to_string tm) #" ") 0 asl gl;
                val _ = map (map print) pat;
              in qpat_x_assum (mk_tm_quote (hd pat)) mp_tac g end))
*)
end
