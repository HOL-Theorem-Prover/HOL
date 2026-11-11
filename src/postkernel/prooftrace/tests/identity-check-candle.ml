let n = mk_comb (mk_const ("~", []), mk_const ("T", []));;
let th = load_th "identity_negation$NEGATION";;
if length (hyp th) = 1 && aconv (hd (hyp th)) n && aconv (concl th) n
then print_endline "IDENTITY_NEGATION_CANDLE_EXACT"
else failwith "wrong NOT_INTRO negation sequent";;
