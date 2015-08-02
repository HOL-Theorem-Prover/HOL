let l = input_line stdin;;
let t = Hl_parser.parse_term l;;
Hh_write.write_atp_proof "testo.p" ([Bool.tRUTH; Bool.bOOL_CASES_AX], ["TRUTH"; "BOOL_CASES"]) "conj" t;;
