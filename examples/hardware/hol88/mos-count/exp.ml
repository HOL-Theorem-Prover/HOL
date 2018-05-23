new_theory `exp`;;

let REV_EXP = new_prim_rec_definition (
	`REV_EXP`,
	"(REV_EXP 0 n = 1) /\
	 (REV_EXP (SUC m) n = (n * (REV_EXP m n)))");;

let EXP = new_infix_definition (
	`EXP`,
	"$EXP n m = REV_EXP m n");;

let EXP = prove_thm (
	`EXP`,
	"(m EXP 0 = 1) /\ (m EXP (SUC n) = m * (m EXP n))",
	REWRITE_TAC [EXP;REV_EXP]);;

close_theory ();;
