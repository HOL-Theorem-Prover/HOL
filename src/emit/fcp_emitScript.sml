open HolKernel boolLib bossLib Parse;
open EmitML fcpTheory fcpLib;
open num_emitTheory;

val _ = new_theory "fcp_emit";

val FCPi_def = Define `FCPi (f, (:'b)) = ($FCP f):'a ** 'b`;

val mk_fcp_def = Define `mk_fcp = FCPi`;

val index_comp = REWRITE_RULE [GSYM FCPi_def] index_comp;
val fcp_subst_comp = REWRITE_RULE [GSYM FCPi_def] fcp_subst_comp;

val _ = new_constant("ITSELF", ``:num -> 'a itself``);

val _ = new_constant("SUMi", ``:'a itself # 'b itself -> 'c itself``);
val _ = new_constant("MULi", ``:'a itself # 'b itself -> 'c itself``);
val _ = new_constant("EXPi", ``:'a itself # 'b itself -> 'c itself``);

val SUMi  = new_axiom("SUMi", ``SUMi (ITSELF a, ITSELF b) = ITSELF (a + b)``);
val MULi  = new_axiom("MULi", ``MULi (ITSELF a, ITSELF b) = ITSELF (a * b)``);
val EXPi  = new_axiom("EXPi", ``EXPi (ITSELF a, ITSELF b) = ITSELF (a ** b)``);

val dimindexi = new_axiom("dimindexi", ``dimindex (ITSELF a) = a``);

val _ = type_pp.pp_array_types := false

val defs = [SUMi, MULi, EXPi, dimindexi, mk_fcp_def, index_comp, fcp_subst_comp]

val _ = eSML "fcp"
  ([OPEN ["num"],
    MLSIG "type num = numML.num",
    DATATYPE(`itself = ITSELF of num`),
    ABSDATATYPE (["'a","'b"], `cart = FCPi of (num -> 'a) # 'b itself`),
    EQDATATYPE (["'a"],`bit0 = BIT0A of 'a | BIT0B of 'a`),
    EQDATATYPE (["'a"],`bit1 = BIT1A of 'a | BIT1B of 'a | BIT1C`)] @
   map DEFN defs)

val _ = eCAML "fcp"
 (MLSIGSTRUCT ["type num = NumML.num"]
   @ OPEN ["num"]
  :: DATATYPE(`itself = ITSELF of num`)
  :: ABSDATATYPE (["'a","'b"], `cart = FCPi of (num -> 'a) # 'b itself`)
  :: EQDATATYPE (["'a"],`bit0 = BIT0A of 'a | BIT0B of 'a`)
  :: EQDATATYPE (["'a"],`bit1 = BIT1A of 'a | BIT1B of 'a | BIT1C`)
  :: map (DEFN o REWRITE_RULE [GSYM FCPi_def, FUN_EQ_THM]) defs)

val _ = export_theory ();
