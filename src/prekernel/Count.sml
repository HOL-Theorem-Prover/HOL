structure Count :> Count =
struct

(*---------------------------------------------------------------------------*
 * Support for monitoring how many theorems (and of what kind) are proved    *
 * in a session. The numbers returned are not "secure", since the counter    *
 * manipulation routines are visible to all.                                 *
 *---------------------------------------------------------------------------*)

val counting = ref false;
fun counting_thms b = (counting := b);
val inc = Portable.inc


datatype rule = Assume | Refl | Beta | Subst | Abs | Disch | Mp | InstType
              | MkComb | ApTerm | ApThm | Alpha
              | Sym | Trans | EqMp | EqImpRule | Inst
              | Spec | Gen
              | Exists | Choose
              | Conj | Conjunct1 | Conjunct2
              | Disj1 | Disj2 | DisjCases
              | NotIntro | NotElim | Ccontr
              | GenAbs
              | Definition  | Axiom | Disk | Oracle;

val count = {ASSUME     = ref 0, REFL = ref 0,
             BETA_CONV  = ref 0, SUBST = ref 0,
             ABS        = ref 0, DISCH = ref 0,
             MP         = ref 0, INST_TYPE  = ref 0,
             MK_COMB    = ref 0, AP_TERM = ref 0,
             AP_THM     = ref 0, ALPHA = ref 0,
             SYM = ref 0,
             TRANS      = ref 0, EQ_MP = ref 0,
             EQ_IMP_RULE = ref 0, INST = ref 0,
             SPEC       = ref 0, GEN = ref 0,
             EXISTS     = ref 0, CHOOSE = ref 0,
             CONJ       = ref 0,
             CONJUNCT1  = ref 0, CONJUNCT2 = ref 0,
             DISJ1      = ref 0, DISJ2 = ref 0,
             DISJ_CASES = ref 0, NOT_INTRO = ref 0,
             NOT_ELIM   = ref 0, CCONTR = ref 0,
             GEN_ABS    = ref 0,
             DEFINITION = ref 0,
             AXIOM      = ref 0, FROM_DISK  = ref 0,
             ORACLE     = ref 0,
             TOTAL      = ref 0};

fun inc_count R =
  if !counting
  then (case R of
         Assume     => inc (#ASSUME count)
       | Refl       => inc (#REFL count)
       | Beta       => inc (#BETA_CONV count)
       | Subst      => inc (#SUBST count)
       | Abs        => inc (#ABS count)
       | Disch      => inc (#DISCH count)
       | Mp         => inc (#MP count)
       | InstType   => inc (#INST_TYPE count)
       | MkComb     => inc (#MK_COMB count)
       | ApTerm     => inc (#AP_TERM count)
       | ApThm      => inc (#AP_THM count)
       | Alpha      => inc (#ALPHA count)
       | Sym        => inc (#SYM count)
       | Trans      => inc (#TRANS count)
       | EqMp       => inc (#EQ_MP count)
       | EqImpRule  => inc (#EQ_IMP_RULE count)
       | Inst       => inc (#INST count)
       | Spec       => inc (#SPEC count)
       | Gen        => inc (#GEN count)
       | Exists     => inc (#EXISTS count)
       | Choose     => inc (#CHOOSE count)
       | Conj       => inc (#CONJ count)
       | Conjunct1  => inc (#CONJUNCT1 count)
       | Conjunct2  => inc (#CONJUNCT2 count)
       | Disj1      => inc (#DISJ1 count)
       | Disj2      => inc (#DISJ2 count)
       | DisjCases  => inc (#DISJ_CASES count)
       | NotIntro   => inc (#NOT_INTRO count)
       | NotElim    => inc (#NOT_ELIM count)
       | Ccontr     => inc (#CCONTR count)
       | GenAbs     => inc (#GEN_ABS count)
       | Definition => inc (#DEFINITION count)
       | Axiom      => inc (#AXIOM count)
       | Disk       => inc (#FROM_DISK count)
       | Oracle     => inc (#ORACLE count))
  else ();


local fun zero (r as ref _) = (r := 0)
in
fun reset_thm_count() =
    (zero (#ASSUME count);
     zero (#REFL count);
     zero (#BETA_CONV count);
     zero (#SUBST count);
     zero (#ABS count);
     zero (#DISCH count);
     zero (#MP count);
     zero (#INST_TYPE count);
     zero (#MK_COMB count);
     zero (#AP_TERM count);
     zero (#AP_THM count);
     zero (#ALPHA count);
     zero (#SYM count);
     zero (#TRANS count);
     zero (#EQ_MP count);
     zero (#EQ_IMP_RULE count);
     zero (#INST count);
     zero (#SPEC count);
     zero (#GEN count);
     zero (#EXISTS count);
     zero (#CHOOSE count);
     zero (#CONJ count);
     zero (#CONJUNCT1 count);
     zero (#CONJUNCT2 count);
     zero (#DISJ1 count);
     zero (#DISJ2 count);
     zero (#DISJ_CASES count);
     zero (#NOT_INTRO count);
     zero (#NOT_ELIM count);
     zero (#CCONTR count);
     zero (#GEN_ABS count);
     zero (#DEFINITION count);
     zero (#AXIOM count);
     zero (#FROM_DISK count);
     zero (#ORACLE count));
end;


fun prims() =
   !(#ASSUME count) + !(#REFL count) + !(#BETA_CONV count) +
   !(#SUBST count) + !(#ABS count) + !(#DISCH count) +
   !(#MP count) + !(#INST_TYPE count) + !(#MK_COMB count) +
   !(#AP_TERM count) + !(#AP_THM count) + !(#ALPHA count) +
   !(#SYM count) + !(#TRANS count) +
   !(#EQ_MP count) + !(#EQ_IMP_RULE count) +
   !(#INST count) + !(#SPEC count) + !(#GEN count) +
   !(#EXISTS count) + !(#CHOOSE count) +
   !(#CONJ count) + !(#CONJUNCT1 count) + !(#CONJUNCT2 count) +
   !(#DISJ1 count) + !(#DISJ2 count) + !(#DISJ_CASES count) +
   !(#NOT_INTRO count) + !(#NOT_ELIM count) + !(#CCONTR count) +
   !(#GEN_ABS count);

fun defns()     = !(#DEFINITION count)
fun axioms()    = !(#AXIOM count)
fun from_disk() = !(#FROM_DISK count)
fun oracles()   = !(#ORACLE count);


fun total() =
  prims() + defns() + axioms() + from_disk() + oracles();

fun thm_count() =
 {ASSUME     = !(#ASSUME count),    REFL       = !(#REFL count),
  BETA_CONV  = !(#BETA_CONV count), SUBST      = !(#SUBST count),
  ABS        = !(#ABS count),       DISCH      = !(#DISCH count),
  MP         = !(#MP count),        INST_TYPE  = !(#INST_TYPE count),
  MK_COMB = !(#MK_COMB count),      AP_TERM = !(#AP_TERM count),
  AP_THM = !(#AP_THM count),        ALPHA = !(#ALPHA count),
  SYM = !(#SYM count), TRANS = !(#TRANS count),
  EQ_MP = !(#EQ_MP count),          EQ_IMP_RULE = !(#EQ_IMP_RULE count),
  INST = !(#INST count),            SPEC = !(#SPEC count),
  GEN = !(#GEN count),  EXISTS = !(#EXISTS count), CHOOSE = !(#CHOOSE count),
  CONJ = !(#CONJ count),  CONJUNCT1 = !(#CONJUNCT1 count),
  CONJUNCT2 = !(#CONJUNCT2 count),  DISJ1 = !(#DISJ1 count),
  DISJ2 = !(#DISJ2 count),  DISJ_CASES = !(#DISJ_CASES count),
  NOT_INTRO = !(#NOT_INTRO count),  NOT_ELIM = !(#NOT_ELIM count),
  CCONTR = !(#CCONTR count), GEN_ABS = !(#GEN_ABS count),
  definition = !(#DEFINITION count),  axiom = !(#AXIOM count),
  from_disk = !(#FROM_DISK count),    oracle = !(#ORACLE count),
  total  = total() }


type meter = {axioms:int, defns:int, oracles:int, disk:int, prims:int}

fun mk_meter() =
 (counting_thms true;
  {prims=prims(), defns=defns(), axioms=axioms(),
   disk=from_disk(), oracles = oracles()});


fun read {prims=p0,defns=d0,axioms=a0,disk=f0,oracles=or0} =
  let val {prims,defns,axioms,disk,oracles} = mk_meter()
  in
    {prims = prims-p0,  defns = defns-d0, axioms = axioms-a0,
      disk = disk-f0, oracles = oracles-or0}
  end;

fun report {prims,defns,axioms,disk,oracles} =
  (Lib.say ("Axioms asserted: " ^Lib.int_to_string axioms^".\n");
   Lib.say ("Definitions made: " ^Lib.int_to_string defns^".\n");
   Lib.say ("Oracle invocations: " ^Lib.int_to_string oracles^".\n");
   Lib.say ("Theorems loaded from disk: "^Lib.int_to_string disk^".\n");
   Lib.say ("HOL primitive inference steps: "^Lib.int_to_string prims^".\n");
   Lib.say ("Total: "
         ^Lib.int_to_string (prims + defns + axioms + oracles + disk)^".\n"));


fun apply f x =
  let val m = mk_meter()
      val res = Lib.time f x handle e => (report (read m); raise e)
   in
     report(read m);  res
   end

end;
