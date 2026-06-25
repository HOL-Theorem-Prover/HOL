# HOL Quick Reference

A one-page-style summary of the tactics, rules, conversions, and
support functions that come up most often in day-to-day HOL4 proof.
Names link to their full entry in the
[Reference manual](../Reference/index.html); names shown in plain
type have no separate Reference entry.

## Creating Theories

|  |  |
|---|---|
| \refentry{Theory.new_theory} *name* | creates a new theory |
| \refentry{Theory.export_theory}() | writes theory to disk |
| \refentry{TotalDefn.Define} *term* | function definition |
| \refentry{bossLib.Hol_datatype} *type-dec* | defines a concrete datatype |
| `EquivType.define_equivalence_type` *rec* | type of equivalence classes |
| \refentry{Theory.save_thm}(*name*,*thm*) | stores theorem |
| \refentry{Tactical.prove}(*term*,*tactic*) | proves theorem using tactic |
| \refentry{Tactical.store_thm}(*name*,*term*,*tactic*) | proves and stores theorem |

## Goal Stack Operations

|  |  |
|---|---|
| \refentry{proofManagerLib.g} *term* | starts a new goal |
| \refentry{proofManagerLib.e} *tactic* | applies a tactic to the top goal |
| \refentry{proofManagerLib.b}() | undoes previous expansion |
| \refentry{proofManagerLib.restart}() | undoes all expansions |
| `proofManagerLib.drop`() | abandons the top goal |
| `proofManagerLib.dropn` *int* | abandons a number of goals |
| \refentry{proofManagerLib.p}() | prints the state of the top goal |
| `proofManagerLib.status`() | prints the state of all goals |
| \refentry{proofManagerLib.top_thm}() | returns the last theorem proved |
| \refentry{proofManagerLib.r} *int* | rotates sub-goals |
| `proofManagerLib.R` *int* | rotates proofs |

## Some Basic Tactics

|  |  |
|---|---|
| \refentry{bossLib.Cases} | case analysis on outermost variable |
| \refentry{bossLib.Cases_on} *term* | case analysis on given term |
| \refentry{bossLib.Induct} | induct on outermost variable |
| \refentry{bossLib.Induct_on} *term* | induct on given term |
| \refentry{Tactic.STRIP_TAC} | splits on outermost connective |
| \refentry{Tactic.EXISTS_TAC} *term* | gives witness for existential |
| \refentry{Tactic.SELECT_ELIM_TAC} | eliminates Hilbert choice operator |
| \refentry{Tactic.EQ_TAC} | reduces boolean equality to implication |
| \refentry{Tactic.ASSUME_TAC} *thm* | adds an assumption |
| \refentry{Tactic.DISJ1_TAC} | selects left disjunct |
| \refentry{Tactic.DISJ2_TAC} | selects right disjunct |
| \refentry{bossLib.SPOSE_NOT_THEN} *thm-tactic* | starts proof by contradiction |

## Some Basic Tacticals

|  |  |
|---|---|
| \refentry{Tactical.THEN} | applies tactics in sequence |
| \refentry{Tactical.THENL} | applies list of tactics to sub-goals |
| \refentry{Tactical.THEN1} | applies the second tactic to first sub-goal |
| \refentry{Tactical.ORELSE} | applies second tactic only if the first fails |
| \refentry{Tactical.REVERSE} | reverses the order of sub-goals |
| \refentry{Tactical.ALL_TAC} | leaves the goal unchanged |
| \refentry{Tactical.TRY} | do nothing if the tactic fails |
| \refentry{Tactical.REPEAT} | repeat a tactic until it fails |
| \refentry{Tactic.NTAC} | apply a tactic some number of times |
| \refentry{Tactical.MAP_EVERY} | apply a tactic using theorems in a list |

## Using Assumptions

|  |  |
|---|---|
| \refentry{bossLib.by}(*term*,*tactic*) | add assumption using proof |
| \refentry{Tactical.ASSUM_LIST} [*thms*] | adds list of theorems |
| \refentry{Tactical.POP_ASSUM} *thm-tactic* | use first assumption |
| \refentry{Tactical.POP_ASSUM_LIST} *thms-tactic* | use all assumptions |
| \refentry{Tactical.PAT_ASSUM} *thm-tactic* | use matching assumption |
| \refentry{Tactical.FIRST_X_ASSUM} *thm-tactic* | use first successful assumption |
| \refentry{Tactic.STRIP_ASSUME_TAC} *thm* | split and add assumption |
| \refentry{Tactic.WEAKEN_TAC} *term-pred* | remove assumptions |
| \refentry{Tactic.RULE_ASSUM_TAC} | apply rule to assumptions |
| \refentry{Tactic.IMP_RES_TAC} *thm* | resolve *thm* using assumptions |
| \refentry{Tactic.RES_TAC} | mutually resolve assumptions |
| \refentry{Q.ABBREV_TAC} | abbreviate goal's sub-term |

## Decision Procedures

|  |  |
|---|---|
| \refentry{tautLib.TAUT_TAC} | tautology checker |
| \refentry{bossLib.DECIDE_TAC} | above, plus linear arithmetic |
| \refentry{mesonLib.MESON_TAC} [*thms*] | first-order prover |
| \refentry{BasicProvers.PROVE_TAC} [*thms*] | uses Meson |
| `metisLib.METIS_TAC` [*thms*] | new first-order prover |
| \refentry{bossLib.EVAL_TAC} | evaluation tactic |
| `numLib.ARITH_TAC` | for Presburger arithmetic |
| `intLib.ARITH_TAC` | uses Omega test |
| `intLib.COOPER_TAC` | Cooper's algorithm |
| `realLib.REAL_ARITH_TAC` | |

## Term Rewriting Tactics

|  |  |
|---|---|
| \refentry{Rewrite.GEN_REWRITE_TAC} *conv-op rws* [*thms*] | used to construct bespoke rewriting tactics; applies *conv-op* to the rewriting conversion |
| \refentry{Rewrite.PURE_REWRITE_TAC} [*thms*] | rewrites goal only using the given theorems |
| \refentry{Rewrite.PURE_ONCE_REWRITE_TAC} [*thms*] | as above but executes just a single rewrite |
| \refentry{Rewrite.REWRITE_TAC} [*thms*] | rewrites goal using theorems and some basic rewrites |
| \refentry{Rewrite.ONCE_REWRITE_TAC} [*thms*] | as above but executes just a single rewrite |
| \refentry{Rewrite.PURE_ASM_REWRITE_TAC} [*thms*] | rewrites goal only using assumptions and theorems |
| \refentry{Rewrite.PURE_ONCE_ASM_REWRITE_TAC} [*thms*] | as above but executes just a single rewrite |
| \refentry{Rewrite.ASM_REWRITE_TAC} [*thms*] | rewrites using assumptions, theorems and basic rewrites |
| \refentry{Rewrite.ONCE_ASM_REWRITE_TAC} [*thms*] | as above but executes just a single rewrite |

## Simplification Tactics

|  |  |
|---|---|
| \refentry{simpLib.SIMP_TAC} *simpset* [*thms*] | simplifies goal using theorems and simplification set |
| \refentry{simpLib.ASM_SIMP_TAC} *simpset* [*thms*] | as above but also uses the assumptions |
| \refentry{simpLib.FULL_SIMP_TAC} *simpset* [*thms*] | simplifies the goal and all the assumptions |
| \refentry{BasicProvers.RW_TAC} *simpset* [*thms*] | more aggressive simplifier; uses type information & case splits |
| \refentry{BasicProvers.SRW_TAC} [*ssfrags*][*thms*] | as above but uses a list of *simpset* fragments |
| \refentry{simpLib.rewrites} [*thms*] | constructs a rewrite fragment |
| \refentry{simpLib.mk_simpset} [*ssfrag*] | constructs a *simpset* from fragments |
| `simpLib.++`(*simpset*,*ssfrag*) | adds a fragment to a *simpset* |
| `simpLib.&&`(*simpset*,[*thms*]) | adds rewrites to a *simpset* |
| \refentry{simpLib.AC} *thm* *thm* | constructs tagged theorem to enable AC simplification |

## Simplification Sets and Fragments

|  |  |
|---|---|
| \refentry{pureSimps.pure_ss} | minimal *simpset* for conditional rewriting |
| \refentry{boolSimps.bool_ss} | propositional and first-order logic simplifications, plus beta-conversion |
| \refentry{bossLib.std_ss} | as above + pairs, options, sums, numeral evaluation & eta reduction |
| \refentry{bossLib.arith_ss} | as above + arithmetic rewrites and decision procedure for linear arithmetic |
| \refentry{bossLib.list_ss} | a version of the above for the theory of lists |
| `realLib.real_ss` | adds some real number evaluation and rewrites to the arithmetic *simpset* |
| \refentry{bossLib.srw_ss}() | returns `stateful` *simpset*; has type theorems from loaded theories |
| \refentry{bossLib.augment_srw_ss} [*ssfrag*] | adds fragments to the `stateful` *simpset* |
| \refentry{BasicProvers.export_rewrites} [*names*] | exports named theorems to the `stateful` *simpset* |

### Simpset fragments

|  |  |
|---|---|
| `boolSimps.CONJ_ss` | congruence rule for conjunction |
| `boolSimps.ETA_ss` | eta conversion |
| `boolSimps.LET_ss` | rewrites out `let` terms |
| \refentry{boolSimps.DNF_ss} | converts term to disjunctive-normal-form |
| `pairSimps.PAIR_ss` | rewrites for pairs |
| `optionSimps.OPTION_ss` | rewrites for options |
| `stringSimps.STRING_ss` | rewrites for strings |
| `numSimps.ARITH_ss` | arithmetic rewrites and decision procedure |
| `numSimps.ARITH_AC_ss` | AC fragment for addition and multiplication |
| `numSimps.REDUCE_ss` | reduces ground-term expressions |
| `listSimps.LIST_ss` | rewrites for lists |
| `pred_setSimps.SET_SPEC_ss` | rewrites for set membership |
| `pred_setSimps.PRED_SET_ss` | rewrites for sets |

## Specialize and Generalize Rules

|  |  |
|---|---|
| \refentry{Thm.SPEC} *term* | specializes one variable in the conclusion of a theorem |
| \refentry{Drule.SPECL} [*terms*] | specializes zero or more variables in the conclusion of a theorem |
| \refentry{Drule.SPEC_ALL} | specializes the conclusion of a theorem with its own quantified variables |
| \refentry{Drule.GSPEC} | as above but uses unique variables |
| \refentry{Drule.ISPEC} *term* | specializes theorem, with type instantiation if necessary |
| \refentry{Drule.ISPECL} [*terms*] | specializes theorem zero or more times, with type instantiation if necessary |
| \refentry{Thm.INST} [*term* `\|->` *term*] | instantiates free variables in a theorem |
| \refentry{Thm.GEN} *term* | generalizes the conclusion of a theorem |
| \refentry{Thm.GENL} [*terms*] | generalizes zero or more variables in the conclusion of a theorem |
| \refentry{Drule.GEN_ALL} | generalizes the conclusion of a theorem over its own free variables |

## Some Inference Rules

|  |  |
|---|---|
| \refentry{Conv.CONV_RULE} *conv* | makes an inference rule from a conversion |
| \refentry{Conv.GSYM} *thm* | reverses the first equation(s) encountered in a top-down search |
| \refentry{Drule.NOT_EQ_SYM} *thm* | swaps left-hand and right-hand sides of a negated equation |
| \refentry{Thm.CONJUNCT1} *thm* | extracts left conjunct of theorem |
| \refentry{Thm.CONJUNCT2} *thm* | extracts right conjunct of theorem |
| \refentry{Drule.CONJUNCTS} *thm* | recursively splits conjunctions into a list of conjuncts |
| \refentry{Drule.MATCH_MP} *thm* *thm* | Modus Ponens inference rule with automatic matching |
| \refentry{Thm.EQ_MP} *thm* *thm* | equality version of the Modus Ponens rule |
| \refentry{Thm.EQ_IMP_RULE} *thm* | derives forward and backward implication from equality of boolean terms |

## Some Conversions

|  |  |
|---|---|
| \refentry{bossLib.DECIDE} | prove term using a tautology checker and linear arithmetic |
| \refentry{Rewrite.REWRITE_CONV} [*thms*] | rewrites term using basic rewrites and given theorems |
| \refentry{simpLib.SIMP_CONV} *simpset* [*thms*] | simplifies term using *simpset* and theorems |
| \refentry{computeLib.CBV_CONV} *compset* | call-by-value conversion |
| \refentry{numLib.num_CONV} | equates a non-zero numeral with the form $\mathrm{SUC}\,x$ for some $x$ |
| \refentry{reduceLib.REDUCE_CONV} | evaluates arithmetic and boolean ground expressions |
| \refentry{numLib.SUC_TO_NUMERAL_DEFN_CONV} | translates $\mathrm{SUC}\,x$ equations to use numeral constructors |
| `numLib.EXISTS_LEAST_CONV` | when applied to a term $\exists n.\,P(n)$, returns:<br>$\vdash (\exists n.\,P(n)) = \exists n.\,P(n) \wedge \forall n'.\,n' < n \Rightarrow \neg P(n')$ |
| \refentry{Conv.SYM_CONV} | interchanges the left and right-hand sides of an equation |
| \refentry{Conv.SKOLEM_CONV} | proves the existence of a Skolem function |
| \refentry{Drule.GEN_ALPHA_CONV} | renames the bound variable of an abstraction, quantified term, *etc.* |
| \refentry{Thm.BETA_CONV} | performs a single step of beta-conversion |
| \refentry{Drule.ETA_CONV} | performs a top level eta-conversion |
| \refentry{PairRules.GEN_PALPHA_CONV} | paired variable version of the above |
| \refentry{PairRules.PBETA_CONV} | paired variable version of the above |
| \refentry{PairRules.PETA_CONV} | paired variable version of the above |

## Quantification Conversions

|  |  |
|---|---|
| `Conv.SWAP_VARS_CONV` | swaps two universally quantified variables |
| \refentry{Conv.SWAP_EXISTS_CONV} | swaps two existentially quantified variables |
| `Conv.{NOT\|AND\|OR}_{EXISTS\|FORALL}_CONV` | moves operation inwards through quantifier |
| `Conv.{EXISTS\|FORALL}_{NOT\|AND\|OR\|IMP}_CONV` | moves quantifier inwards through operation |
| `Conv.{LEFT\|RIGHT}_{AND\|OR\|IMP}_{EXISTS\|FORALL}_CONV` | moves quantifier of left/right operand outward |

## Conversion Operations

|  |  |
|---|---|
| \refentry{Conv.DEPTH_CONV} | applies conversion repeatedly to all sub-terms, in bottom-up order |
| \refentry{Conv.REDEPTH_CONV} | applies conversion bottom-up to sub-terms, retraversing changed ones |
| \refentry{Conv.ONCE_DEPTH_CONV} | applies conversion once to the first suitable sub-term in top-down order |
| \refentry{Conv.TOP_DEPTH_CONV} | applies conversion top-down to all sub-terms, retraversing changed ones |
| \refentry{Conv.LAND_CONV} | applies conversion to the left-hand argument of a binary operator |
| \refentry{Conv.RAND_CONV} | applies conversion to the operand of an application |
| \refentry{Conv.RATOR_CONV} | applies conversion to the operator of an application |
| \refentry{Conv.BINOP_CONV} | applies conversion to both arguments of a binary operator |
| `Conv.LHS_CONV` | applies conversion to the left-hand side of an equality |
| `Conv.RHS_CONV` | applies conversion to the right-hand side of an equality |
| \refentry{Conv.STRIP_QUANT_CONV} | applies conversion underneath a quantifier prefix |
| \refentry{Conv.STRIP_BINDER_CONV} | applies conversion underneath a binder prefix |
| \refentry{Conv.FORK_CONV}(*conv*,*conv*) | applies a pair of conversions to the arguments of a binary operator |
| \refentry{Conv.THENC}(*conv*,*conv*) | applies two conversions in sequence |
| \refentry{Conv.ORELSEC}(*conv*,*conv*) | applies the first of two conversions that succeeds |

## Parsing

|  |  |
|---|---|
| `numLib.prefer_num`() | give numerals and operators natural number types by default |
| \refentry{intLib.prefer_int}() | give numerals and operators integer types by default |
| \refentry{Parse.overload_on}(*name*,*term*) | establishes constant as one of the overloading possibilities for a string |
| \refentry{Parse.add_infix}(*name*,*int*,*assoc*) | adds string as infix with given precedence & associativity to grammar |
| \refentry{Parse.set_fixity} *name* *fixity* | allows the fixity of tokens to be updated |
| \refentry{Parse.type_abbrev}(*name*,*type*) | establishes a type abbreviation |
| \refentry{Parse.add_rule} *record* | adds a parsing/printing rule to the global grammar |

## The Database

|  |  |
|---|---|
| \refentry{DB.match} [*names*] *term* | attempt to find matching theorems in the specified theories |
| \refentry{DB.find} *string* | search for theory element by name fragment |
| \refentry{DB.axioms} *name* | all the axioms stored in the named theory |
| \refentry{DB.theorems} *name* | all the theorems stored in the named theory |
| \refentry{DB.definitions} *name* | all the definitions stored in the named theory |
| `DB.export_theory_as_docfiles` *name* | produce *.doc* files for the named theory |
| `DB.html_theory` *name* | produce web-page for the named theory |

## Tracing

|  |  |
|---|---|
| \refentry{Feedback.traces}() | returns a list of registered tracing variables |
| \refentry{Feedback.set_trace} *name* *int* | set a tracing level for a registered trace |
| \refentry{Feedback.reset_trace} *name* | resets a tracing variable to its default value |
| \refentry{Feedback.reset_traces}() | resets all registered tracing variables to their default values |

Some commonly-traced variables (with their value ranges):

|  |  |
|---|---|
| `"Rewrite"` | tracing variable for term rewriting (0–1) |
| `"Subgoal number"` | number of printed sub-goals (10–10000) |
| `"meson"` | for the first-order prover (1–2) |
| `"numeral types"` | show types of numerals (0–1) |
| `"simplifier"` | for the simplifier (0–7) |
| `"types"` | printing of types (0–2) |

|  |  |
|---|---|
| \refentry{Globals.show_types} := *bool* | flag controlling printing of HOL types |
| `Globals.show_assums` := *bool* | flag for controlling display of theorem assumptions |
| \refentry{Globals.show_tags} := *bool* | flag for controlling display of tags in theorem pretty-printer |
| \refentry{Lib.start_time}() | set a timer running |
| \refentry{Lib.end_time} *name* | check a running timer, and print out how long it has been running |
| \refentry{Lib.time} *function* | measure how long a function application takes |
| \refentry{Count.thm_count}() | returns the current value of the theorem counter |
| `Count.reset_thm_count`() | resets the theorem counter |
| \refentry{Count.apply} *function* | returns the theorem count for a function application |
