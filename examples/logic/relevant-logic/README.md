# Relevant Logic

This mechanisation of some core relevant logic theory is work done by James Taylor as his ANU Honours project (finishing in June 2022).

There are seven files:

**GoldblattRL**: an axiomatic presentation of propositional relevant logic, based on [Goldblatt 2011]. Defines the syntax of the logic and a predicate called `goldblatt_provable`, capturing the axioms and four rules of inference (including Modus Ponens).

**SlaneyRL**: a slightly different axiomatic presentation of propositional relevant logic, with a different syntax (disjunction and intensional conjunction are built-in rather than defined), and different axioms and rules.

**RLRules**: a number of results derived about the Goldblatt system. Some are results provable entirely within the system (*e.g.*, (A & (A --> B)) --> B); others are derivable rules of inference.

**GoldblattSlaneyEquiv**: proves that the two RL systems above are equivalent: there are functions for transforming the syntax from one to the other and these have the required properties wrt provability.

**NaturalDeduction**: a natural deduction system that is proved equivalent to the Goldblatt system. This uses “bunches” to the left of the turnstile, with comma and semicolon operators to merge bunches together.

**RMSemantics**: a presentation of the Routley-Meyer semantics based on ternary relations. Soundness and completeness proved.

**CoverSemantics**: a presentation of Goldblatt’s cover semantics, again with proofs of soundness and completeness.
