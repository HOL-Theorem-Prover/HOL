% hhTptpProblem tf1.p
% Declarations (3)
tff(ty.i, type,
    i : $tType).
tff(sy.f, type,
    f : ($i * $i) > $i).
tff(sy.p, type,
    p : $i > $o).
% Facts (1)
tff(fact, axiom,
    ((!>[A : $tType]: (![X : A]: p(A,X))))).
% Conjecture (1)
tff(conjecture, conjecture,
    (p(a))).
