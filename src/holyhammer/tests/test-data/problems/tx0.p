% hhTptpProblem tx0.p
% Declarations (3)
tff(ty.i, type,
    i : $tType).
tff(sy.f, type,
    f : ($i * $i) > $i).
tff(sy.p, type,
    p : $i > $o).
% Facts (1)
tff(fact, axiom,
    ((![X : $i]: p($ite(c(X),f(X,a),a))))).
% Conjecture (1)
tff(conjecture, conjecture,
    (p(a))).
