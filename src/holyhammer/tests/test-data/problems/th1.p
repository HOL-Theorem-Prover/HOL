% hhTptpProblem th1.p
% Declarations (3)
thf(ty.i, type,
    i : $tType).
thf(sy.f, type,
    f : $i > $i > $i).
thf(sy.p, type,
    p : $i > $o).
% Facts (1)
thf(fact, axiom,
    ((!>[A : $tType]: (p @ (A) @ $ite((c @ X),(f @ X @ a),a))))).
% Conjecture (1)
thf(conjecture, conjecture,
    ((p @ a))).
