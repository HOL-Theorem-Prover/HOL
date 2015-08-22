#!/bin/sh

EPROVER="../provers/eprover/eprover"
VAMPIRE="../provers/vampire/vampire"
Z3="../provers/z3/z3"

# Run eprover, vampire and z3
(type eprover >/dev/null 2>&1 && sh hh_eprover.sh $2 $5 $1) & \
(type vampire >/dev/null 2>&1 && sh hh_vampire.sh $3 $6 $1) & \
(type z3      >/dev/null 2>&1 && sh hh_z3.sh $4 $7 $1)
