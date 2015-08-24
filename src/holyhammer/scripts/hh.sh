#!/bin/sh

EPROVER="../provers/eprover"
VAMPIRE="../provers/vampire"
Z3="../provers/z3"

# Run eprover, vampire and z3
(if [ -f $EPROVER ]; then sh hh_eprover.sh $2 $5 $1; fi) & \
(if [ -f $VAMPIRE ]; then sh hh_vampire.sh $3 $6 $1; fi) & \
(if [ -f $Z3 ]; then sh hh_z3.sh $4 $7 $1; fi) & \
wait
