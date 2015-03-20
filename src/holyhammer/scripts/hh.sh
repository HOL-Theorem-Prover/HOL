EPROVER="../provers/eprover/eprover"
VAMPIRE="../provers/vampire/vampire"
Z3="../provers/z3/z3"

# Run eprover, vampire and z3
(if [ -f $EPROVER ]; then sh hh_eprover.sh; fi) & \
(if [ -f $VAMPIRE ]; then sh hh_vampire.sh; fi) & \
(if [ -f $Z3 ]; then sh hh_z3.sh; fi)
