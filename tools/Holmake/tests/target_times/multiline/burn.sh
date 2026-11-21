#!/bin/sh
# burn.sh N
#
# Spend CPU: N rounds of shell arithmetic, in a child of this script
# rather than in this script itself.  The nesting is the point.  What
# Holmake records is its own `cutime', which only grows when a child is
# reaped, and which carries that child's *own* waited-for descendants
# with it -- so a grandchild's cost reaches Holmake exactly the way a
# recursive `Holmake -C dir' inside a recipe does.
#
# N is a round count rather than a duration so that the two targets
# here stay in a fixed ratio whatever the machine's speed; the test
# asserts on that ratio, never on a wall-clock figure.

sh -c 'i=0; while [ $i -lt '"$1"' ]; do i=$((i+1)); done'
