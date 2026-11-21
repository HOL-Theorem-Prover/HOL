#!/bin/sh
# burn.sh N
#
# N rounds of shell arithmetic, in a child of this script rather than
# in this script itself, so that a grandchild's cost has to travel the
# same path a recursive `Holmake -C dir' inside a recipe does.
#
# A round count rather than a duration, so the four targets here stay
# in a fixed ratio whatever the machine's speed; the test asserts on
# the ratios between them and never on a wall-clock figure.

sh -c 'i=0; while [ $i -lt '"$1"' ]; do i=$((i+1)); done'
