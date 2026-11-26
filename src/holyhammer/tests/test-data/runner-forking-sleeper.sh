#!/bin/sh

if [ "$1" = "--version" ]; then
  printf '%s\n' test
  exit 0
fi

/bin/sleep 30 &
child=$!
printf '%s\n' "$child"
/bin/sleep 30
