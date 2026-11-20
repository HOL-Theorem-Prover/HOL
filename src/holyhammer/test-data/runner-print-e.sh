#!/bin/sh

if [ "$1" = "--version" ]; then
  printf '%s\n' test
  exit 0
fi

delay=${1:-0}
recording=${2:-e-theorem-chatter.out}

if [ "$delay" != 0 ]; then
  /bin/sleep "$delay"
fi

exec /bin/cat "${0%/*}/$recording"
