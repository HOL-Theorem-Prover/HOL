#!/bin/bash

if [ $# -ne 2 ]
then
    echo "Usage: $0 outputfile command" >&2
    exit 1
fi

output=$1
shift
fast=0

(sleep 3
 while IFS= read -r line
 do
    case "$line" in
        '##FAST' ) fast=1 ;;
        '##SLOW' ) fast=0 ;;
        * ) echo "$line" ;;
    esac
    if [ $fast -eq 0 ] ; then sleep 1 ; fi
 done) | script $output "$@"
