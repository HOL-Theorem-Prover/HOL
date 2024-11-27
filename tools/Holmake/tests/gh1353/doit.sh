#!/bin/bash

set -e

cd testd
ulimit -t 2
if [ "$#" -ne 1 ]
then
    echo "Need Holmake as arg 1"
    exit 1
fi

hmake=$1
retcode=$?

$hmake

if [ $? -eq 0 ]
then
    exit 1
elif [ $? -eq 152 ]
then
    # shouldn't happen given set -e
    echo "Time limit exceeded"
    exit 1
else
    exit 0
fi
