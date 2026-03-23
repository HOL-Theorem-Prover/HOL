#!/bin/bash

cd testd
ulimit -t 2
if [ "$#" -ne 2 ]
then
    echo "Usage:"
    echo "  $0 holstatefile holmake"
    exit 1
fi

holstate=$1
holmake=$2

echo "Running Holmake in testd directory"
$holmake --holstate=$holstate

retcode=$?
echo "Holmake completed with code $retcode"

if [ $retcode -eq 0 ]
then
    exit 1
elif [ $retcode -eq 152 ]
then
    echo "Time limit exceeded"
    exit 1
else
    exit 0
fi
