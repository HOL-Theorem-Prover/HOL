#!/bin/bash

ulimit -t 2
unquote=$1

echo "Running unquote"
$unquote < bugScript.sml

retcode=$?
echo
echo "unquote completed with code $retcode"

exit $retcode
