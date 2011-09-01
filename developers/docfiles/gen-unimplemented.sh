#!/bin/sh

fgrep -x -f implemented.txt -v documented.txt
