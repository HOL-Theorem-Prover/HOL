#!/bin/sh

fgrep -x -f documented.txt -v implemented.txt
