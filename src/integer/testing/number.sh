#!/bin/sh

perl -e '$/ = "\n\n"; while (<>) { print $i++, " ", $_; }'
