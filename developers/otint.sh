#!/bin/sh
sed "/!interpretation/ {r$1
d}" $2 > ${2%unint.thy}thy
