#!/bin/bash

for i in *Script.sml
do
    Holmake "$@" ${i%Script.sml}.ot.art
done
