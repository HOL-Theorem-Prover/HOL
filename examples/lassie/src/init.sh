#!/bin/bash

if [ "$LASSIEDIR" == "" ]; then
  export LASSIEDIR=../ #recovery attempt
fi

if [[ -d "$LASSIEDIR/sempre/fig" ]]
then
  echo "SEMPRE already initialized skipping intialization"
else
  cd $LASSIEDIR/sempre 
  echo "Initialization running" 
  ./pull-dependencies core interactive
  #ant core interactive
  echo "Initialization done"
  cd $LASSIEDIR/src
fi
