#!/bin/sh
# This file creates the hh/hh_h4 (main and translation) 
# and predict/predict (predictions) binaries.

cd hh/hh1
make
cd ..
make
cd ../predict
make
