#!/bin/bash

set -e

if [ -z "$GITPOLY" ]
then

wget -q -O polyml.tar.gz https://github.com/polyml/polyml/archive/v5.7.1.tar.gz

tar xzf polyml.tar.gz
cd polyml-5.7.1
if [ -z "$ROOTPOLY" ]
then
  echo "*** Installing PolyML in home directory"
  ./configure --prefix=$HOME
  make
  make install
else
  echo "*** Installing PolyML in root land directory"
  ./configure --prefix=/usr/
  make
  sudo make install
fi

else

git clone https://github.com/polyml/polyml.git
cd polyml
./configure --prefix=$HOME
make
make compiler
make install

if [ $(uname) = "Darwin" ]
then
    perl -pi -e 's/-R/-rpath /g' $HOME/bin/polyc
fi

fi
