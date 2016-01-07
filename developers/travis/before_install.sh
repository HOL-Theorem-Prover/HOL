#!/bin/bash

set -e

cd

if [ -z "$GITPOLY" ]
then

wget -q -O polyml5.5.2.tar.gz "http://sourceforge.net/projects/polyml/files/polyml/5.5.2/polyml.5.5.2.tar.gz/download"

tar xzf polyml5.5.2.tar.gz
cd polyml.5.5.2
if [ -z "$ROOTPOLY" ]
then
  echo "*** Installing PolyML in home directory"
  ./configure --prefix=$HOME --enable-shared
  make
  make install
else
  echo "*** Installing PolyML in root land directory"
  ./configure --prefix=/usr/ --enable-shared
  make
  sudo make install
fi

else

git clone https://github.com/polyml/polyml.git
cd polyml
if [ $(uname) = "Darwin" ]
then
  SHARED=
else
  SHARED=--enable-shared
fi
./configure --prefix=$HOME $SHARED
make
make compiler
make install

if [ $(uname) = "Darwin" ]
then
    perl -pi -e 's/-R/-rpath /g' $HOME/bin/polyc
fi

fi
