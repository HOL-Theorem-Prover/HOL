#!/bin/bash

set -e

cd

if [ -z "$SVNPOLY" ]
then

wget -q -O polyml5.5.1.tar.gz "http://downloads.sourceforge.net/project/polyml/polyml/5.5.1/polyml.5.5.1.tar.gz?r=http%3A%2F%2Fsourceforge.net%2Fprojects%2Fpolyml%2Ffiles%2Fpolyml%2F5.5.1%2Fpolyml.5.5.1.tar.gz%2Fdownload&ts=1384728510&use_mirror=softlayer-dal"

tar xzf polyml5.5.1.tar.gz
cd polyml.5.5.1
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

svn checkout svn://svn.code.sourceforge.net/p/polyml/code/trunk/polyml polyml
cd polyml
./configure --prefix=$HOME --enable-shared
make
make compiler
make install

fi
