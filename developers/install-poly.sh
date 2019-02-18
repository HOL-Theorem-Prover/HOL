#!/bin/bash

set -e

POLY_BASE="https://github.com/polyml/polyml"

# Defaults:
POLY_VERSION=${POLY_VERSION:-v5.7.1}
POLY_GIT=${POLY_GIT:-F}
POLY_ROOT=${POLY_ROOT:-F}

PREFIX=$HOME
if [ "$POLY_ROOT" == "T" ]
then
  PREFIX="/usr/"
fi

if [ "$POLY_GIT" == "T" ]
then
  git clone ${POLY_BASE}.git
else
  mkdir polyml
  wget -qO- ${POLY_BASE}/archive/${POLY_VERSION}.tar.gz | \
  tar xvz -C polyml --strip-components 1
fi

cd polyml
echo "*** Configuring PolyML for prefix: ${PREFIX}"
./configure --prefix=$PREFIX
make

if [ "$POLY_GIT" == "T" ]
then
  make compiler
fi

if [ "$POLY_ROOT" == "T" -a "$UID" != "0" ]
then
  sudo make install
else
  make install
fi

if [ $(uname) = "Darwin" ]
then
  perl -pi -e 's/-R/-rpath /g' $HOME/bin/polyc
fi

cd
if [ "$OPENTHEORY" == "T" ]
then
    mkdir opentheory
    wget -qO- http://www.gilith.com/software/opentheory/opentheory.tar.gz | \
      tar xvz -C opentheory --strip-components 1
    pushd opentheory
    make polyml && bin/polyml/opentheory help && sudo mv bin/polyml/opentheory /usr/bin
    popd
fi
