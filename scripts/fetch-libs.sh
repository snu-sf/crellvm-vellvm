#!/bin/bash
set -e

LIB=./lib
SRC=./src
if [[ $OSTYPE =~ "darwin" ]]; then
  MKTEMP=gmktemp
else
  MKTEMP=mktemp
fi

mkdir -p $LIB
cd $LIB
mkdir -p $SRC

LIBS="http://www.cis.upenn.edu/~plclub/metalib/dists/metalib-20090714.zip,metalib-20090714.zip \
      http://adam.chlipala.net/cpdt/cpdtlib.tgz,cpdtlib.tgz"

prep_metalib-20090714() {
    unzip -qqo $SRC/$1
    patch -p1 < ../patch/metalib.patch
}

prep_cpdtlib() {
    tar xzf $SRC/$1
    patch -p1 < ../patch/cpdtlib.patch
}

for p in $LIBS; do
  u=${p%,*}; f=${p#*,}
  echo -n "Downloading $SRC/$f"
  if [ -f $SRC/$f ]; then
      echo " ... archive exists, skipping"
  else
      echo; curl -L# "$u" -o $SRC/$f
  fi

  d=${f%.*}
  echo -n "Extracting to $d"
  if [ -d $d ]; then
      echo " ... target dir exists, skipping"
  else
      eval prep_$d $f      
  fi
done

echo "Done!"
