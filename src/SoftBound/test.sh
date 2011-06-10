#!/bin/bash

BC_DIR=../Parser/tvcases/
SB=../_build/SoftBound/main.d.byte
ML_DIR=../Parser/tvcases/milli/
ML_CASES="addrof all bug1 bug2 cint2ptr fptr fptr2 fptr3 fptrret free funcargs 
  funcargs2 funcargsm funcargsret funcret funcret2 funcret3 globals int2ptr 
  loadm loadm2 loadr locals multimalloc postalloc ptr2int samechk select simple 
  storem storem2 storer struct undef"
MC_DIR=../Parser/tvcases/microbench/
MC_CASES="array array2 array3 global_array linkedlist linkedlistloop
          reference_test struct_array"
OC_DIR=../Parser/tvcases/olden-ccured/
# bh: llvm cannot compile it.
# power: TV isn't terminating.
# perimeter tsp have 'switch' instructions that we do not support so far.
# em3d: removed 'free', since Softbound is not sound with 'free'.
OC_CASES="bisort em3d health mst treeadd"
S95_DIR=../Parser/tvcases/spec95-ccured/
# 099.go 130.li 132.ijpeg has 'switch'
S95_CASES="129.compress"

for name in $ML_CASES; do 
  echo -e $name": \c" ; 
  llvm-as -f $ML_DIR$name"/test-linked.ll" -o input.bc
  $SB input.bc >& output.ll
  llvm-as -f output.ll
  opt -f output.bc -o opt.bc
  llvm-link opt.bc $BC_DIR"/softbound.bc" $BC_DIR"/softbound-wrappers.bc" > test-softbound.bc
  llvm-ld -native -lm -lcrypt test-softbound.bc -o test.exe
  ./test.exe 50
  ./test.exe 55
done;
for name in $MC_CASES; do 
  echo -e $name": \c" ; 
  llvm-as -f $MC_DIR$name"/test-linked.ll" -o input.bc
  $SB input.bc >& output.ll
  llvm-as -f output.ll
  opt -f output.bc -o opt.bc
  llvm-link opt.bc $BC_DIR"/softbound.bc" $BC_DIR"/softbound-wrappers.bc" > test-softbound.bc
  llvm-ld -native -lm -lcrypt test-softbound.bc -o test.exe
  ./test.exe 50
  ./test.exe 55
done;
for name in $OC_CASES; do 
  echo -e $name": \c" ; 
  llvm-as -f $OC_DIR$name"/test-linked.ll" -o $name"i.bc" 
  $SB $name"i.bc" >& $name"o.ll"
  llvm-as -f $name"o.ll"
  opt -f  $name"o.bc" -o $name"opt.bc"
  llvm-link $name"opt.bc" $BC_DIR"/softbound.bc" $BC_DIR"/softbound-wrappers.bc" > test-softbound.bc
  llvm-ld -native -lm -lcrypt test-softbound.bc -o $name".exe"
done;
echo -e "bisort: \c"; time ./bisort.exe 5000000 0;
echo -e "em3d: \c"; time ./em3d.exe 30000 300 50;
echo -e "health: \c"; time ./health.exe 8 250 1;
echo -e "mst: \c"; time ./mst.exe 4000;
echo -e "treeadd: \c"; time ./treeadd.exe 24 10;
for name in $S95_CASES; do 
  echo -e $name": \c" ; 
  llvm-as -f $S95_DIR$name"/src/test-linked.ll" -o $name"i.bc" 
  $SB $name"i.bc" >& $name"o.ll"
  llvm-as -f $name"o.ll"
  opt -f $name"o.bc" -o $name"opt.bc"
  llvm-link $name"opt.bc" $BC_DIR"/softbound.bc" $BC_DIR"/softbound-wrappers.bc" > test-softbound.bc
  llvm-ld -native -lm -lcrypt test-softbound.bc -o $name".exe"
  ./$name".exe"
done;
rm -f input.* output.* opt.* *.exe *.exe.bc bisort* em3d* health* mst* \
  treeadd* 129.compress* test-softbound.bc




