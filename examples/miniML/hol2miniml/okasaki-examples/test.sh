#!/bin/sh

echo "-------------------- BankersQueue --------------------"
poly < BankersQueue_ml.txt
ocamlc -impl BankersQueue_ocaml.txt
echo "-------------------- LeftistHeap --------------------"
poly < LeftistHeap_ml.txt
ocamlc -impl LeftistHeap_ocaml.txt
echo "-------------------- BatchedQueue --------------------"
poly < BatchedQueue_ml.txt
ocamlc -impl BatchedQueue_ocaml.txt
echo "-------------------- PairingHeap --------------------"
poly < PairingHeap_ml.txt
ocamlc -impl PairingHeap_ocaml.txt
echo "-------------------- BinaryRandomAccessLists --------------------"
poly < BinaryRandomAccessLists_ml.txt
ocamlc -impl BinaryRandomAccessLists_ocaml.txt
echo "-------------------- PhysicistsQueue --------------------"
poly < PhysicistsQueue_ml.txt
ocamlc -impl PhysicistsQueue_ocaml.txt
echo "-------------------- BinomialHeap --------------------"
poly < BinomialHeap_ml.txt
ocamlc -impl BinomialHeap_ocaml.txt
echo "-------------------- RealTimeQueue --------------------"
poly < RealTimeQueue_ml.txt
ocamlc -impl RealTimeQueue_ocaml.txt
echo "-------------------- BottomUpMergeSort --------------------"
poly < BottomUpMergeSort_ml.txt
ocamlc -impl BottomUpMergeSort_ocaml.txt
echo "-------------------- RedBlackSet --------------------"
poly < RedBlackSet_ml.txt
ocamlc -impl RedBlackSet_ocaml.txt
echo "-------------------- HoodMelvilleQueue --------------------"
poly < HoodMelvilleQueue_ml.txt
ocamlc -impl HoodMelvilleQueue_ocaml.txt
echo "-------------------- SplayHeap --------------------"
poly < SplayHeap_ml.txt
ocamlc -impl SplayHeap_ocaml.txt
echo "-------------------- ImplicitQueue --------------------"
poly < ImplicitQueue_ml.txt
ocamlc -impl ImplicitQueue_ocaml.txt
echo "-------------------- UnbalancedSet --------------------"
poly < UnbalancedSet_ml.txt
ocamlc -impl UnbalancedSet_ocaml.txt
echo "-------------------- LazyPairingHeap --------------------"
poly < LazyPairingHeap_ml.txt
ocamlc -impl LazyPairingHeap_ocaml.txt
