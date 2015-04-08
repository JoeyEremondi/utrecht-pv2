#!/bin/bash
for i in {1..8}
do
  echo "Testing with N=$i"
  spin -a -DN=$i $1.pml
  gcc pan.c
  ./a.out -a 
done