#!/bin/sh

rm -v -rf for-wasp 
cp -v -R for-gillian for-wasp

./for_wasp.py

make
