#!/bin/sh

rm -v -rf for-wasp
cp -v -R original for-wasp

./for_wasp.py

make
