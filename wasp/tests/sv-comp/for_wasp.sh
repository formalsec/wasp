rm -v -rf for-wasp
cp -v -R original for-wasp

python for_wasp.py

for d in for-wasp/*; do
  cp -v Makefile_ $d/Makefile
  cp -v patch.sh $d/patch.sh
done

make
