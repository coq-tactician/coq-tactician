#!/bin/bash

git log -1 --pretty=%B >> ../coq-tactician-stdlib/git-log.txt
git log -1 --pretty=%B >> ../coq-tactician-stdlib/all-errors.txt
make clean
make
make install
cd ../coq-tactician-stdlib
make clean
/usr/bin/time -o git-log.txt -a make BENCHMARK=40 -j64 2> error.txt
cat error.txt >> all-errors.txt
find . -name *.bench | xargs cat | awk '$3!=""' | wc -l >> git-log.txt
cd ../coq-tactician
