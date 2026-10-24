#!/bin/bash
# fetch factordb factorizations of 2^t-1 for t = $1..$2 into the current directory (one JSON per t), 1 request/s
for t in $(seq $1 $2); do
  f=m$t.json
  if [ -s $f ] && grep -q '"FF"' $f; then continue; fi
  curl -sS -m 60 -A "Mozilla/5.0 (research)" "http://factordb.com/api?query=2%5E$t-1" -o $f
  sleep 1
done
echo done
