#!/bin/sh

set -e

CAT=cat

if [ -x $(which jq) ]
then
    CAT="jq ."
fi

cabal run ambient-verifier:ambient-verifier -- \
  verify \
  --binary rop-unbal-read.exe \
  --overrides "overrides" \
  --metrics "metrics.json" \
  --fsroot "fs" \
  --statechart "rop-unbal-read.exe.yaml"

$CAT "metrics.json"
