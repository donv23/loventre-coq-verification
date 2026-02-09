#!/bin/bash
##
## LOVENTRE ENGINE — gen_batch_witness_v6
## v1200/fix22
## Genera witness_v6_011 ... witness_v6_063
##

START=11
END=63

for i in $(seq $START $END); do
  NUM=$(printf "%03d" $i)
  echo "[GEN] witness_v6_$NUM"
  ./scripts/gen_one_witness_v6.sh $i || {
    echo "[ERRORE] generazione fallita su $NUM"
    exit 1
  }
done

echo "=== OK: batch generato $START → $END ==="

