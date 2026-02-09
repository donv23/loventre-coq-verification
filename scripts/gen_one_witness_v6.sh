#!/bin/bash
##
## LOVENTRE ENGINE — gen_one_witness_v6
## v1200/fix21
## Genera un witness LMetrics_v6 parametrico dato un numero X
##

if [ -z "$1" ]; then
  echo "[ERRORE] Devi passare un indice (es: ./gen_one_witness_v6.sh 2)"
  exit 1
fi

IDX=$(printf "%03d" $1)
FILE="Coq_IO/LMetrics_v6/witness_v6_${IDX}.v"

echo "[INFO] Genero $FILE"

cat > "$FILE" <<EOF
(** Loventre Engine — witness_v6_${IDX}
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_${IDX}_example : LMetrics :=
  mkLMetrics
    ${1}.0%R      (* kappa_eff *)
    ${1}.1%R      (* entropy_eff *)
    ${1}.2%R      (* mass_eff *)
    ${1}.3%R      (* inertial_idx *)
    ${1}.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    ${1}.5%R      (* loventre_global_score *)
    ${1}          (* meta_label *)
    "witness_v6_${IDX}"%string.
EOF

echo "[OK] Created $FILE"

