#!/bin/bash
cd "/Volumes/Extreme SSD/RICERCA/TUTTA LA RICERCA/02_VINCIT_R_D/loventre-coq-cycle11-lab"
Q=(-Q 01_Core Loventre_Core -Q 02_Advanced Loventre_Advanced -Q 02_Advanced/Geometry Loventre_Geometry -Q 03_Main Loventre_Main)
export Q
echo "Working dir: $(pwd)"
echo "Q=${Q[@]}"
