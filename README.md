# Project VINCIT: UMA Physics & Entropy Harvesting (v1206)

> **Experimental Report on Thermodynamic Computation Limits in Apple Silicon Architecture (Validated on M1 Testbench).**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Status: Gold Run Certified](https://img.shields.io/badge/Status-Gold_Run_v1206-green.svg)](./VINCIT_GENESIS_BLOCK.txt)

## 🔭 Overview
Project VINCIT is not a theoretical attempt to solve P vs NP purely mathematically. Instead, it is a **Cyber-Physical Systems (CPS) report** that isolates the physical limits of information processing on Unified Memory Architectures (UMA).

We identified a specific hardware event, the **Asymptotic Bus Saturation (ABS)**, where the system transitions from a deterministic computational state to a chaotic, high-entropy state (NP-BlackHole).

## 📂 Repository Structure

* **`/docs`**: Contains the **Whitepaper v1206** and the Methodological Note. These documents detail the "Gold Run" telemetry and the geometric constraints observed.
* **`/proofs`**: Contains the **Coq/Rocq** formal verification files (Seed C). These proofs demonstrate that the observed thermal obstruction is a structural necessity, not a software bug.
* **`VINCIT_GENESIS_BLOCK.txt`**: The SHA-256 root hash anchoring the dataset to the physical experimental session of Jan 23, 2026.

## 🗝 Key Findings (Evidence)

1.  **ABS Threshold**: The interconnect bus saturates at a specific physical limit (validated at **~49.8 GB/s** on M1), acting as an event horizon for computability.
2.  **Volumetric Barrier ($\mathfrak{B}$)**: A sharp discontinuity in latency observed at **20 GB** memory allocation (on 16GB RAM architecture).
3.  **Chaos Harvesting**: The system's behavior beyond the ABS threshold generates thermodynamically certified entropy, suitable for Post-Quantum cryptographic key generation.

## ⚠️ Disclaimer
This repository contains experimental data specific to the "Sparta" (M1) testbench. While the geometric principles ($\neg Rec$) and the thermodynamic obstruction pattern are intrinsic to the **Unified Memory Architecture (UMA)** design, specific throughput values will vary across chip generations (M2, M3, M4).

---
*Principal Investigator: Vincenzo Loventre*
