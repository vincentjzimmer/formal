# Machine-Checked Linear Temporal Logic for the UEFI Capsule Update Process

[![Lean 4](https://img.shields.io/badge/Lean-4.16.0-blue.svg)](https://leanprover.github.io/)
[![TLA+](https://img.shields.io/badge/TLA%2B-2.19-purple.svg)](https://lamport.azurewebsites.net/tla/tla.html)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Official source artifact repository for the IEEE CARS 2026 paper:
> **"Machine-Checked Linear Temporal Logic for the UEFI Capsule Update Process: A Foundational Proof of Authenticity, Anti-Rollback, and Responsiveness"**  
> *Vincent Zimmer* (IEEE CARS 2026)

Repository URL: [https://github.com/vincentjzimmer/formal/capsule-ltl](https://github.com/vincentjzimmer/formal/capsule-ltl)

---

## 📌 Overview

Platform firmware update is among the highest-value targets in modern system security. UEFI standardizes this path via `UpdateCapsule` and the Firmware Management Protocol (FMP), but security arguments have historically existed only in prose and reference C code (`FmpDevicePkg`).

This repository provides the complete, open-source verification artifacts:
1. **Machine-Checked Lean 4 Proofs**: A shallow Linear Temporal Logic (LTL) embedding verifying 5 core security properties:
   - **Authenticity ($S$)**: Only signed capsules are applied.
   - **Anti-Rollback ($R1, R2$)**: Installed version is monotone non-decreasing (locally & globally).
   - **Apply Guard ($G$)**: Pre-application state requires a strictly newer version.
   - **Reset Ordering ($O$)**: Application requires a mandatory platform reset.
   - **Responsiveness ($L$)**: Good path forcing guarantees eventual application.
2. **TLA+ & TLAPS Specifications**: Explicit-state cross-validation (TLC) probing model boundaries (power failures, torn metadata, multi-device dependencies) and unbounded safety re-proofs (TLAPS).
3. **Executable Safe-Rust Reference Monitor**: Verified refinement via Charon/Aeneas mapping executable Rust `advance` code to the abstract Lean `Step` relation.

---

## 📂 Repository Structure

```
.
├── README.md                          # Top-level artifact documentation
├── LICENSE                            # License file (MIT)
├── lean/                              # Lean 4 theorem proving suite
│   ├── lakefile.lean                  # Lake package manager setup
│   ├── lean-toolchain                 # Lean toolchain pin (v4.16.0)
│   ├── ltl_capsule.lean               # Core LTL semantics & 5 security theorems
│   ├── refine_capsule.lean            # Rust refinement proof
│   ├── AbstractAdvance.lean           # Abstract state transition model
│   ├── AuthMonotone.lean              # Monotonicity helper lemmas
│   ├── CapsuleInstance.lean           # Model instantiation
│   └── Composition.lean               # System composition proofs
├── tla+/                              # TLA+ specifications & TLC configs
│   ├── CapsuleUpdate.tla              # Baseline TLA+ model
│   ├── CapsuleInductive.tla           # Inductive invariant for TLAPS
│   ├── CapsuleMultiDevice.tla         # Multi-device dependency extension
│   ├── CapsuleProof.tla               # TLAPS interactive proof script
│   └── configs/                       # TLC configurations
│       ├── MC_nocrash.cfg             # Baseline execution (157 states)
│       ├── MC_crash.cfg               # Power-fail / crash model checking
│       ├── MC_multidevice.cfg         # Multi-device cyclic dependency analysis
│       └── MC_multidevice_acyclic.cfg # Multi-device acyclic dependency analysis
└── rust/                              # Executable Rust reference monitor & extraction
    ├── aeneas/                        # Charon / Aeneas translation pipeline
    │   ├── capsule.rs                 # Safe Rust capsule state machine
    │   └── extract.sh                 # Lean translation script
    └── verus/                         # Verus verification specs
```

---

## 🛠️ Verification & Build Instructions

### 1. Verifying Lean 4 Proofs

**Prerequisites**: Lean 4 (v4.16.0) installed via `elan`.

```bash
cd lean
elan override set leanprover/lean4:v4.16.0
lake build
```

To verify that the kernel axioms rest only on standard logic with **zero `sorry`**:

```bash
lean --run ltl_capsule.lean
```

### 2. Running TLA+ Model Checker (TLC)

**Prerequisites**: Java 11+ and `tla2tools.jar` (TLC v2.19).

```bash
cd tla+
# Run baseline safety check
java -cp tla2tools.jar tlc2.TLC -config configs/MC_nocrash.cfg CapsuleUpdate.tla

# Run power-fail / crash check
java -cp tla2tools.jar tlc2.TLC -config configs/MC_crash.cfg CapsuleUpdate.tla
```

### 3. Executable Rust Monitor

**Prerequisites**: Rust toolchain (stable).

```bash
cd rust/aeneas
rustc --crate-type lib capsule.rs
```

---

## 📜 Citation

If you use this work, please cite:

```bibtex
@inproceedings{zimmer2026capsuleltl,
  author    = {Vincent Zimmer},
  title     = {Machine-Checked Linear Temporal Logic for the UEFI Capsule Update Process: A Foundational Proof of Authenticity, Anti-Rollback, and Responsiveness},
  booktitle = {IEEE Cyber Awareness and Research Symposium (CARS)},
  year      = {2026}
}
```

---

## 📄 License

This repository is licensed under the [MIT License](LICENSE).
