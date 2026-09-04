# Reproducing the Results of the Paper

> **"Machine-Checked Linear Temporal Logic for the UEFI Capsule Update Process"**  
> Vincent Zimmer — IEEE CARS 2026

This guide gives a self-contained, step-by-step recipe for reproducing every
claim in the paper from a fresh clone. All tools are free and open-source.
Estimated total time: **~30 minutes** (most of which is toolchain download).

---

## Prerequisites

| Tool | Version | Install |
|------|---------|---------|
| [elan / Lean 4](https://leanprover.github.io/lean4/doc/setup.html) | 4.30.0-rc2 | `curl -sSf https://elan.lean-lang.org/elan-init.sh \| sh` |
| [Java 11+](https://adoptium.net/) | ≥ 11 | `apt install default-jdk` / brew / etc. |
| [tla2tools.jar](https://github.com/tlaplus/tlaplus/releases) | 2.19 | Download jar, place in `tla+/` |
| [tlapm](https://tla.msr-inria.inria.fr/tlaps/) | ≥ 1.4.5 | `nix profile install nixpkgs#tlaps` |
| [z3](https://github.com/Z3Prover/z3) | 4.16.0 | `nix profile install nixpkgs#z3` |
| [Rust stable](https://rustup.rs/) | ≥ 1.75 | `curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \| sh` |
| [Verus](https://github.com/verus-lang/verus) | ≥ 0.2026 | see §4 below |
| [Charon + Aeneas](https://github.com/AeneasVerif/aeneas) | main | see §5 below |

A **Nix** environment (`nix profile install nixpkgs#tlaps nixpkgs#z3`) is the
quickest way to get the TLAPS + z3 stack on Linux/macOS.

---

## 1  Lean 4 Proofs  ✅ Machine-checked, zero `sorry`

Reproduces **all six theorems** from §IV of the paper (S, R1, R2, R3, O, G, L).

```bash
cd lean
lake build
```

Expected output: 9 modules compiled, 0 errors, at most 1 pre-existing warning
in `SecureBootInstance.lean` (opaque oracle stub).

To audit that no axiom beyond standard Lean logic is used:

```bash
lean --run ltl_capsule.lean   # prints theorem list; no `sorry` in #check output
```

Key theorems and their location in `ltl_capsule.lean`:

| Paper claim | Lean theorem | Line (approx.) |
|-------------|-------------|----------------|
| S  — authenticity       | `safety_authentic`   | ~180 |
| R1 — anti-rollback step | `antirollback_step`  | ~210 |
| R2 — anti-rollback run  | `antirollback_global`| ~230 |
| R3 — LSV monotonicity   | `lsv_monotone`       | ~160 |
| O  — reset ordering     | `reset_first`        | ~250 |
| G  — apply guarded      | `apply_guarded`      | ~270 |
| L  — responsiveness     | `responsiveness`     | ~300 |

---

## 2  TLA+ Model Checking (TLC)  ✅ Explicit-state exhaustive

Reproduces the **TLC findings** from §V: 157 reachable states (no-crash),
liveness counterexample under power-fail, and multi-device deadlock.

```bash
cd tla+

# Baseline (no power-fail): all invariants hold, liveness holds
java -cp tla2tools.jar tlc2.TLC -config configs/MC_nocrash.cfg CapsuleUpdate.tla

# Power-fail regime: liveness violated (expected counterexample)
java -cp tla2tools.jar tlc2.TLC -config configs/MC_crash.cfg CapsuleUpdate.tla

# Multi-device acyclic: safe
java -cp tla2tools.jar tlc2.TLC -config configs/MC_multidevice_acyclic.cfg CapsuleMultiDevice.tla

# Multi-device cyclic: deadlock found (expected)
java -cp tla2tools.jar tlc2.TLC -config configs/MC_multidevice.cfg CapsuleMultiDevice.tla
```

---

## 3  TLAPS Unbounded Safety Proofs  ✅ Interactive theorem prover

Reproduces the **TLAPS proofs** from §V: `NoRollback`, `NoRollbackLSV`,
`InvFloor`, and the inductive invariant from `CapsuleProof.tla`.

Requires `tlapm` and `z3` on PATH (see Prerequisites above).

```bash
cd tla+
bash CapsuleProof.sh
```

Expected: `tlapm exit 0 => all generated obligations proved`.

---

## 4  Verus SMT Verification  — safe-Rust spec

Reproduces verification of the Verus-annotated spec in `rust/verus/capsule.rs`,
which mirrors the Lean model with `proof` blocks for all invariants.

### Install Verus from source (Ubuntu 22.04 / Linux)

```bash
git clone https://github.com/verus-lang/verus /tmp/verus-src
cd /tmp/verus-src/source
./tools/get-z3.sh          # downloads compatible z3
source ../tools/activate   # sets up PATH + rustup
vargo build --release      # ~10 min first time
```

The `verus` binary will be at `source/target-verus/release/verus`.

### Run verification

```bash
/tmp/verus-src/source/target-verus/release/verus \
    /path/to/capsule-ltl/rust/verus/capsule.rs
```

Expected: `0 errors` — all `proof fn` blocks, `invariant`, and `ensures`
clauses verified by z3.

---

## 5  Aeneas Pipeline (Rust → Lean extraction)

Reproduces the **Charon/Aeneas extraction** that produces `lean/Capsule.lean`
from `rust/aeneas/capsule.rs`, closing the loop to the Lean refinement proof
in `lean/refine_capsule.lean`.

### Install Charon and Aeneas

```bash
# Build from the Aeneas nix flake (requires nix with flakes enabled)
CHARON_OUT=$(nix build "git+https://github.com/AeneasVerif/aeneas#charon" \
    --no-link --print-out-paths)
AENEAS_OUT=$(nix build "git+https://github.com/AeneasVerif/aeneas#aeneas-release" \
    --no-link --print-out-paths)

export CHARON=$CHARON_OUT/bin/charon
export AENEAS=$AENEAS_OUT/bin/aeneas
```

### Re-generate the Lean extraction

```bash
cd rust/aeneas
bash extract.sh
```

This produces `lean/Capsule.lean` — the pure-functional Lean model extracted
from the safe Rust code. `rust/aeneas/lean/Bridge.lean` links that generated
model to the abstract `Step` relation in `ltl_capsule.lean`, conditional on the
explicit `VerifierRefines` assumption that the concrete verifier implements the
abstract `certOK` oracle.

Type-check the generated modules and all three refinement bridges with the
Aeneas-compatible toolchain pinned in that directory:

```bash
cd lean
lake build
```

The bridge package pins its Aeneas support-library revision; the complete
artifact uses Lean 4.30.0-rc2 so generated and hand-written modules share one
compatible kernel format.

> **Note:** The repository ships a pre-generated `lean/Capsule.lean` snapshot
> so that steps 1–3 above work without Charon/Aeneas installed.  Run `extract.sh`
> to regenerate after any change to `capsule.rs`.

---

## Quick-check matrix

| Step | Command | Expected result |
|------|---------|----------------|
| Lean build | `cd lean && lake build` | 0 errors, 9 modules |
| TLAPS proofs | `cd tla+ && bash CapsuleProof.sh` | `tlapm exit 0` |
| TLC no-crash | `java … CapsuleUpdate.tla` (nocrash cfg) | All invariants hold |
| TLC crash | `java … CapsuleUpdate.tla` (crash cfg) | Liveness CE found |
| Rust/Aeneas | `rustc --crate-type lib capsule.rs` | 0 errors |
| Verus | `verus rust/verus/capsule.rs` | 0 errors |
| Aeneas pipeline | `cd rust/aeneas && bash extract.sh` | `lean/Capsule.lean` regenerated |
