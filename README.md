# Formal Verification for Platform Firmware & Systems

A collection of machine-checked proofs, temporal logic specifications, and model checking artifacts for platform firmware architectures, system security protocols, and hardware-software interfaces.

---

## 📚 Projects & Artifacts

| Project | Description | Methods / Tools | Associated Paper / Venue |
| :--- | :--- | :--- | :--- |
| [**`capsule-ltl/`**](./capsule-ltl/) | Machine-checked LTL proofs for UEFI capsule updates (Authenticity, Anti-Rollback, Reset Ordering) | Lean 4, TLA+, Safe Rust (Aeneas) | IEEE CARS 2026 |
| *`future-project/`* | *Brief description of next model / protocol* | *e.g., Lean 4, Coq, Isabelle, TLA+* | *Upcoming / In Review* |

  ---

## 🛠️ General Prerequisites

Individual subdirectories contain project-specific instructions, scripts, and pinned toolchains. Common tools used across this repository include:

    * **Theorem Proving:** [Lean 4](https://leanprover.github.io/) (managed via `elan`)
    * **Model Checking:** [TLA+ Tools / TLC](https://lamport.azurewebsites.net/tla/tla.html) (`java -jar tla2tools.jar`)
    * **Executable Specifications & Verification:** [Rust](https://rustup.rs/) / [Aeneas / Charon](https://github.com/AeneasVerif/aeneas)

---

## 🚀 Getting Started

Clone the repository:

```bash
  git clone https://github.com/vincentjzimmer/formal.git
  cd formal

Navigate to a specific project directory to inspect proofs and run verifications:

  cd capsule-ltl
  # Follow the local README.md for build and verification instructions
──────
## 📜 Citations

If you reference or build upon any of these artifacts, please cite the corresponding paper found in each subfolder's README.md.

For the repository as a whole:

  @misc{zimmer_formal,
    author    = {Vincent Zimmer},
    title     = {Formal Verification Models and Artifacts for Platform Firmware},
    url       = {https://github.com/vincentjzimmer/formal},
    year      = {2026}
  }
──────
  ## 📄 License

  Artifacts in this repository are available under the MIT License /LICENSE unless specified otherwise within individual subdirectories.
