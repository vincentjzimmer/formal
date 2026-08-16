# Rust reference monitor: Verus and Aeneas

Two routes to verifying a Rust reimplementation of the UEFI capsule-update
*decision logic* — moving the foundational proof's guarantees from an abstract
state machine onto executable code. Hardware I/O (flash writes, the signature
primitive) stays behind a trusted boundary: the same `sigOK`-oracle
decomposition the Lean/TLA+ models use.

| | Verus | Aeneas |
|--|-------|--------|
| **How** | Verifies Rust *directly* (spec/proof annotations, Z3) | Extracts safe Rust → pure functional model in **Lean**/Coq/F\*, prove there |
| **File** | `verus/capsule.rs` | `aeneas/capsule.rs` (+ Lean harness) |
| **Subset** | Most of Rust, incl. `proof`/`spec` ghost code | Safe, `unsafe`-free, sequential only |
| **In nixpkgs?** | No (prebuilt release / source build) | No (Charon + Aeneas from source) |
| **Best for** | Self-contained verified Rust monitor | Refinement-to-Lean tying back to `ltl_capsule.lean` |

Plain `rustc` confirms `aeneas/capsule.rs` compiles as ordinary safe Rust
(prerequisite for Charon extraction); `verus/capsule.rs` requires the Verus
toolchain (it uses `vstd` and `spec`-mode `nat`).

## What ports, and what does not

The five foundational properties split cleanly by *kind*:

- **Safety / functional correctness — port directly to both tools.**
  S (authenticity), R1/R2 (anti-rollback), G (apply-guard), O (reset-first) are
  inductive invariants over a `step` relation. `verus/capsule.rs` carries all of
  them: `anti_rollback_step` (R1), `apply_guard` (G), `inv_step` + `inv_run`
  (S, O), and `anti_rollback_global` (R2) by induction over a `Seq<St>` run.
- **Liveness (L) — does NOT port directly.** Neither Verus nor Aeneas reasons
  about infinite executions or fairness; both are safety/termination verifiers.
  L stays in the TLA+/Lean temporal layer. See the next section for what *can*
  be recovered at the code level.

## Liveness on the refinement to code — the real options

This is the subtle part. You cannot get the *infinitary* liveness property
(`G(good ⇒ F applied)` over ω-runs) from Verus or Aeneas. But the foundational
proof's L is special: it is **fairness-free** and proved by a **bounded,
deterministic 3-step witness** (reset → beginAuth → apply). That bounded shape
is exactly what *can* cross to code. Four options, strongest to weakest:

1. **Bounded-liveness as a total function + postcondition (recommended).**
   Implement the good path as a deterministic function — `advance` in
   `aeneas/capsule.rs`, or a `fn drive(s) -> St` in Verus — and prove:
   *if `good(s)` then `advance(advance(advance(s))).phase == Applied`*.
   This is a pure safety/functional-correctness statement (a postcondition on a
   terminating function), so **both tools accept it**. It is the executable
   image of the Lean 3-step witness: "from a good staged state, three forced
   steps reach Applied." You lose the ∀-run framing but keep the operational
   content, on real code.

2. **Termination / total correctness (Verus `decreases`).** Verus proves
   functions terminate via `decreases` clauses. Phrase progress as: the good
   path's driver terminates *and* lands in `Applied`. This upgrades option 1
   with a machine-checked termination measure — genuine total correctness of
   the apply path, which is the code-level meaning of "it eventually applies"
   when the path is deterministic and uninterrupted.

3. **Refinement + liveness upstairs (the Aeneas-to-Lean story).** Aeneas emits
   a Lean model of `advance`. Build the run `σ i = advance^[i](s0)` *in Lean*,
   reuse the existing LTL embedding in `ltl_capsule.lean`, and prove
   `Sat (G (good ⇒ F applied))` about the extracted function — the very theorem
   `responsiveness` already proves, now about code-derived `step`. Liveness
   lives in Lean (where ω-runs and `F`/`G` exist); the refinement guarantees the
   Lean run faithfully reflects the Rust. This is the only route that yields the
   *full* temporal L on something mechanically tied to the implementation.

4. **What genuinely cannot be done at the code layer.** Liveness *under
   adversarial interruption* — the crash-regime L the companion paper shows
   fails — is inherently about infinite fair schedules and belongs in TLA+/TLC,
   not in a code verifier. No Rust-level tool recovers it, and (per the
   companion) it is *false* without an added fairness assumption anyway.

**Bottom line.** Deterministic, uninterrupted progress crosses to code as
bounded-liveness + termination (options 1–2, both tools). The full ∀-run
temporal L crosses only via refinement into a temporal prover (option 3, Aeneas
→ Lean). Fairness-dependent liveness does not cross at all and stays in TLA+.

## Toolchain notes

- **Verus**: `https://github.com/verus-lang/verus` — download the prebuilt
  release (`verus-x86-linux.zip`) or build against its pinned `rust-toolchain`.
  Run `verus capsule.rs`. **Verified here: `8 verified, 0 errors`**
  (Verus 0.2026.05.03, bundled Z3). The `proof fn` bodies are short — the case
  split over `step` disjuncts is what Z3 closes — except the two run-induction
  lemmas (`anti_rollback_global`, `inv_run`), which each need one
  `assert(step(run[k], run[k+1]))` to instantiate the `is_run` quantifier and
  fire its trigger.
- **Aeneas**: `charon --dest llbc cargo` then
  `aeneas -backend lean capsule.llbc`. The generated Lean goes alongside
  `ltl_capsule.lean`; the liveness harness (option 3) is hand-written Lean that
  imports both.
