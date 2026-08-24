# TLA+ companion to the Lean capsule-update development

A starter TLA+ model for the proposed follow-on study: use model checking to
probe the *fidelity gap* between the hand-abstracted Lean LTS
(`ltl_capsule.lean`) and the real EDK II `FmpDevicePkg` flow.

## Files

| File | Purpose |
|------|---------|
| `CapsuleUpdate.tla` | The spec. Phase 1 mirrors the Lean `St`/`Step` one-to-one; Phase 2 adds the power-fail (`Crash`) action the Lean model abstracts away. |
| `MC_nocrash.cfg` | Baseline regime (`CRASH = FALSE`). Reproduces the Lean result. |
| `MC_crash.cfg` | Power-fail regime (`CRASH = TRUE`). Breaks fairness-free liveness. |

## Correspondence to the Lean model

The Lean `St` fields map directly to TLA+ state variables:

| Lean field | TLA+ variable | Note |
|------------|---------------|------|
| `phase` | `phase` | Same phase enum. |
| `fwVersion` | `fwVersion` | Running firmware version. |
| `lsv` | `lsv` | Lowest-supported-version floor. |
| `capsulePresent` | `capsulePresent` | Whether a capsule is staged. |
| `capsuleVersion` | `capsuleVersion` | Version carried by the staged capsule. |
| `imageDigest` | `imageDigest` | Authenticated input passed to `CertOK`. |
| `capsuleSigValid` | `capsuleSigValid` | Computed in `BeginAuth`, not chosen in `Stage`. |
| `resetOccurred` | `resetOccurred` | Reset-tracking flag. |

Each Lean `Step` constructor maps to exactly one TLA+ action:

| Lean rule | TLA+ action |
|-----------|-------------|
| `stutterIdle` | `StutterIdle` |
| `stage` (∃ `v`, `digest`) | `Stage` (∃ `v ∈ Versions`, `d ∈ Versions`) |
| `reset` | `Reset` |
| `beginAuth` | `BeginAuth` (`capsuleSigValid' := CertOK(imageDigest)`) |
| `apply` | `Apply` (`capsuleSigValid = TRUE /\ lsv <= capsuleVersion`) |
| `reject` | `Reject` (`capsuleSigValid = FALSE \/ capsuleVersion < lsv`) |
| `finishApplied` / `finishRejected` | `Finish` |
| *(none)* | `Crash` — power-fail, no Lean counterpart |

Notable alignment detail: `Stage` now sets only the staged version/digest and
presence bit; it does **not** choose `capsuleSigValid`. Authentication derives
that flag later from the staged digest via the spec-level oracle
`CertOK(d) == d /= 0`.

The Lean anti-rollback story now maps to the TLA+ floor properties:
`antirollback_lsv` → `AntiRollbackLSV`, `lsv_floor_maintained` → `InvFloor`,
`apply_guarded` → `ApplyGuarded`, `safety_authentic` → `SafetyAuthentic`,
`reset_first` → `ResetFirst`, and `responsiveness` → `Responsiveness`.

## Running

```sh
tlc -config MC_nocrash.cfg CapsuleUpdate.tla   # safety/floor/liveness checks
tlc -config MC_crash.cfg   CapsuleUpdate.tla   # L fails; safety/floor survive
```

## Findings reproduced here

1. **Baseline (no crash) passes the aligned checks.** The TLA+ model agrees
   with the current Lean proofs on the abstraction they share: authenticity,
   reset ordering, LSV-floor monotonicity, the floor invariant, and the guarded
   apply rule.

2. **Crash regime: `Responsiveness` (L) fails.** TLC returns a lasso
   `… Crash → BeginAuth → Crash → …`: a good capsule (its digest satisfies
   `CertOK` and its version is at or above the floor) is staged, but a
   power-fail fires repeatedly in the post-reset/authenticate window and
   starves `Apply` forever. This is the headline result the proposed paper
   predicts — **the fairness-freedom of L is an artefact of the Lean model's
   determinism.** Recovering L requires an explicit bounded-retry /
   no-infinite-crash fairness hypothesis.

3. **Safety and the stored floor survive the crash.** With a *faithful*
   partial write (a torn `SetImage` can only land the version actually being
   written, and only when an apply was in flight), `SafetyAuthentic`,
   `AntiRollbackLSV`, `ApplyGuarded`, `ResetFirst`, and `InvFloor` all still
   hold under crashes. The key monotone state is the stored floor `lsv`; the
   running `fwVersion` may vary independently after a crash.

4. **Crash-consistency of the running-version record is its own obligation.**
   Swap `CrashAdversarial` for `Crash` in `Next` (a torn write of the version
   *metadata* itself, landing any value) and `InvFloor` can break. This
   isolates a proof obligation invisible to the atomic-apply Lean model: the
   durability/atomicity relation between the persisted floor and the running
   firmware version across power loss.

## Unbounded closure: two routes (floor monotonicity without a version bound)

Both routes discharge the SAME inductive invariant
`IndInv == TypeOK /\ InvSig /\ InvReset /\ InvFloor` over all version numbers
in `Nat`, closing the bounded/unbounded gap between TLC and the Lean deductive
proof. `InvReset` is the same strengthening the Lean proof needed
(`Applied`-alone is not inductive). The step property is `NoRollbackLSV`
(`lsv' >= lsv`); its transitive closure yields the global anti-rollback fact.

### Route A — TLAPS (deductive; runnable from nixpkgs; **executed here**)

`CapsuleProof.tla` + `CapsuleProof.sh`. This is the TLA+ analogue of the Lean
development: a machine-checked *proof*, checked by the SMT/Zenon backends
instead of the Lean kernel.

```sh
nix profile install nixpkgs#tlaps nixpkgs#z3   # tlapm + a solver
./CapsuleProof.sh                              # tlapm exits 0
```

Theorems closed in the source module:

| Theorem | Statement |
|---------|-----------|
| `InitType` | `Init => TypeOK` |
| `NextType` | `TypeOK /\ [Next]_vars => TypeOK'` |
| `InitInv` | `Init => Inv` |
| `NextInv` | `Inv /\ [Next]_vars => Inv'` |
| `NoRollback` / `NoRollbackLSV` | `TypeOK /\ [Next]_vars => lsv' >= lsv` |

As before, the spec-level lifting `Safety == Spec => []Inv` ends in one purely
temporal step. If `ls4` is unavailable, that final QED remains marked
`OMITTED`; the state/action proof obligations are still spelled out in the
module.

### Route B — Apalache (symbolic / SMT; push-button; not run here)

`CapsuleInductive.tla` + `CapsuleInductive.sh`. Use Apalache's own flake:

```sh
nix run github:apalache-mc/apalache -- check --init=IndInv --inv=IndInv CapsuleInductive.tla
# or just: ./CapsuleInductive.sh   (auto-falls back to the flake)
```

Three queries: (1) `Init => IndInv`, (2) `IndInv /\ Next => IndInv'`, (3)
`NoRollbackLSV`. All UNSAT ⇒ `[] IndInv` and floor monotonicity for all of
`Nat`.

## Multi-device + EFI_FIRMWARE_IMAGE_DEP

`CapsuleMultiDevice.tla` lifts `fwVersion` to a per-device vector
`[Devices -> Nat]` and adds dependency expressions (`Dep[d]` = prereqs that
must already hold before applying to `d`). Apply gains a third guard,
`DepsSatisfied(target)`; reject fires if it is unmet.

```sh
tlc -config MC_multidevice.cfg          CapsuleMultiDevice.tla  # cyclic dep
tlc -config MC_multidevice_acyclic.cfg  CapsuleMultiDevice.tla  # acyclic dep
```

Findings (both verified above):

- **Safety lifts cleanly.** `SafetyAuthentic`, `AntiRollbackStep` (monotone in
  *every* component / product order), and `ApplyGuarded` all hold under both
  dependency tables. 482 distinct states.
- **The scalar liveness theorem L does NOT lift.** `ResponsivenessApply`
  (the faithful lift of Lean `responsiveness`, `GoodStaged => <> Applied`)
  **fails in both regimes**:
  - *Acyclic* (`nic` needs `ec >= 1`, `ec` free): a good capsule for `nic`
    can be staged while `ec` is still at 0, so it is *rejected* on a transient
    ordering miss. Lasso `Stage(nic) -> Reset -> BeginAuth -> Reject ->
    Finish`. Staging order is environment-controlled, so per-capsule liveness
    is simply false once dependencies exist.
  - *Cyclic* (`nic` needs `ec >= 1`, `ec` needs `nic >= 1`): the same
    rejection, but **permanent** — no staging order ever satisfies the cycle.
    A signed, strictly-newer image is authentic yet un-appliable forever.
- Every individual action remains weakly fair in both cases; the hazard is
  **structural**, invisible to the scalar Lean model. This isolates a new
  obligation: a *scheduling/ordering* condition (a topological apply order,
  acyclic `Dep`) under which a multi-device liveness analogue could be
  recovered.

## Next steps toward implementation alignment

- **Apalache** for the unbounded inductive-invariant closure (floor
  monotonicity without a version bound).
- **PlusCal** rendering of `FmpDeviceCheckImage`/`FmpDeviceSetImage` for
  EDK II reviewers who read C, not tactics.
- **Trace validation**: instrument the EDK II post-reset coalescing +
  `CheckImage`/`SetImage` path to emit phase/version/sig/LSV/device events,
  then check real execution traces against this spec (TLC as a monitor).
- **Multi-device + `EFI_FIRMWARE_IMAGE_DEP`**: lift the version field to a
  per-device vector with a partial order; model dependency expressions and
  let TLC hunt for ordering hazards and partial-update windows.
