/-
  CapsuleInstance.lean — capsule update as INSTANCE #1 of AuthMonotone.

  This validates the abstraction: the existing capsule transition system is
  packaged as a `Monitor`, and the generic theorems (R1, R2, S, G) specialize
  back to the capsule properties proved by hand in ltl_capsule.lean — recovered
  here with NO new bespoke proof, only by discharging the monitor obligations
  (which reuse the existing step lemmas).

  Under the corrected model (EDK II checks the LSV floor, not running fwVer),
  the monotone observable is `lsv` (the stored lowest-supported-version floor),
  NOT `fwVersion`.  The running version is NOT guaranteed non-decreasing; a
  signed capsule above the LSV floor may install a version lower than the
  currently-running one.  The `StrictMonitor` extension no longer applies
  (the floor is bumped to `capsuleVersion` on apply, but that is a weak ≤ step,
  not a strict < step when `capsuleVersion = lsv`), so we instantiate the base
  `Monitor` only.

  Compile together with the framework and the capsule development:
    cat AuthMonotone.lean ltl_capsule.lean CapsuleInstance.lean > /tmp/c.lean
    lean /tmp/c.lean
-/

import AuthMonotone
import ltl_capsule

namespace UefiCapsuleLTL
open AuthMonotone Phase

/-- The capsule update process as an authority-guarded monotone monitor.
    `val` is the LSV floor (the correct EDK II anti-rollback observable);
    `committed` is "phase = Applied"; `authRec` is "signature checked valid".
    The four obligations are discharged by the step lemmas from ltl_capsule. -/
def capsuleMonitor : Monitor where
  S            := St
  V            := Nat
  Init         := Init
  Step         := Step
  val          := fun s => s.lsv        -- LSV floor is the monotone observable
  le           := Nat.le
  committed    := fun s => s.phase = Applied
  authRec      := fun s => s.capsuleSigValid = true
  le_refl      := Nat.le_refl
  le_trans     := Nat.le_trans
  step_mono    := step_lsv_mono
  init_unc     := by
    intro s h hap; rw [h.1] at hap; exact absurd hap (by decide)
  invAuth_step := by
    intro s s' h hs hap; cases h <;> simp_all
  commit_guard := by
    intro s s' h hnow hprev
    exact (apply_guard h hnow hprev).1

/-- The capsule monitor's runs coincide with capsule `IsRun`. -/
theorem capsuleMonitor_isRun (σ : Nat → St) :
    capsuleMonitor.IsRun σ ↔ IsRun σ := Iff.rfl

/-! ## The core properties, recovered as specializations -/

/-- R1/R2 (LSV anti-rollback) from the generic `global_mono`.
    The LSV floor is non-decreasing along every run. -/
theorem capsule_lsv_antirollback {σ} (hr : IsRun σ) :
    ∀ i j, i ≤ j → (σ i).lsv ≤ (σ j).lsv :=
  capsuleMonitor.global_mono hr

/-- S (authenticity) from the generic `auth_at_commit`. -/
theorem capsule_authentic {σ} (hr : IsRun σ) (i : Nat)
    (hc : (σ i).phase = Applied) : (σ i).capsuleSigValid = true :=
  capsuleMonitor.auth_at_commit hr i hc

/-- G (apply-guard) from the generic `commit_needs_auth`:
    entering `Applied` requires a valid signature at the pre-state. -/
theorem capsule_apply_guard {σ} (hr : IsRun σ) (i : Nat)
    (hprev : (σ i).phase ≠ Applied) (hnext : (σ (i+1)).phase = Applied) :
    (σ i).capsuleSigValid = true :=
  capsuleMonitor.commit_needs_auth hr i hprev hnext

end UefiCapsuleLTL
