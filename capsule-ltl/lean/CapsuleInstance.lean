/-
  CapsuleInstance.lean — capsule update as INSTANCE #1 of AuthMonotone.

  This validates the abstraction: the existing capsule transition system is
  packaged as a `StrictMonitor`, and the generic theorems (R1, R2, S, G, strict
  advance) specialize back to the capsule properties proved by hand in
  ltl_capsule.lean — recovered here with NO new bespoke proof, only by
  discharging the monitor obligations (which reuse the existing step lemmas).

  Compile together with the framework and the capsule development:
    cat AuthMonotone.lean ltl_capsule.lean CapsuleInstance.lean > /tmp/c.lean
    lean /tmp/c.lean
-/

import AuthMonotone
import ltl_capsule

namespace UefiCapsuleLTL
open AuthMonotone Phase

/-- The capsule update process as a strict, authority-guarded monotone monitor.
    `val` is the running firmware version, ordered by `≤`/`<` on `Nat`;
    `committed` is "phase = Applied"; `authRec` is "signature valid". The four
    obligations are discharged by the capsule step lemmas. -/
def capsuleMonitor : StrictMonitor where
  S            := St
  V            := Nat
  Init         := Init
  Step         := Step
  val          := fun s => s.fwVersion
  le           := Nat.le
  committed    := fun s => s.phase = Applied
  authRec      := fun s => s.capsuleSigValid = true
  le_refl      := Nat.le_refl
  le_trans     := Nat.le_trans
  step_mono    := step_version_mono
  init_unc     := by
    intro s h hap; rw [h.1] at hap; exact absurd hap (by decide)
  invAuth_step := by
    intro s s' h hs hap; cases h <;> simp_all
  commit_guard := by
    intro s s' h hnow hprev
    exact (apply_guard h hnow hprev).1
  lt           := Nat.lt
  lt_irrefl    := Nat.lt_irrefl
  commit_strict := by
    intro s s' h hnow hprev
    -- entering Applied forces the `apply` rule, whose guard gives fw < cap = fw'
    have hg := apply_guard h hnow hprev   -- sig ∧ fw < cap
    -- and applying sets fw' := cap, so fw < fw'
    cases h <;> simp_all

/-- The capsule monitor's runs coincide with capsule `IsRun`. -/
theorem capsuleMonitor_isRun (σ : Nat → St) :
    capsuleMonitor.toMonitor.IsRun σ ↔ IsRun σ := Iff.rfl

/-! ## The five core properties, recovered as specializations -/

/-- R1/R2 (anti-rollback) from the generic `global_mono`. -/
theorem capsule_antirollback {σ} (hr : IsRun σ) :
    ∀ i j, i ≤ j → (σ i).fwVersion ≤ (σ j).fwVersion :=
  capsuleMonitor.toMonitor.global_mono hr

/-- S (authenticity) from the generic `auth_at_commit`. -/
theorem capsule_authentic {σ} (hr : IsRun σ) (i : Nat)
    (hc : (σ i).phase = Applied) : (σ i).capsuleSigValid = true :=
  capsuleMonitor.toMonitor.auth_at_commit hr i hc

/-- G (apply-guard) from the generic `commit_needs_auth` + `commit_strictly_advances`. -/
theorem capsule_apply_guard {σ} (hr : IsRun σ) (i : Nat)
    (hprev : (σ i).phase ≠ Applied) (hnext : (σ (i+1)).phase = Applied) :
    (σ i).capsuleSigValid = true ∧ (σ i).fwVersion < (σ (i+1)).fwVersion :=
  ⟨capsuleMonitor.toMonitor.commit_needs_auth hr i hprev hnext,
   capsuleMonitor.commit_strictly_advances hr i hprev hnext⟩

end UefiCapsuleLTL
