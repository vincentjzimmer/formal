/-
  Composition.lean — the unifying cross-cutting theorem.

  This is the payoff of the shared framework: a security property that neither
  the Secure Boot policy machine nor the authenticated-variable mechanism states
  alone, obtained by composing the generic monotonicity and authenticity
  results on the dbx store.

  Secure Boot's image-verification decision READS dbx (an image is denied iff
  its hash is revoked), and dbx CHANGES ONLY through the KEK-authorized update
  path (instance #3). Composing:

    * monotonicity (R2): a revoked hash stays in dbx forever, and
    * authenticity (S) + guard (G): dbx only ever changes under authorization,

  we prove POLICY NON-WEAKENING: once an image is denied by Secure Boot, it is
  denied at every later boot, and no unauthenticated actor can lift that denial.
  This is exactly the "an attacker cannot weaken Secure Boot" guarantee the
  prose specifications assert but never prove.

  Builds on AuthMonotone.lean + SecureBootInstance.lean. Mathlib-free, Lean 4.16.
-/

import SecureBootInstance

namespace UefiSecureBoot
open AuthMonotone Phase

/-- Secure Boot's image-verification decision: an image with hash `h` is denied
    iff `h` is in the forbidden database `dbx`. We phrase the predicate as
    `denied` (revoked) directly, the security-critical direction, to stay
    membership-based and Mathlib-free. -/
def denied (s : St) (h : Nat) : Prop := h ∈ s.dbx

/-- **POLICY NON-WEAKENING (composition of R2).** Once an image is denied at
    position `i`, it is denied at every later position `j ≥ i`. A revocation can
    never be silently undone: Secure Boot policy is monotone over the platform's
    lifetime. -/
theorem policy_non_weakening {σ} (hr : IsRun σ) {i j : Nat} (hij : i ≤ j)
    {h : Nat} (hdenied : denied (σ i) h) :
    denied (σ j) h :=
  sb_revocation_persists hr hij hdenied

/-- State-level: a step that introduces a new dbx member must be the
    KEK-authorized `update`. Proved over arbitrary `s s'` so the `idle`
    self-loop eliminates cleanly. -/
theorem new_revocation_authorized {s s' : St} (hstep : Step s s') {h : Nat}
    (hwas : h ∉ s.dbx) (hnow : h ∈ s'.dbx) : s.reqAuthorized = true := by
  cases hstep with
  | idle hp           => exact absurd hnow hwas
  | recv revs auth hp => exact absurd hnow hwas
  | beginVerify hp    => exact absurd hnow hwas
  | update hp hauth   => exact hauth
  | refuse hp hcond   => exact absurd hnow hwas
  | finishUpdated hp  => exact absurd hnow hwas
  | finishRefused hp  => exact absurd hnow hwas

/-- **AUTHORIZED-ONLY POLICY CHANGE (composition of the guard).** If a new
    denial appears between consecutive states (an image not previously revoked
    becomes revoked), that transition was KEK-authorized. An unauthenticated
    actor cannot alter Secure Boot policy. -/
theorem policy_change_authorized {σ} (hr : IsRun σ) (i : Nat)
    {h : Nat}
    (hwas : ¬ denied (σ i) h)
    (hnow : denied (σ (i+1)) h) :
    (σ i).reqAuthorized = true :=
  new_revocation_authorized (hr.2 i) hwas hnow

/-- **THE END-TO-END GUARANTEE.** Combining both: from any boot at which an
    image is denied, it remains denied at every subsequent boot, and the denial
    can only have been *introduced* by an authorized (KEK-signed) policy update.
    No unauthenticated actor can install a bogus revocation it was not authorized
    for, nor remove a legitimate one. -/
theorem secure_boot_policy_integrity {σ} (hr : IsRun σ) :
    (∀ i j, i ≤ j → ∀ h, denied (σ i) h → denied (σ j) h)
    ∧ (∀ i h, ¬ denied (σ i) h → denied (σ (i+1)) h →
        (σ i).reqAuthorized = true) := by
  refine ⟨?_, ?_⟩
  · intro i j hij h hd; exact policy_non_weakening hr hij hd
  · intro i h hwas hnow; exact policy_change_authorized hr i hwas hnow

end UefiSecureBoot
