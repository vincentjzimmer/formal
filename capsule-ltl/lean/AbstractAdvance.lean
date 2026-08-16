/-
  AbstractAdvance.lean — deterministic good-path `advance` functions for the
  authenticated-variable and Secure Boot instances, with their `step_advance`
  refinements (each `advance` step is a legal `Step`).

  These are the abstract targets the Aeneas-extracted Rust `advance` functions
  refine, exactly as `refine_capsule.lean`'s `advance` is for capsule. Compile
  after AuthVarInstance.lean / SecureBootInstance.lean (which define Step).

  Mathlib-free, Lean 4.16.
-/

import AuthVarInstance
import SecureBootInstance

/-! ## Authenticated variables: deterministic good-path advance -/
namespace UefiAuthVar
open Phase

/-- Deterministic good-path scheduler, mirroring rust/aeneas/authvar.rs. -/
def advance (s : St) : St :=
  match s.phase with
  | Idle        => s
  | Received    => { s with phase := Verifying }
  | Verifying   =>
      if s.reqAuthorized = true ∧ s.storedTime < s.reqTime then
        { s with phase := Written, storedTime := s.reqTime, storedData := s.reqData }
      else
        { s with phase := Refused, reqPresent := false }
  | Written     => { s with phase := Idle, reqPresent := false }
  | Refused     => { s with phase := Idle, reqPresent := false }

/-- Every `advance` step is a legal `Step` of the auth-var system. -/
theorem step_advance (s : St) : Step s (advance s) := by
  unfold advance
  cases h : s.phase with
  | Idle        => exact Step.idle s h
  | Received    => exact Step.beginVerify s h
  | Verifying   =>
      by_cases hc : s.reqAuthorized = true ∧ s.storedTime < s.reqTime
      · rw [if_pos hc]; exact Step.write s h hc.1 hc.2
      · rw [if_neg hc]
        apply Step.refuse s h
        by_cases ha : s.reqAuthorized = true
        · have : ¬ s.storedTime < s.reqTime := fun hlt => hc ⟨ha, hlt⟩
          exact Or.inr (Nat.le_of_not_lt this)
        · exact Or.inl (by cases hb : s.reqAuthorized <;> simp_all)
  | Written     => exact Step.finishWritten s h
  | Refused     => exact Step.finishRefused s h

end UefiAuthVar


/-! ## Secure Boot: deterministic good-path advance -/
namespace UefiSecureBoot
open Phase

/-- Deterministic good-path scheduler, mirroring rust/aeneas/secureboot.rs. -/
def advance (s : St) : St :=
  match s.phase with
  | Idle        => s
  | Received    => { s with phase := Verifying }
  | Verifying   =>
      if s.reqAuthorized = true then
        { s with phase := Updated, dbx := s.dbx ++ s.reqRevs }
      else
        { s with phase := Refused, reqPresent := false }
  | Updated     => { s with phase := Idle, reqPresent := false }
  | Refused     => { s with phase := Idle, reqPresent := false }

/-- Every `advance` step is a legal `Step` of the Secure Boot system. -/
theorem step_advance (s : St) : Step s (advance s) := by
  unfold advance
  cases h : s.phase with
  | Idle        => exact Step.idle s h
  | Received    => exact Step.beginVerify s h
  | Verifying   =>
      by_cases hc : s.reqAuthorized = true
      · rw [if_pos hc]; exact Step.update s h hc
      · rw [if_neg hc]
        apply Step.refuse s h
        cases hb : s.reqAuthorized <;> simp_all
  | Updated     => exact Step.finishUpdated s h
  | Refused     => exact Step.finishRefused s h

end UefiSecureBoot
