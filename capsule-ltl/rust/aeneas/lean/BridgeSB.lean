/-
  BridgeSB.lean — refinement of the Aeneas-extracted Secure Boot `advance`
  (Secureboot.lean, monadic, cons-list `Revs` of U64) to the abstract Secure
  Boot `advance` (UefiSecureBoot.advance, pure, `List Nat`), via an abstraction
  map α. Instance #3's analogue of Bridge.lean.

  Unlike capsule/authvar (numeric U64), the observable here is a SET, so the
  bridge must relate the extracted recursive `append`/`clone` on `Revs` to
  `List.append` on `List Nat`. We prove those correspondences as lemmas, so the
  refinement is axiom-clean (the cons-list extraction avoids the opaque
  `Vec.append` axiom). No `sorry`.
-/
import Secureboot
import AbstractSB

open Aeneas Aeneas.Std Result ControlFlow Error

namespace SecureBootBridge

/-- Map an extracted revocation cons-list to the abstract `List Nat`. -/
def toList : secureboot.Revs → List Nat
  | secureboot.Revs.Nil      => []
  | secureboot.Revs.Cons h t => h.val :: toList t

def αPhase : secureboot.Phase → UefiSecureBoot.Phase
  | secureboot.Phase.Idle      => UefiSecureBoot.Phase.Idle
  | secureboot.Phase.Received  => UefiSecureBoot.Phase.Received
  | secureboot.Phase.Verifying => UefiSecureBoot.Phase.Verifying
  | secureboot.Phase.Updated   => UefiSecureBoot.Phase.Updated
  | secureboot.Phase.Refused   => UefiSecureBoot.Phase.Refused

def α (s : secureboot.St) : UefiSecureBoot.St :=
  { phase         := αPhase s.phase
    dbx           := toList s.dbx
    reqPresent    := s.req_present
    reqRevs       := toList s.req_revs
    reqAuthorized := s.req_authorized }

/-- The extracted recursive `clone` on `Revs` is the identity (returns `ok` of
    its argument). The element clone `CloneU64.clone h = h` is pure. -/
theorem clone_eq (r : secureboot.Revs) :
    secureboot.Revs.Insts.CoreCloneClone.clone r = ok r := by
  induction r with
  | Nil => rw [secureboot.Revs.Insts.CoreCloneClone.clone]
  | Cons h t ih =>
      rw [secureboot.Revs.Insts.CoreCloneClone.clone]
      have hh : core.clone.impls.CloneU64.clone h = h := by
        simp [core.clone.impls.CloneU64.clone]
      rw [hh]; simp [ih, lift]

/-- The extracted recursive `append` corresponds to `List.append` under `toList`:
    `append a b = ok r` with `toList r = toList a ++ toList b`. -/
theorem append_toList (a b : secureboot.Revs) :
    ∃ r, secureboot.append a b = ok r ∧ toList r = toList a ++ toList b := by
  induction a with
  | Nil =>
      refine ⟨b, ?_, by simp [toList]⟩
      rw [secureboot.append]
  | Cons h t ih =>
      obtain ⟨r, hr, hrl⟩ := ih
      refine ⟨secureboot.Revs.Cons h r, ?_, ?_⟩
      · rw [secureboot.append]; simp [hr]
      · simp [toList, hrl]

def NonSink (s : secureboot.St) : Prop :=
  s.phase ≠ secureboot.Phase.Updated ∧ s.phase ≠ secureboot.Phase.Refused

/-- **Refinement (good path).** On any non-sink state, the extracted `advance`
    succeeds and its abstraction equals the abstract `advance` of the abstracted
    state. The append-only `update` is bridged via `append_toList`/`clone_eq`. -/
theorem advance_refines (s : secureboot.St) (hns : NonSink s) :
    ∃ s', secureboot.advance s = ok s' ∧ α s' = UefiSecureBoot.advance (α s) := by
  obtain ⟨hU, hR⟩ := hns
  unfold secureboot.advance secureboot.begin_verify secureboot.update
         secureboot.Phase.Insts.CoreCmpPartialEqPhase.eq
  cases h : s.phase with
  | Idle       => exact ⟨s, rfl, by simp [h, α, αPhase, UefiSecureBoot.advance]⟩
  | Received   =>
      exact ⟨{ s with phase := secureboot.Phase.Verifying },
             by simp, by simp [h, α, αPhase, UefiSecureBoot.advance]⟩
  | Verifying  =>
      by_cases ha : s.req_authorized = true
      · -- update: clone req_revs, append to dbx
        obtain ⟨r, hr, hrl⟩ := append_toList s.dbx s.req_revs
        refine ⟨{ s with phase := secureboot.Phase.Updated, dbx := r }, ?_, ?_⟩
        · simp [ha, clone_eq, hr]
        · simp [α, αPhase, UefiSecureBoot.advance, h, ha, hrl]
      · exact ⟨{ s with phase := secureboot.Phase.Refused, req_present := false },
               by simp [ha], by simp [α, αPhase, UefiSecureBoot.advance, h, ha]⟩
  | Updated    => exact absurd h hU
  | Refused    => exact absurd h hR

end SecureBootBridge
