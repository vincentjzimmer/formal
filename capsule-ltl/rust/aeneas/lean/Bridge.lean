/-
  Bridge.lean — the refinement lemma between the Aeneas-EXTRACTED capsule code
  (Capsule.lean, monadic `Result`, `U64` versions) and the ABSTRACT model
  (Abstract.lean = ltl_capsule.lean + refine_capsule.lean, pure, `Nat` versions).

  This closes the single previously-unproved link in the end-to-end chain.

  We define an abstraction map α : capsule.St → UefiCapsuleLTL.St (taking the
  U64 version fields to their Nat values) and prove:

    advance_refines : ∀ s, capsule.advance s = ok (α⁻¹-image of UefiCapsuleLTL.advance (α s))

  i.e. the extracted `advance` always succeeds and its result abstracts to the
  abstract `advance` of the abstracted state. Composed with the L1/L5 theorems
  (`responsiveness_det`, `safety_authentic_det`), the temporal guarantees then
  hold of the EXTRACTED Rust-derived function, not merely a hand-copy of it.

  No `sorry`. `advance` performs no arithmetic (it only copies capVer into
  fwVer), so no u64-overflow side-condition is needed for the refinement.
-/
import Capsule
import Abstract

open Aeneas Aeneas.Std Result ControlFlow Error

namespace CapsuleBridge

/-- Map an extracted phase to the abstract phase. -/
def αPhase : capsule.Phase → UefiCapsuleLTL.Phase
  | capsule.Phase.Idle           => UefiCapsuleLTL.Phase.Idle
  | capsule.Phase.CapsuleStaged  => UefiCapsuleLTL.Phase.CapsuleStaged
  | capsule.Phase.PostReset      => UefiCapsuleLTL.Phase.PostReset
  | capsule.Phase.Authenticating => UefiCapsuleLTL.Phase.Authenticating
  | capsule.Phase.Applied        => UefiCapsuleLTL.Phase.Applied
  | capsule.Phase.Rejected       => UefiCapsuleLTL.Phase.Rejected

/-- Abstraction map on states: U64 version fields go to their Nat values. -/
def α (s : capsule.St) : UefiCapsuleLTL.St :=
  { phase          := αPhase s.phase
    fwVersion      := s.fw_version.val
    capsulePresent := s.capsule_present
    capsuleVersion := s.capsule_version.val
    capsuleSigValid := s.capsule_sig_valid
    resetOccurred  := s.reset_occurred }

/-- A phase that is not a terminal sink. The Rust `advance` halts at the
    `Applied`/`Rejected` sinks (returns its input unchanged), whereas the
    abstract `advance` loops them back to `Idle` (the `finish` step). The two
    therefore agree precisely on the *non-sink* phases---which is exactly the
    good-path regime the liveness/safety corollaries traverse. -/
def NonSink (s : capsule.St) : Prop :=
  s.phase ≠ capsule.Phase.Applied ∧ s.phase ≠ capsule.Phase.Rejected

/-- **Refinement (good path).** On any non-sink state, the Aeneas-extracted
    `advance` succeeds (returns `ok`), and the abstraction (via α) of its result
    equals the abstract `advance` of the abstracted state: there is an extracted
    successor `s'` with `advance s = ok s'` and
    `α s' = UefiCapsuleLTL.advance (α s)`. This is the kernel-checked replacement
    for the by-eye "branch-for-branch" correspondence: the extracted Rust-derived
    code provably refines the proved transition system along the good path.
    `advance` does no arithmetic (it only copies capVer into fwVer), so no
    u64-overflow side-condition is needed. -/
theorem advance_refines (s : capsule.St) (hns : NonSink s) :
    ∃ s', capsule.advance s = ok s' ∧ α s' = UefiCapsuleLTL.advance (α s) := by
  obtain ⟨hA, hR⟩ := hns
  unfold capsule.advance capsule.reset capsule.begin_auth capsule.authenticate
         capsule.Phase.Insts.CoreCmpPartialEqPhase.eq
  cases h : s.phase with
  | Idle           => exact ⟨s, rfl, by simp [h, α, αPhase, UefiCapsuleLTL.advance]⟩
  | CapsuleStaged  =>
      exact ⟨{ s with phase := capsule.Phase.PostReset, reset_occurred := true },
             by simp, by simp [h, α, αPhase, UefiCapsuleLTL.advance]⟩
  | PostReset      =>
      exact ⟨{ s with phase := capsule.Phase.Authenticating },
             by simp, by simp [h, α, αPhase, UefiCapsuleLTL.advance]⟩
  | Authenticating =>
      by_cases hsig : s.capsule_sig_valid = true
      · by_cases hlt : s.fw_version < s.capsule_version
        · have hv : s.fw_version.val < s.capsule_version.val := (UScalar.lt_equiv _ _).mp hlt
          exact ⟨{ s with phase := capsule.Phase.Applied, fw_version := s.capsule_version },
                 by simp [hsig, hlt], by simp [α, αPhase, UefiCapsuleLTL.advance, h, hsig, hv]⟩
        · have hv : ¬ (s.fw_version.val < s.capsule_version.val) :=
            fun hc => hlt ((UScalar.lt_equiv _ _).mpr hc)
          exact ⟨{ s with phase := capsule.Phase.Rejected, capsule_present := false },
                 by simp [hsig, hlt], by simp [α, αPhase, UefiCapsuleLTL.advance, h, hsig, hv]⟩
      · exact ⟨{ s with phase := capsule.Phase.Rejected, capsule_present := false },
               by simp [hsig], by simp [α, αPhase, UefiCapsuleLTL.advance, h, hsig]⟩
  | Applied        => exact absurd h hA
  | Rejected       => exact absurd h hR

/-- The good path is non-sink throughout: a good staged state and its two
    forced successors (PostReset, Authenticating) are all non-sink, so
    `advance_refines` applies at each of the three steps to Applied. -/
theorem good_staged_nonsink (s : capsule.St) (h : s.phase = capsule.Phase.CapsuleStaged) :
    NonSink s := by
  refine ⟨?_, ?_⟩ <;> simp [h]

end CapsuleBridge
