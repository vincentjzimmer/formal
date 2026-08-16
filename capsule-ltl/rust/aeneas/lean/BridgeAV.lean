/-
  BridgeAV.lean — refinement of the Aeneas-extracted authenticated-variable
  `advance` (Authvar.lean, monadic, U64) to the abstract auth-var `advance`
  (UefiAuthVar.advance, pure, Nat), via an abstraction map α. Instance #2's
  analogue of Bridge.lean. No `sorry`; `advance` copies reqTime into storedTime
  (no arithmetic), so no u64-overflow side-condition is needed.
-/
import Authvar
import AbstractAV

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AuthVarBridge

def αPhase : authvar.Phase → UefiAuthVar.Phase
  | authvar.Phase.Idle       => UefiAuthVar.Phase.Idle
  | authvar.Phase.Received   => UefiAuthVar.Phase.Received
  | authvar.Phase.Verifying  => UefiAuthVar.Phase.Verifying
  | authvar.Phase.Written    => UefiAuthVar.Phase.Written
  | authvar.Phase.Refused    => UefiAuthVar.Phase.Refused

/-- Abstraction map: U64 timestamps go to their Nat values. The extracted state
    has no `storedData`/`reqData`; the abstract ones are set from the request,
    which on the good path equals the carried value, so we map them uniformly
    from the request timestamp's companion (here we use 0 as the abstract data
    placeholder — data is not part of any monitored property). -/
def α (s : authvar.St) : UefiAuthVar.St :=
  { phase          := αPhase s.phase
    storedTime     := s.stored_time.val
    storedData     := 0
    reqPresent     := s.req_present
    reqTime        := s.req_time.val
    reqData        := 0
    reqAuthorized  := s.req_authorized }

/-- Non-sink phases: the Rust `advance` halts at Written/Refused, the abstract
    one loops them to Idle; they agree on the good-path (non-sink) phases. -/
def NonSink (s : authvar.St) : Prop :=
  s.phase ≠ authvar.Phase.Written ∧ s.phase ≠ authvar.Phase.Refused

/-- **Refinement (good path).** On any non-sink state, the extracted `advance`
    succeeds and its abstraction equals the abstract `advance` of the abstracted
    state. -/
theorem advance_refines (s : authvar.St) (hns : NonSink s) :
    ∃ s', authvar.advance s = ok s' ∧ α s' = UefiAuthVar.advance (α s) := by
  obtain ⟨hW, hR⟩ := hns
  unfold authvar.advance authvar.begin_verify authvar.verify
         authvar.Phase.Insts.CoreCmpPartialEqPhase.eq
  cases h : s.phase with
  | Idle       => exact ⟨s, rfl, by simp [h, α, αPhase, UefiAuthVar.advance]⟩
  | Received   =>
      exact ⟨{ s with phase := authvar.Phase.Verifying },
             by simp, by simp [h, α, αPhase, UefiAuthVar.advance]⟩
  | Verifying  =>
      by_cases ha : s.req_authorized = true
      · by_cases hlt : s.stored_time < s.req_time
        · have hv : s.stored_time.val < s.req_time.val := (UScalar.lt_equiv _ _).mp hlt
          exact ⟨{ s with phase := authvar.Phase.Written, stored_time := s.req_time },
                 by simp [ha, hlt], by simp [α, αPhase, UefiAuthVar.advance, h, ha, hv]⟩
        · have hv : ¬ (s.stored_time.val < s.req_time.val) :=
            fun hc => hlt ((UScalar.lt_equiv _ _).mpr hc)
          exact ⟨{ s with phase := authvar.Phase.Refused, req_present := false },
                 by simp [ha, hlt], by simp [α, αPhase, UefiAuthVar.advance, h, ha, hv]⟩
      · exact ⟨{ s with phase := authvar.Phase.Refused, req_present := false },
               by simp [ha], by simp [α, αPhase, UefiAuthVar.advance, h, ha]⟩
  | Written    => exact absurd h hW
  | Refused    => exact absurd h hR

end AuthVarBridge
