/-
  AuthVarInstance.lean — UEFI time-based authenticated variables as
  INSTANCE #2 of AuthMonotone.

  Models the SetVariable path for a variable carrying
  EFI_VARIABLE_AUTHENTICATION_2 (UEFI spec §8.2): a write must carry a PKCS#7
  signature by an authorized key AND a timestamp strictly newer than the stored
  one (anti-replay). The strict-monotone observable is the stored timestamp.

  Surfaces modelled here that have no capsule analogue:
    * an authority predicate `authorized` (signer ∈ key hierarchy) — kept as an
      oracle exactly like the capsule signature check;
    * the timestamp is the anti-rollback quantity (replacing the firmware
      version), demonstrating the framework generalizes beyond version numbers.

  We package the machine as a `StrictMonitor`; R1/R2 (timestamp never decreases),
  S (a committed write was authorized), and G (entering committed needs an
  authorized signer) come for free from the generic theorems, plus strict
  advance (no replay: a committed write strictly increases the timestamp).

  Self-contained, Mathlib-free, Lean 4.16.
-/

import AuthMonotone

namespace UefiAuthVar

/-- Phases of processing one SetVariable request for an authenticated variable. -/
inductive Phase where
  | Idle        -- no request in flight
  | Received    -- SetVariable() called; payload + auth descriptor staged
  | Verifying   -- checking signer authorization + timestamp freshness
  | Written     -- payload committed to the variable store
  | Refused     -- authorization or anti-replay check failed
  deriving DecidableEq, Repr

open Phase

/-- State of the authenticated-variable monitor. The adversary controls the
    request fields (`reqAuthorized`, `reqTime`, `reqData`) — modelling an
    attacker submitting forged or replayed writes. -/
structure St where
  phase         : Phase
  storedTime    : Nat   -- timestamp of the currently stored value (monotone)
  storedData    : Nat   -- abstract committed payload
  reqPresent    : Bool  -- a request is staged
  reqTime       : Nat   -- timestamp claimed by the staged request
  reqData       : Nat   -- payload of the staged request
  reqAuthorized : Bool  -- signer is in the key hierarchy (trusted oracle)
  deriving Repr

/-- Initial store: idle, nothing staged. `storedTime` may be any starting value
    (monotonicity is proved for all starts). -/
def Init (s : St) : Prop :=
  s.phase = Idle ∧ s.reqPresent = false

/-- One step of authenticated-variable processing. -/
inductive Step : St → St → Prop where
  | idle (s) :
      s.phase = Idle → Step s s
  | recv (s) (t d : Nat) (auth : Bool) :
      s.phase = Idle →
      Step s { s with phase := Received, reqPresent := true,
                      reqTime := t, reqData := d, reqAuthorized := auth }
  | beginVerify (s) :
      s.phase = Received →
      Step s { s with phase := Verifying }
  | write (s) :
      s.phase = Verifying →
      s.reqAuthorized = true →            -- authorized signer
      s.storedTime < s.reqTime →          -- strictly newer timestamp (anti-replay)
      Step s { s with phase := Written, storedTime := s.reqTime,
                      storedData := s.reqData }
  | refuse (s) :
      s.phase = Verifying →
      (s.reqAuthorized = false ∨ s.reqTime ≤ s.storedTime) →
      Step s { s with phase := Refused, reqPresent := false }
  | finishWritten (s) :
      s.phase = Written →
      Step s { s with phase := Idle, reqPresent := false }
  | finishRefused (s) :
      s.phase = Refused →
      Step s { s with phase := Idle, reqPresent := false }

/-! ## Step lemmas (the per-instance obligation proofs) -/

/-- The stored timestamp never decreases: only `write` changes it, requiring a
    strictly newer request time. -/
theorem step_time_mono {s s'} (h : Step s s') : s.storedTime ≤ s'.storedTime := by
  cases h <;> simp_all <;> omega

/-- Entering `Written` from a non-`Written` state requires an authorized signer
    and a strictly newer timestamp. -/
theorem write_guard {s s'} (h : Step s s')
    (hnow : s'.phase = Written) (hprev : s.phase ≠ Written) :
    s.reqAuthorized = true ∧ s.storedTime < s.reqTime := by
  cases h <;> simp_all

end UefiAuthVar


/-! ## Authenticated variables as a StrictMonitor instance -/

namespace UefiAuthVar
open AuthMonotone Phase

/-- The authenticated-variable processor as a strict, authority-guarded monotone
    monitor: `val` is the stored timestamp, `committed` is "phase = Written",
    `authRec` is "request was authorized". -/
def authVarMonitor : StrictMonitor where
  S            := St
  V            := Nat
  Init         := Init
  Step         := Step
  val          := fun s => s.storedTime
  le           := Nat.le
  committed    := fun s => s.phase = Written
  authRec      := fun s => s.reqAuthorized = true
  le_refl      := Nat.le_refl
  le_trans     := Nat.le_trans
  step_mono    := step_time_mono
  init_unc     := by
    intro s h hw; rw [h.1] at hw; exact absurd hw (by decide)
  invAuth_step := by
    intro s s' h hs hw; cases h <;> simp_all
  commit_guard := by
    intro s s' h hnow hprev; exact (write_guard h hnow hprev).1
  lt           := Nat.lt
  lt_irrefl    := Nat.lt_irrefl
  commit_strict := by
    intro s s' h hnow hprev
    have hg := write_guard h hnow hprev
    cases h <;> simp_all

/-- The IsRun of the monitor coincides with the auth-var run relation. -/
def IsRun (σ : Nat → St) : Prop := authVarMonitor.toMonitor.IsRun σ

/-! ## The properties, recovered from the generic theorems -/

/-- **ANTI-REPLAY / anti-rollback (R1,R2).** The stored timestamp is monotone
    non-decreasing along every run: no replay can ever move the variable to an
    older timestamp. -/
theorem authvar_antireplay {σ} (hr : IsRun σ) :
    ∀ i j, i ≤ j → (σ i).storedTime ≤ (σ j).storedTime :=
  authVarMonitor.toMonitor.global_mono hr

/-- **AUTHENTICITY (S).** Whenever a write is committed (`Written`), the request
    was authorized — an unauthorized write is never committed. -/
theorem authvar_authentic {σ} (hr : IsRun σ) (i : Nat)
    (hw : (σ i).phase = Written) : (σ i).reqAuthorized = true :=
  authVarMonitor.toMonitor.auth_at_commit hr i hw

/-- **WRITE-GUARD (G) + STRICT FRESHNESS.** Entering `Written` requires an
    authorized signer and strictly advances the stored timestamp — so a
    replayed (equal-timestamp) write is never committed. -/
theorem authvar_write_guard {σ} (hr : IsRun σ) (i : Nat)
    (hprev : (σ i).phase ≠ Written) (hnext : (σ (i+1)).phase = Written) :
    (σ i).reqAuthorized = true ∧ (σ i).storedTime < (σ (i+1)).storedTime :=
  ⟨authVarMonitor.toMonitor.commit_needs_auth hr i hprev hnext,
   authVarMonitor.commit_strictly_advances hr i hprev hnext⟩

end UefiAuthVar
