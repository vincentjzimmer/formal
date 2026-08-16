/-
  AuthMonotone.lean — a parameterized verified reference monitor for UEFI's
  authority-signed, monotonically-guarded write surfaces.

  This is the unifying core extracted from the capsule-update development. It
  captures, ONCE, the pattern shared by:
    * capsule update      (monotone firmware version, signature authority)
    * authenticated vars  (monotone timestamp, key-hierarchy authority)
    * Secure Boot db/dbx  (append-only policy set, KEK authority)

  A `Monitor` bundles a transition system with a monotone observable `val` in an
  order `le`, a `committed` ("applied") predicate, and an `authRec`
  ("authority was recorded in the state") predicate, together with the four
  obligations an instance must discharge. From those we prove GENERICALLY:

    global_mono     (R2): val is non-decreasing along every run (anti-rollback)
    auth_at_commit  (S) : a committed state always has authority recorded
    commit_needs_auth(G): entering committed requires authority at the pre-state

  A `StrictMonitor` adds the strict-increase guard (capsule, auth-vars); from it
  we prove `commit_strictly_advances`: entering committed strictly raises `val`.
  Secure Boot satisfies only the core (append-only is ≤, not <), which is itself
  a finding, not a defect — see SecureBoot.lean.

  Mathlib-free; same axiom discipline as the capsule development.
-/

namespace AuthMonotone

/-- A monotone, authority-guarded reference monitor. The order laws and the four
    step/init obligations are fields, so a generic proof can rely on them and
    each instance discharges them concretely. -/
--LISTING:monitor:begin
structure Monitor where
  S            : Type
  V            : Type
  Init         : S → Prop
  Step         : S → S → Prop
  /-- The monotone observable (version / timestamp / policy set). -/
  val          : S → V
  /-- The order `val` is monotone in. -/
  le           : V → V → Prop
  /-- The "applied / committed" predicate. -/
  committed    : S → Prop
  /-- "Authority was recorded": the state carries a valid-authority witness
      (e.g. signature checked, signer in the key hierarchy). -/
  authRec      : S → Prop
  -- order laws (kept as fields to stay Mathlib-free)
  le_refl      : ∀ v, le v v
  le_trans     : ∀ {a b c}, le a b → le b c → le a c
  -- per-instance obligations:
  /-- R1: every step is non-decreasing in `val`. -/
  step_mono    : ∀ {s s'}, Step s s' → le (val s) (val s')
  /-- Initial states are not committed (so the authenticity invariant is base). -/
  init_unc     : ∀ {s}, Init s → ¬ committed s
  /-- The authenticity invariant `committed → authRec` is preserved by steps. -/
  invAuth_step : ∀ {s s'}, Step s s' → (committed s → authRec s) →
                   (committed s' → authRec s')
  /-- G: entering `committed` from a non-committed state requires authority. -/
  commit_guard : ∀ {s s'}, Step s s' → committed s' → ¬ committed s → authRec s
--LISTING:monitor:end

namespace Monitor

variable (M : Monitor)

/-- A run of the monitor: initial, and closed under `Step`. -/
def IsRun (σ : Nat → M.S) : Prop :=
  M.Init (σ 0) ∧ ∀ i, M.Step (σ i) (σ (i + 1))

/-- The authenticity invariant as a state predicate. -/
def InvAuth (s : M.S) : Prop := M.committed s → M.authRec s

theorem invAuth_init {s} (h : M.Init s) : M.InvAuth s :=
  fun hc => absurd hc (M.init_unc h)

theorem invAuth_run {σ} (hr : M.IsRun σ) : ∀ i, M.InvAuth (σ i) := by
  intro i
  induction i with
  | zero      => exact M.invAuth_init hr.1
  | succ n ih => exact M.invAuth_step (hr.2 n) ih

/-- **S (authenticity).** Every committed state on every run has authority
    recorded: an unauthenticated payload is never committed. -/
theorem auth_at_commit {σ} (hr : M.IsRun σ) (i : Nat) (hc : M.committed (σ i)) :
    M.authRec (σ i) :=
  M.invAuth_run hr i hc

/-- **R1 (per-step anti-rollback).** -/
theorem step_le {σ} (hr : M.IsRun σ) (i : Nat) :
    M.le (M.val (σ i)) (M.val (σ (i + 1))) :=
  M.step_mono (hr.2 i)

/-- **R2 (global anti-rollback).** `val` is non-decreasing between any two
    positions: no run can ever roll the observable backward. -/
--LISTING:globalmono:begin
theorem global_mono {σ} (hr : M.IsRun σ) :
    ∀ i j, i ≤ j → M.le (M.val (σ i)) (M.val (σ j)) := by
  intro i j h
  induction h with
  | refl       => exact M.le_refl _
  | step _ ih  => exact M.le_trans ih (M.step_mono (hr.2 _))
--LISTING:globalmono:end

/-- **G (apply-guard).** Whenever a run *enters* `committed`, the pre-state
    carried authority. -/
theorem commit_needs_auth {σ} (hr : M.IsRun σ) (i : Nat)
    (hprev : ¬ M.committed (σ i)) (hnext : M.committed (σ (i + 1))) :
    M.authRec (σ i) :=
  M.commit_guard (hr.2 i) hnext hprev

end Monitor

/-- A monitor whose commit additionally *strictly* advances the observable —
    the strong anti-rollback guard of capsule update and authenticated
    variables (a strictly-newer version / timestamp). Secure Boot's append-only
    policy store does NOT extend this (equal-or-superset), and the distinction
    is itself a result. -/
structure StrictMonitor extends Monitor where
  lt            : V → V → Prop
  lt_irrefl     : ∀ v, ¬ lt v v
  /-- The strict guard: entering `committed` strictly raises `val`. -/
  commit_strict : ∀ {s s'}, Step s s' → committed s' → ¬ committed s →
                    lt (val s) (val s')

namespace StrictMonitor

variable (M : StrictMonitor)

/-- **Strict anti-rollback at commit.** Entering the committed state strictly
    advances the observable; in particular the pre-state value is not the
    committed one, so a replay (equal version/timestamp) is never committed. -/
theorem commit_strictly_advances {σ} (hr : M.toMonitor.IsRun σ) (i : Nat)
    (hprev : ¬ M.committed (σ i)) (hnext : M.committed (σ (i + 1))) :
    M.lt (M.val (σ i)) (M.val (σ (i + 1))) :=
  M.commit_strict (hr.2 i) hnext hprev

end StrictMonitor

end AuthMonotone
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
