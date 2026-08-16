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
