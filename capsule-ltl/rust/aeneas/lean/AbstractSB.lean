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
  SecureBootInstance.lean — UEFI Secure Boot policy (db/dbx) as INSTANCE #3 of
  AuthMonotone.

  Secure Boot's forbidden-signature database `dbx` is itself an authenticated
  variable updated by KEK-signed writes (UEFI spec §32.x / §8.2). The
  security-relevant monotone quantity is the SET of revoked image hashes: a
  revocation, once installed, must never silently disappear. So the observable
  `val` is the dbx set ordered by SUBSET (⊆), not a number.

  THE INSTRUCTIVE DIFFERENCE (the unifying thread's payoff): unlike capsule
  versions and variable timestamps, dbx growth is APPEND-ONLY — a policy update
  adds revocations, so the order is ≤ (superset), and re-applying the same dbx
  is allowed (equality). Hence Secure Boot is a `Monitor` but NOT a
  `StrictMonitor`: there is no "strictly advances" guarantee, and there should
  not be. The framework expresses this distinction precisely: instances #1/#2
  extend StrictMonitor; instance #3 does not. Same core theorems (R1/R2 = "dbx
  never shrinks", S = "policy change was authorized", G), minus strictness.

  Self-contained, Mathlib-free, Lean 4.16.
-/

namespace UefiSecureBoot

inductive Phase where
  | Idle
  | Received     -- a signed dbx-update request is staged
  | Verifying    -- checking KEK authorization
  | Updated      -- dbx extended with the new revocations
  | Refused      -- authorization failed
  deriving DecidableEq, Repr

open Phase

/-- State of the Secure Boot policy monitor. `dbx` is the list of revoked image
    hashes (a set, used up to membership). The adversary controls the request
    (`reqRevs`, `reqAuthorized`). -/
structure St where
  phase         : Phase
  dbx           : List Nat   -- revoked image hashes (the monotone set)
  reqPresent    : Bool
  reqRevs       : List Nat   -- revocations the staged request would add
  reqAuthorized : Bool       -- request is KEK-signed (trusted oracle)
  deriving Repr

/-- Subset order on revocation sets: every revoked hash in `a` is in `b`. -/
def Sub (a b : List Nat) : Prop := ∀ x, x ∈ a → x ∈ b

theorem Sub.refl (a : List Nat) : Sub a a := fun _ h => h
theorem Sub.trans {a b c} (hab : Sub a b) (hbc : Sub b c) : Sub a c :=
  fun x h => hbc x (hab x h)

/-- Appending revocations only grows the set. -/
theorem sub_append (a r : List Nat) : Sub a (a ++ r) := by
  intro x h; exact List.mem_append.mpr (Or.inl h)

def Init (s : St) : Prop :=
  s.phase = Idle ∧ s.reqPresent = false

/-- One step of Secure Boot dbx update. `update` APPENDS the requested
    revocations (append-only policy), guarded by KEK authorization. There is no
    path that removes from dbx without authorization — that is the whole point. -/
inductive Step : St → St → Prop where
  | idle (s) :
      s.phase = Idle → Step s s
  | recv (s) (revs : List Nat) (auth : Bool) :
      s.phase = Idle →
      Step s { s with phase := Received, reqPresent := true,
                      reqRevs := revs, reqAuthorized := auth }
  | beginVerify (s) :
      s.phase = Received →
      Step s { s with phase := Verifying }
  | update (s) :
      s.phase = Verifying →
      s.reqAuthorized = true →                       -- KEK-authorized
      Step s { s with phase := Updated, dbx := s.dbx ++ s.reqRevs }
  | refuse (s) :
      s.phase = Verifying →
      s.reqAuthorized = false →
      Step s { s with phase := Refused, reqPresent := false }
  | finishUpdated (s) :
      s.phase = Updated →
      Step s { s with phase := Idle, reqPresent := false }
  | finishRefused (s) :
      s.phase = Refused →
      Step s { s with phase := Idle, reqPresent := false }

/-! ## Step lemmas -/

/-- dbx never shrinks: the only dbx-changing rule is `update`, which appends. -/
theorem step_dbx_mono {s s'} (h : Step s s') : Sub s.dbx s'.dbx := by
  cases h with
  | update hp _ => exact sub_append _ _
  | _ => exact (by intro x hx; simp_all [Sub])

/-- Entering `Updated` from a non-`Updated` state requires KEK authorization. -/
theorem update_guard {s s'} (h : Step s s')
    (hnow : s'.phase = Updated) (hprev : s.phase ≠ Updated) :
    s.reqAuthorized = true := by
  cases h <;> simp_all

end UefiSecureBoot


/-! ## Secure Boot as a (core, non-strict) Monitor instance -/

namespace UefiSecureBoot
open AuthMonotone Phase

/-- The Secure Boot policy store as a monotone, authority-guarded monitor.
    `val` is the dbx set, ordered by `Sub` (⊆); `committed` is "phase = Updated";
    `authRec` is "request KEK-authorized". NOTE: this is a `Monitor`, not a
    `StrictMonitor` — append-only growth is non-strict. -/
--LISTING:sbmonitor:begin
def secureBootMonitor : Monitor where
  S            := St
  V            := List Nat
  Init         := Init
  Step         := Step
  val          := fun s => s.dbx
  le           := Sub
  committed    := fun s => s.phase = Updated
  authRec      := fun s => s.reqAuthorized = true
  le_refl      := Sub.refl
  le_trans     := Sub.trans
  step_mono    := step_dbx_mono
  init_unc     := by
    intro s h hu; rw [h.1] at hu; exact absurd hu (by decide)
  invAuth_step := by
    intro s s' h hs hu; cases h <;> simp_all
  commit_guard := by
    intro s s' h hnow hprev; exact update_guard h hnow hprev
--LISTING:sbmonitor:end

def IsRun (σ : Nat → St) : Prop := secureBootMonitor.IsRun σ

/-! ## Properties, recovered from the generic theorems -/

/-- **NO SILENT UN-REVOCATION (R1,R2).** dbx is subset-monotone along every
    run: a revoked hash, once in dbx, remains in dbx forever. No sequence of
    operations can shrink the forbidden-signature database. -/
theorem sb_dbx_monotone {σ} (hr : IsRun σ) :
    ∀ i j, i ≤ j → Sub (σ i).dbx (σ j).dbx :=
  secureBootMonitor.global_mono hr

/-- Concretely: any hash revoked at position `i` is still revoked at any later
    position `j`. -/
theorem sb_revocation_persists {σ} (hr : IsRun σ) {i j : Nat} (hij : i ≤ j)
    {h : Nat} (hrev : h ∈ (σ i).dbx) : h ∈ (σ j).dbx :=
  sb_dbx_monotone hr i j hij h hrev

/-- **AUTHENTICITY (S).** Whenever a policy update is committed (`Updated`), the
    request was KEK-authorized — an unauthorized actor never changes dbx. -/
theorem sb_authentic {σ} (hr : IsRun σ) (i : Nat)
    (hu : (σ i).phase = Updated) : (σ i).reqAuthorized = true :=
  secureBootMonitor.auth_at_commit hr i hu

/-- **UPDATE-GUARD (G).** Entering `Updated` requires a KEK-authorized request. -/
theorem sb_update_guard {σ} (hr : IsRun σ) (i : Nat)
    (hprev : (σ i).phase ≠ Updated) (hnext : (σ (i+1)).phase = Updated) :
    (σ i).reqAuthorized = true :=
  secureBootMonitor.commit_needs_auth hr i hprev hnext

end UefiSecureBoot
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
