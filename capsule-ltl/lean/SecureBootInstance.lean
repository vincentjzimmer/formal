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

import AuthMonotone

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
