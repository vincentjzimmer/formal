/-
  LTL properties of the UEFI capsule update process.

  A self-contained Lean 4 development (no Mathlib).

  We model the UEFI Capsule Update flow as a labelled transition system:

      Idle ──UpdateCapsule()──▶ CapsuleStaged ──reset──▶ PostReset
        ▲                                                    │
        │                                              beginAuthenticate
        │                                                    ▼
        ├────────────── finish ──── Applied ◀── apply ── Authenticating
        │                                          │            │
        └────────────── finish ─── Rejected ◀──────┴── reject ──┘

  - UpdateCapsule() (a UEFI Runtime Service) stages a capsule image in a
    reserved memory region together with a requested system reset
    (EFI_OS_INDICATIONS_FILE_CAPSULE_DELIVERY_SUPPORTED semantics).
  - After the reset the firmware (capsule coalescing + the Firmware Management
    Protocol / FMP) authenticates the image: a signature check *and* a
    monotonic version check (anti-rollback, per EDK II `FmpDeviceCheckImage`
    / lowest-supported-version handling).
  - apply is only enabled for an authentic image whose version is at or above
    the stored lowest-supported-version (LSV) floor; otherwise the capsule is
    rejected. Applying writes the image and bumps the LSV floor.

  We then prove, by machine-checked LTL theorems quantified over *all* runs:
    1. SAFETY (authenticity):  G (Applied → signature was valid)
    2. ANTI-ROLLBACK:          G (lsv floor non-decreasing), its global
                               monotonicity corollary  i ≤ j → lsv i ≤ lsv j,
                               and the floor invariant  G (lsv ≤ fwVersion)
    3. APPLY-GUARD:            you only *enter* Applied via an authentic image
                               at or above the LSV floor (no sub-floor image is
                               ever applied)
    4. RESET-FIRST:            G (Applied → a reset has occurred)
    5. RESPONSIVENESS (live):  G (good capsule staged → F Applied)
                               — fairness-free, because the good path is forced.
-/

namespace UefiCapsuleLTL

/-! ## System model -/

inductive Phase where
  | Idle           -- normal runtime; no update pending
  | CapsuleStaged  -- UpdateCapsule() called; image in memory; reset requested
  | PostReset      -- machine has reset; capsule awaiting authentication
  | Authenticating -- FMP authenticating signature + version
  | Applied        -- image authenticated and written
  | Rejected       -- authentication or anti-rollback check failed
  deriving DecidableEq, Repr

open Phase

structure St where
  phase           : Phase
  fwVersion       : Nat   -- currently running firmware version
  lsv             : Nat   -- lowest supported version stored in NV RAM
  capsulePresent  : Bool  -- a capsule image is staged
  capsuleVersion  : Nat   -- version of the staged image
  imageDigest     : Nat   -- digest of the staged image (authenticated input)
  capsuleSigValid : Bool  -- staged image carries a valid signature
  resetOccurred   : Bool  -- a reset has happened since staging
  deriving Repr

/-- Abstract certificate/signature verifier applied to the staged image digest.
    `capsuleSigValid` is *computed* from this during authentication rather than
    chosen at staging; the proofs are independent of its definition. -/
opaque certOK : Nat → Bool := fun _ => true

/-- Initial firmware state: idle, nothing staged. The LSV floor starts at or
    below the running firmware version (an invariant maintained by `apply`). -/
def Init (s : St) : Prop :=
  s.phase = Idle ∧ s.capsulePresent = false ∧ s.resetOccurred = false
    ∧ s.lsv ≤ s.fwVersion

/-- One step of the capsule-update transition system. -/
inductive Step : St → St → Prop where
  | stutterIdle (s) :
      s.phase = Idle →
      Step s s
  | stage (s) (v : Nat) (digest : Nat) :
      s.phase = Idle →
      Step s { s with phase := CapsuleStaged, capsulePresent := true,
                      capsuleVersion := v, imageDigest := digest,
                      resetOccurred := false }
  | reset (s) :
      s.phase = CapsuleStaged →
      Step s { s with phase := PostReset, resetOccurred := true }
  | beginAuth (s) :
      s.phase = PostReset →
      Step s { s with phase := Authenticating,
                      capsuleSigValid := certOK s.imageDigest }
  | apply (s) :
      s.phase = Authenticating →
      s.capsuleSigValid = true →              -- signature valid
      s.lsv ≤ s.capsuleVersion →              -- at or above the LSV floor
      Step s { s with phase := Applied, fwVersion := s.capsuleVersion,
                      lsv := s.capsuleVersion }
  | reject (s) :
      s.phase = Authenticating →
      (s.capsuleSigValid = false ∨ s.capsuleVersion < s.lsv) →
      Step s { s with phase := Rejected, capsulePresent := false }
  | finishApplied (s) :
      s.phase = Applied →
      Step s { s with phase := Idle, capsulePresent := false, resetOccurred := false }
  | finishRejected (s) :
      s.phase = Rejected →
      Step s { s with phase := Idle, capsulePresent := false, resetOccurred := false }

/-- An (ω-)run: an infinite trace beginning at an initial state and
    closed under the transition relation. -/
def IsRun (σ : Nat → St) : Prop :=
  Init (σ 0) ∧ ∀ i, Step (σ i) (σ (i + 1))


/-! ## Shallow-embedded LTL

    A temporal proposition is a predicate on a trace and a position. -/

--LISTING:ltl:begin
abbrev TProp := (Nat → St) → Nat → Prop

/-- Lift a state predicate to "holds now". -/
def now (p : St → Prop) : TProp := fun σ i => p (σ i)

/-- G φ : φ holds at every position from here on. -/
def G (P : TProp) : TProp := fun σ i => ∀ j, i ≤ j → P σ j

/-- F φ : φ holds at some position from here on. -/
def F (P : TProp) : TProp := fun σ i => ∃ j, i ≤ j ∧ P σ j

/-- X φ : φ holds at the next position. -/
def X (P : TProp) : TProp := fun σ i => P σ (i + 1)

def Imp (P Q : TProp) : TProp := fun σ i => P σ i → Q σ i
def And (P Q : TProp) : TProp := fun σ i => P σ i ∧ Q σ i

/-- A temporal property is *valid* if it holds at position 0 of every run. -/
def Sat (φ : TProp) : Prop := ∀ σ, IsRun σ → φ σ 0
--LISTING:ltl:end

/-- Convenience state predicates. -/
def appliedNow  : TProp := now (fun s => s.phase = Applied)
def sigValidNow : TProp := now (fun s => s.capsuleSigValid = true)
def resetNow    : TProp := now (fun s => s.resetOccurred = true)


/-! ## Transition-level lemmas -/

/-- Every transition leaves the LSV floor non-decreasing: the only floor-changing
    rule is `apply`, which requires `lsv ≤ capsuleVersion` and sets the floor to
    `capsuleVersion`. (The running `fwVersion` is *not* monotone: a downgrade to
    any version at or above the floor is permitted.) -/
theorem step_lsv_mono {s s'} (h : Step s s') :
    s.lsv ≤ s'.lsv := by
  cases h <;> simp_all <;> omega

/-- The stored lowest-supported-version floor never decreases across a step. -/
theorem lsv_monotone {s s'} (h : Step s s') :
    s.lsv ≤ s'.lsv :=
  step_lsv_mono h

/-- APPLY-GUARD: one only *enters* `Applied` (from a non-`Applied` state) via
    an authentic image at or above the LSV floor. No sub-floor image is applied. -/
theorem apply_guard {s s'} (h : Step s s')
    (hnow : s'.phase = Applied) (hprev : s.phase ≠ Applied) :
    s.capsuleSigValid = true ∧ s.lsv ≤ s.capsuleVersion := by
  cases h <;> simp_all

/-- From a `CapsuleStaged` state the only enabled transition is `reset`; it
    advances to `PostReset` and preserves the image fields (including the digest
    and the floor). -/
theorem reset_forced {s s'} (hp : s.phase = CapsuleStaged) (h : Step s s') :
    s'.phase = PostReset
      ∧ s'.fwVersion = s.fwVersion
      ∧ s'.capsuleVersion = s.capsuleVersion
      ∧ s'.lsv = s.lsv
      ∧ s'.imageDigest = s.imageDigest := by
  cases h <;> simp_all

/-- From a `PostReset` state the only enabled transition is `beginAuth`; it
    advances to `Authenticating`, preserves the version fields, and *computes*
    the signature verdict from the stored digest (`capsuleSigValid = certOK d`). -/
theorem auth_forced {s s'} (hp : s.phase = PostReset) (h : Step s s') :
    s'.phase = Authenticating
      ∧ s'.fwVersion = s.fwVersion
      ∧ s'.capsuleVersion = s.capsuleVersion
      ∧ s'.lsv = s.lsv
      ∧ s'.capsuleSigValid = certOK s.imageDigest := by
  cases h <;> simp_all

/-- From an authentic `Authenticating` state at or above the floor the `reject`
    guard is false, so the only enabled transition is `apply`: the next state is
    `Applied`. This is what makes the good path *forced* (no fairness needed). -/
theorem good_apply_forced {s s'}
    (hp : s.phase = Authenticating)
    (hsig : s.capsuleSigValid = true)
    (hfloor : s.lsv ≤ s.capsuleVersion)
    (h : Step s s') :
    s'.phase = Applied := by
  cases h <;> simp_all <;> omega


/-! ## Inductive invariants -/

/-- SAFETY invariant: if `Applied`, the staged image's signature was valid. -/
def InvSig (s : St) : Prop := s.phase = Applied → s.capsuleSigValid = true

theorem invSig_init {s} (h : Init s) : InvSig s := by
  intro hap; rw [h.1] at hap; exact absurd hap (by decide)

theorem invSig_step {s s'} (h : Step s s') (_hs : InvSig s) : InvSig s' := by
  intro hap; cases h <;> simp_all

theorem invSig_run {σ} (hr : IsRun σ) : ∀ i, InvSig (σ i) := by
  intro i
  induction i with
  | zero      => exact invSig_init hr.1
  | succ n ih => exact invSig_step (hr.2 n) ih

/-- RESET-FIRST invariant: every phase reachable only after a reset records it.
    (Strengthened across PostReset/Authenticating/Applied to be inductive.) -/
def InvReset (s : St) : Prop :=
  (s.phase = PostReset ∨ s.phase = Authenticating ∨ s.phase = Applied) →
    s.resetOccurred = true

theorem invReset_init {s} (h : Init s) : InvReset s := by
  intro hmem; rw [h.1] at hmem
  rcases hmem with h | h | h <;> exact absurd h (by decide)

--LISTING:inv:begin
theorem invReset_step {s s'} (h : Step s s') (hs : InvReset s) : InvReset s' := by
  intro hmem
  cases h with
  | beginAuth hp => exact hs (Or.inl hp)
  | apply hp _ _ => exact hs (Or.inr (Or.inl hp))
  | _ => simp_all
--LISTING:inv:end

theorem invReset_run {σ} (hr : IsRun σ) : ∀ i, InvReset (σ i) := by
  intro i
  induction i with
  | zero      => exact invReset_init hr.1
  | succ n ih => exact invReset_step (hr.2 n) ih

/-- FLOOR invariant: the LSV floor never exceeds the running firmware version.
    `Init` establishes `lsv ≤ fwVersion`; `apply` sets both fields to
    `capsuleVersion` (restoring equality), and every other rule leaves them
    fixed — so the invariant is inductive. -/
def InvFloor (s : St) : Prop := s.lsv ≤ s.fwVersion

theorem invFloor_init {s} (h : Init s) : InvFloor s := h.2.2.2

theorem invFloor_step {s s'} (h : Step s s') (hs : InvFloor s) : InvFloor s' := by
  unfold InvFloor at *
  cases h <;> simp_all <;> omega

theorem invFloor_run {σ} (hr : IsRun σ) : ∀ i, InvFloor (σ i) := by
  intro i
  induction i with
  | zero      => exact invFloor_init hr.1
  | succ n ih => exact invFloor_step (hr.2 n) ih


/-! ## The LTL theorems (quantified over all runs) -/

/-- **1. SAFETY (authenticity).**
    `⊨ G (Applied → signature valid)`.
    The firmware never reports a capsule as applied unless its signature was
    valid — an unauthenticated image is never applied. -/
theorem safety_authentic : Sat (G (Imp appliedNow sigValidNow)) := by
  intro σ hr j _ hap
  exact invSig_run hr j hap

/-- **2a. ANTI-ROLLBACK (step monotonicity of the LSV floor).**
    `⊨ G (lsv ≤ X lsv)`.
    The lowest-supported-version floor never decreases across a step. (This is
    the correct anti-rollback invariant: EDK II checks the staged version against
    the stored LSV floor, not against the running firmware version, and the
    running `fwVersion` may legitimately decrease to any value at/above it.) -/
theorem antirollback_lsv :
    Sat (G (fun σ i => (σ i).lsv ≤ (σ (i + 1)).lsv)) := by
  intro σ hr j _
  exact step_lsv_mono (hr.2 j)

/-- **2b. ANTI-ROLLBACK (global monotonicity of the LSV floor).**
    For any two positions `i ≤ j`, `lsv i ≤ lsv j`.
    No sequence of capsule updates can ever roll the floor backwards. -/
theorem antirollback_lsv_global {σ} (hr : IsRun σ) :
    ∀ i j, i ≤ j → (σ i).lsv ≤ (σ j).lsv := by
  intro i j h
  induction h with
  | refl       => exact Nat.le_refl _
  | step _ ih  => exact Nat.le_trans ih (step_lsv_mono (hr.2 _))

/-- **2c. FLOOR INVARIANT.**
    `⊨ G (lsv ≤ fwVersion)`.
    The LSV floor never exceeds the running firmware version; together with 2a/2b
    this is what the old (unsound) `fwVersion`-monotonicity claim is replaced by
    under the corrected, LSV-checking model. -/
theorem lsv_floor_maintained :
    Sat (G (fun σ i => (σ i).lsv ≤ (σ i).fwVersion)) := by
  intro σ hr j _
  exact invFloor_run hr j

/-- **3. APPLY-GUARD.**
    `⊨ G ((¬Applied ∧ X Applied) → (authentic ∧ at-or-above-floor)_now)`.
    Whenever a run *enters* `Applied`, the state it came from carried a valid
    signature and a version at or above the LSV floor — a sub-floor or forged
    image is never applied. (The guard is stated on the pre-state; `apply` bumps
    `fwVersion := lsv := capsuleVersion`.) -/
theorem apply_guarded :
    Sat (G (Imp (fun σ i => (σ i).phase ≠ Applied ∧ (σ (i+1)).phase = Applied)
                (fun σ i => (σ i).capsuleSigValid = true
                            ∧ (σ i).lsv ≤ (σ i).capsuleVersion))) := by
  intro σ hr j _ hpre
  exact apply_guard (hr.2 j) hpre.2 hpre.1

/-- **4. RESET-FIRST.**
    `⊨ G (Applied → reset occurred)`.
    A capsule is only ever applied after the system has actually reset
    (capsule coalescing runs in the post-reset boot, not in the runtime call). -/
theorem reset_first : Sat (G (Imp appliedNow resetNow)) := by
  intro σ hr j _ hap
  exact invReset_run hr j (Or.inr (Or.inr hap))

/-- **5. RESPONSIVENESS (liveness, fairness-free).**
    `⊨ G ((staged ∧ digest authenticates ∧ at-or-above-floor) → F Applied)`.
    Once a capsule whose digest passes `certOK` and whose version is at or above
    the LSV floor is staged, every run reaches `Applied`. No fairness hypothesis
    is required: from the good staged state the enabled transitions are forced
    (reset → beginAuth → apply), so `Applied` is reached within three steps.
    (Holds only in this interruption-free model; power failure falsifies it.) -/
def goodStaged : TProp := fun σ i =>
  (σ i).phase = CapsuleStaged
    ∧ certOK ((σ i).imageDigest) = true
    ∧ (σ i).lsv ≤ (σ i).capsuleVersion

--LISTING:live:begin
theorem responsiveness : Sat (G (Imp goodStaged (F appliedNow))) := by
  intro σ hr j _ hgood
  obtain ⟨hStaged, hSig, hFloor⟩ := hgood
  -- step 1: reset  (CapsuleStaged → PostReset), version/digest fields preserved
  obtain ⟨h1p, h1fw, h1ver, h1lsv, h1digest⟩ := reset_forced hStaged (hr.2 j)
  -- step 2: beginAuth (PostReset → Authenticating), sig computed from digest
  obtain ⟨h2p, h2fw, h2ver, h2lsv, h2sig⟩ := auth_forced h1p (hr.2 (j + 1))
  -- step 3: apply forced (authentic + at-or-above-floor ⇒ Applied)
  have h3 : (σ (j + 3)).phase = Applied := by
    apply good_apply_forced h2p
    · rw [h2sig, h1digest]; exact hSig
    · rw [h2lsv, h1lsv, h2ver, h1ver]; exact hFloor
    · exact hr.2 (j + 2)
  exact ⟨j + 3, by omega, h3⟩
--LISTING:live:end

end UefiCapsuleLTL
